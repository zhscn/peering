/*
 * Vermilion simplified peer metadata.
 *
 * Under append-only + single-writer constraints, peering no longer needs
 * Ceph's full PGLog machinery, but it still needs two semantic layers:
 *
 *   - a PG-scoped committed journal prefix for IO ordering
 *   - an objectwise image for recovery planning
 *
 * This replaces the parts of Ceph's pg_info_t, pg_log_t, pg_missing_t, and
 * eversion_t that are relevant to the extracted peering state machine.
 */

#pragma once

#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace vermilion::peering {

// ── Basic type aliases ─────────────────────────────────────────────

using epoch_t = uint32_t;
using osd_id_t = int32_t;
using pg_id_t = uint64_t;
using object_id_t = uint64_t;
using journal_seq_t = uint64_t;

// Legacy scalar-compatibility object id used only to translate older
// committed_length-only inputs into an object image. It is not a semantic
// "primary object" and must not drive primary selection.
inline constexpr object_id_t primary_object_id = 0;

// ── Objectwise image summaries ────────────────────────────────────

using ObjectImage = std::map<object_id_t, uint64_t>;

struct ObjectAuthority {
  osd_id_t authority_osd = -1;
  uint64_t authority_length = 0;

  bool operator==(const ObjectAuthority &) const = default;
};

using AuthorityImage = std::map<object_id_t, ObjectAuthority>;

struct ObjRecovery {
  object_id_t obj = 0;
  osd_id_t source = -1;
  uint64_t from_length = 0;
  uint64_t to_length = 0;

  bool operator==(const ObjRecovery &) const = default;
};

struct PeerRecoveryPlan {
  osd_id_t target = -1;
  journal_seq_t peer_committed_seq = 0;
  journal_seq_t authoritative_seq = 0;
  std::vector<ObjRecovery> recoveries;

  bool operator==(const PeerRecoveryPlan &) const = default;
};

// ── PeerInfo ───────────────────────────────────────────────────────

// Simplified peer metadata. In Ceph this is pg_info_t + pg_log_t +
// pg_missing_t — hundreds of fields. Under append-only semantics,
// the peering-relevant state is:
//   - how far the peer's committed journal prefix extends
//   - what committed object image it has materialized
struct PeerInfo {
  osd_id_t osd = -1;
  journal_seq_t committed_seq = 0;

  // Legacy scalar compatibility for older image-only reducers and replay.
  // This is not the ordering source of truth once committed_seq is present.
  uint64_t committed_length = 0;
  ObjectImage image;

  // Last epoch this peer participated in a completed peering.
  epoch_t last_epoch_started = 0;

  // Last epoch this peer's interval started.
  epoch_t last_interval_started = 0;

  bool is_empty() const {
    return image.empty() ? committed_length == 0 : image.empty();
  }
};

// ── PGInfo ─────────────────────────────────────────────────────────

// Aggregate PG state on this OSD. Replaces pg_info_t.
struct PGInfo {
  pg_id_t pgid = 0;
  journal_seq_t committed_seq = 0;

  // Legacy scalar compatibility for older image-only reducers and replay.
  uint64_t committed_length = 0;
  ObjectImage image;

  // Peering history (subset of pg_history_t).
  epoch_t last_epoch_started = 0;
  epoch_t last_interval_started = 0;
  epoch_t last_epoch_clean = 0;

  // Creation metadata.
  epoch_t epoch_created = 0;

  // Acting/up set tracking (from OSDMap).
  epoch_t same_interval_since = 0;
  epoch_t same_up_since = 0;
  epoch_t same_primary_since = 0;
};

inline uint64_t lookup_length(const ObjectImage &image, object_id_t obj) {
  auto it = image.find(obj);
  return it == image.end() ? 0 : it->second;
}

inline ObjectImage singleton_image(object_id_t obj, uint64_t length) {
  ObjectImage image;
  if (length > 0) {
    image[obj] = length;
  }
  return image;
}

inline ObjectImage primary_image(uint64_t length) {
  return singleton_image(primary_object_id, length);
}

inline uint64_t primary_length(const ObjectImage &image) {
  return lookup_length(image, primary_object_id);
}

inline ObjectImage effective_image(const PeerInfo &info) {
  if (!info.image.empty() || info.committed_length == 0) {
    return info.image;
  }
  return primary_image(info.committed_length);
}

inline ObjectImage effective_image(const PGInfo &info) {
  if (!info.image.empty() || info.committed_length == 0) {
    return info.image;
  }
  return primary_image(info.committed_length);
}

inline PeerInfo normalized_peer_info(PeerInfo info) {
  info.image = effective_image(info);
  info.committed_length = primary_length(info.image);
  return info;
}

inline PGInfo normalized_pg_info(PGInfo info) {
  info.image = effective_image(info);
  info.committed_length = primary_length(info.image);
  return info;
}

inline ObjectImage join_image(const ObjectImage &lhs, const ObjectImage &rhs) {
  ObjectImage joined = lhs;
  for (const auto &[obj, len] : rhs) {
    auto it = joined.find(obj);
    if (it == joined.end() || it->second < len) {
      joined[obj] = len;
    }
  }
  return joined;
}

inline ObjectImage join_images(const std::vector<ObjectImage> &images) {
  ObjectImage joined;
  for (const auto &image : images) {
    joined = join_image(joined, image);
  }
  return joined;
}

inline ObjectImage clamp_image_to(const ObjectImage &auth,
                                  const ObjectImage &image) {
  ObjectImage clamped;
  for (const auto &[obj, len] : image) {
    auto auth_len = lookup_length(auth, obj);
    if (auth_len > 0) {
      auto bounded = len < auth_len ? len : auth_len;
      if (bounded > 0) {
        clamped[obj] = bounded;
      }
    }
  }
  return clamped;
}

inline bool prefix_image(const ObjectImage &lhs, const ObjectImage &rhs) {
  for (const auto &[obj, len] : lhs) {
    if (len > lookup_length(rhs, obj)) {
      return false;
    }
  }
  return true;
}

inline bool same_image(const ObjectImage &lhs, const ObjectImage &rhs) {
  return prefix_image(lhs, rhs) && prefix_image(rhs, lhs);
}

inline std::vector<ObjRecovery> image_recovery_gaps(const ObjectImage &local,
                                                    const AuthorityImage &auth) {
  std::vector<ObjRecovery> gaps;
  for (const auto &[obj, source] : auth) {
    auto auth_len = source.authority_length;
    auto local_len = lookup_length(local, obj);
    if (local_len < auth_len) {
      gaps.push_back(ObjRecovery{
          .obj = obj,
          .source = source.authority_osd,
          .from_length = local_len,
          .to_length = auth_len,
      });
    }
  }
  return gaps;
}

inline ObjectImage authoritative_image(const std::vector<PeerInfo> &infos) {
  std::vector<ObjectImage> images;
  images.reserve(infos.size());
  for (const auto &info : infos) {
    images.push_back(effective_image(info));
  }
  return join_images(images);
}

inline AuthorityImage
authoritative_sources(const std::vector<PeerInfo> &infos) {
  AuthorityImage auth;
  for (const auto &raw : infos) {
    auto info = normalized_peer_info(raw);
    for (const auto &[obj, len] : info.image) {
      auto it = auth.find(obj);
      if (it == auth.end() || it->second.authority_length < len) {
        auth[obj] = ObjectAuthority{
            .authority_osd = info.osd,
            .authority_length = len,
        };
      }
    }
  }
  return auth;
}

inline AuthorityImage authority_from_image(osd_id_t source,
                                           const ObjectImage &image) {
  AuthorityImage auth;
  for (const auto &[obj, len] : image) {
    if (len > 0) {
      auth[obj] = ObjectAuthority{
          .authority_osd = source,
          .authority_length = len,
      };
    }
  }
  return auth;
}

inline AuthorityImage authority_from_peer_info(const PeerInfo &raw) {
  auto info = normalized_peer_info(raw);
  return authority_from_image(info.osd, info.image);
}

inline ObjectImage authority_image_values(const AuthorityImage &auth) {
  ObjectImage image;
  for (const auto &[obj, item] : auth) {
    if (item.authority_length > 0) {
      image[obj] = item.authority_length;
    }
  }
  return image;
}

inline std::vector<ObjRecovery>
peer_image_recovery_plan(const AuthorityImage &auth, const PeerInfo &peer) {
  return image_recovery_gaps(effective_image(peer), auth);
}

inline std::vector<ObjRecovery> pg_image_recovery_plan(const AuthorityImage &auth,
                                                       const PGInfo &pg) {
  return image_recovery_gaps(effective_image(pg), auth);
}

inline std::vector<PeerRecoveryPlan>
build_peer_recovery_plans(const AuthorityImage &auth,
                          journal_seq_t authoritative_seq,
                          const std::vector<PeerInfo> &peers) {
  std::vector<PeerRecoveryPlan> plans;
  for (const auto &raw : peers) {
    auto peer = normalized_peer_info(raw);
    auto gaps = peer_image_recovery_plan(auth, peer);
    if (!gaps.empty() || peer.committed_seq < authoritative_seq) {
      plans.push_back(PeerRecoveryPlan{
          .target = peer.osd,
          .peer_committed_seq = peer.committed_seq,
          .authoritative_seq = authoritative_seq,
          .recoveries = std::move(gaps),
      });
    }
  }
  return plans;
}

// ── OSD set description ────────────────────────────────────────────

// An acting set with roles. Index 0 is primary.
struct ActingSet {
  std::vector<osd_id_t> osds;
  epoch_t epoch = 0;

  osd_id_t primary() const { return osds.empty() ? -1 : osds[0]; }
  int size() const { return static_cast<int>(osds.size()); }
  bool contains(osd_id_t osd) const {
    for (auto o : osds)
      if (o == osd)
        return true;
    return false;
  }
};

} // namespace vermilion::peering
