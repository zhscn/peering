import Peering.Machine

namespace Peering

structure InvariantChecks where
  haveEnoughInfo : Bool
  imageInvariant : Bool
  imageClean : Bool
  imageRecovering : Bool
  deriving DecidableEq, Repr

def authorityEntryBackedByKnownPeer (knownPeers : List PeerInfo)
    (entry : ObjectId × ObjectAuthority) : Prop :=
  ∃ peer ∈ knownPeers,
    lookupLength (effectivePeerImage peer) entry.1 = entry.2.authorityLength

def authSourcesBackedByKnownPeers (snap : Snapshot) : Prop :=
  ∀ entry ∈ snap.authSources.entries,
    authorityEntryBackedByKnownPeer (knownPeerImages snap) entry

def authImageMatchesKnownPeers (snap : Snapshot) : Prop :=
  sameImage snap.authImage (authorityImageValues (authoritativeSources (knownPeerImages snap)))

def authSeqMatchesKnownPeers (snap : Snapshot) : Prop :=
  snap.authSeq = authoritativeCommittedSeq (knownPeerImages snap)

def authSourcesMatchKnownPeers (snap : Snapshot) : Prop :=
  sameImage (authorityImageValues snap.authSources)
    (authorityImageValues (authoritativeSources (knownPeerImages snap)))

def localWithinAuthority (snap : Snapshot) : Prop :=
  snap.localInfo.committedSeq ≤ snap.authSeq ∧
    prefixImage (effectivePGImage snap.localInfo) snap.authImage

def actingReplicaWithinAuthority (snap : Snapshot) : Prop :=
  ∀ peer ∈ actingReplicaImages snap,
    peer.committedSeq ≤ snap.authSeq ∧
      prefixImage (effectivePeerImage peer) snap.authImage

def peerRecoveryPlansMatchAuthority (snap : Snapshot) : Prop :=
  snap.peerRecoveryPlans =
    buildPeerRecoveryPlans
      (authoritativeSources (knownPeerImages snap))
      (authoritativeCommittedSeq (knownPeerImages snap))
      (actingReplicaImages snap)

def localRecoveryPlanMatchesAuthority (snap : Snapshot) : Prop :=
  snap.localRecoveryPlan =
    pgImageRecoveryPlan
      (authoritativeSources (knownPeerImages snap))
      snap.localInfo

def ImageInvariant (snap : Snapshot) : Prop :=
  authSourcesBackedByKnownPeers snap ∧
    authImageMatchesKnownPeers snap ∧
    authSeqMatchesKnownPeers snap ∧
    authSourcesMatchKnownPeers snap ∧
    localWithinAuthority snap ∧
    actingReplicaWithinAuthority snap ∧
    peerRecoveryPlansMatchAuthority snap ∧
    localRecoveryPlanMatchesAuthority snap

def ImageClean (snap : Snapshot) : Prop :=
  ImageInvariant snap ∧
    snap.peerRecoveryPlans = [] ∧
    snap.localRecoveryPlan = [] ∧
    snap.localInfo.committedSeq ≥ snap.authSeq ∧
    sameImage (effectivePGImage snap.localInfo) snap.authImage ∧
    ∀ peer ∈ actingReplicaImages snap,
      peer.committedSeq ≥ snap.authSeq ∧
        sameImage (effectivePeerImage peer) snap.authImage

def ImageRecovering (snap : Snapshot) : Prop :=
  ImageInvariant snap ∧
    ¬ ImageClean snap ∧
    (
      snap.peerRecoveryPlans ≠ [] ∨
      snap.localRecoveryPlan ≠ [] ∨
      snap.localInfo.committedSeq < snap.authSeq ∨
      ∃ peer ∈ actingReplicaImages snap, peer.committedSeq < snap.authSeq
    )

def authorityEntryBackedByKnownPeer? (knownPeers : List PeerInfo)
    (entry : ObjectId × ObjectAuthority) : Bool :=
  knownPeers.any fun peer =>
    lookupLength (effectivePeerImage peer) entry.1 = entry.2.authorityLength

def authSourcesBackedByKnownPeers? (snap : Snapshot) : Bool :=
  snap.authSources.entries.all fun entry =>
    authorityEntryBackedByKnownPeer? (knownPeerImages snap) entry

def actingReplicaWithinAuthority? (snap : Snapshot) : Bool :=
  boolAnd ((actingReplicaImages snap).map fun peer =>
    decide (peer.committedSeq ≤ snap.authSeq) &&
      prefixImage? (effectivePeerImage peer) snap.authImage)

def peerRecoveryPlansMatchAuthority? (snap : Snapshot) : Bool :=
  let knownPeers := knownPeerImages snap
  let recomputedSources := authoritativeSources knownPeers
  let recomputedSeq := authoritativeCommittedSeq knownPeers
  snap.peerRecoveryPlans =
    buildPeerRecoveryPlans recomputedSources recomputedSeq (actingReplicaImages snap)

def localRecoveryPlanMatchesAuthority? (snap : Snapshot) : Bool :=
  let knownPeers := knownPeerImages snap
  let recomputedSources := authoritativeSources knownPeers
  snap.localRecoveryPlan = pgImageRecoveryPlan recomputedSources snap.localInfo

def snapshotImageInvariant? (snap : Snapshot) : Bool :=
  let knownPeers := knownPeerImages snap
  let recomputedSources := authoritativeSources knownPeers
  let recomputedImage := authorityImageValues recomputedSources
  let recomputedSeq := authoritativeCommittedSeq knownPeers
  authSourcesBackedByKnownPeers? snap &&
    sameImage? snap.authImage recomputedImage &&
    decide (snap.authSeq = recomputedSeq) &&
    sameImage? (authorityImageValues snap.authSources) recomputedImage &&
    decide (snap.localInfo.committedSeq ≤ snap.authSeq) &&
    prefixImage? (effectivePGImage snap.localInfo) snap.authImage &&
    actingReplicaWithinAuthority? snap &&
    peerRecoveryPlansMatchAuthority? snap &&
    localRecoveryPlanMatchesAuthority? snap

def snapshotImageClean? (snap : Snapshot) : Bool :=
  if !snapshotImageInvariant? snap then
    false
  else if !snap.peerRecoveryPlans.isEmpty || !snap.localRecoveryPlan.isEmpty then
    false
  else if snap.localInfo.committedSeq < snap.authSeq ||
      !sameImage? (effectivePGImage snap.localInfo) snap.authImage then
    false
  else
    boolAnd ((actingReplicaImages snap).map fun peer =>
      decide (peer.committedSeq ≥ snap.authSeq) &&
        sameImage? (effectivePeerImage peer) snap.authImage)

def snapshotImageRecovering? (snap : Snapshot) : Bool :=
  let peerSeqLag := (actingReplicaImages snap).any fun peer => peer.committedSeq < snap.authSeq
  snapshotImageInvariant? snap && !snapshotImageClean? snap &&
    (!snap.peerRecoveryPlans.isEmpty ||
      !snap.localRecoveryPlan.isEmpty ||
      snap.localInfo.committedSeq < snap.authSeq ||
      peerSeqLag)

def computeInvariantChecks (snap : Snapshot) : InvariantChecks :=
  {
    haveEnoughInfo := haveEnoughInfo snap
    imageInvariant := snapshotImageInvariant? snap
    imageClean := snapshotImageClean? snap
    imageRecovering := snapshotImageRecovering? snap
  }

theorem imageClean_implies_imageInvariant (snap : Snapshot) :
    ImageClean snap → ImageInvariant snap := by
  intro h
  exact h.left

theorem imageRecovering_implies_imageInvariant (snap : Snapshot) :
    ImageRecovering snap → ImageInvariant snap := by
  intro h
  exact h.left

theorem imageRecovering_not_imageClean (snap : Snapshot) :
    ImageRecovering snap → ¬ ImageClean snap := by
  intro h
  exact h.right.left

theorem snapshotImageClean?_implies_invariant_check (snap : Snapshot) :
    snapshotImageClean? snap = true → snapshotImageInvariant? snap = true := by
  intro h
  unfold snapshotImageClean? at h
  by_cases hinv : snapshotImageInvariant? snap
  · simp [hinv]
  · simp [hinv] at h

theorem snapshotImageRecovering?_implies_invariant_check (snap : Snapshot) :
    snapshotImageRecovering? snap = true → snapshotImageInvariant? snap = true := by
  intro h
  unfold snapshotImageRecovering? at h
  simp at h
  exact h.left.left

end Peering
