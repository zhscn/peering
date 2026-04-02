import Std.Data.TreeMap.Lemmas
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

theorem prefixImage_of_prefixImage? (lhs rhs : ObjectImage) :
    prefixImage? lhs rhs = true → prefixImage lhs rhs := by
  intro h obj
  by_cases hPos : 0 < lookupLength lhs obj
  · have hMem : obj ∈ ObjectImage.support lhs := mem_support_of_lookupLength_pos lhs hPos
    unfold prefixImage? at h
    have hAll := List.all_eq_true.mp h
    have hObj := hAll obj hMem
    simpa using hObj
  · have hZero : lookupLength lhs obj = 0 := Nat.eq_zero_of_not_pos hPos
    simp [hZero]

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

private def eraseDupsIdem {α} [BEq α] [LawfulBEq α] :
    (xs : List α) → xs.eraseDups.eraseDups = xs.eraseDups
  | [] => by
      simp
  | a :: as => by
      rw [List.eraseDups_cons, List.eraseDups_cons]
      have hFilter :
          List.filter (fun b => !b == a) ((List.filter (fun b => !b == a) as).eraseDups) =
            (List.filter (fun b => !b == a) as).eraseDups := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hb' : b ∈ List.filter (fun b => !b == a) as := (List.mem_eraseDups).1 hb
        exact (List.mem_filter.mp hb').2
      have ih := eraseDupsIdem (List.filter (fun b => !b == a) as)
      simp [hFilter, ih]
termination_by xs => xs.length
decreasing_by
  exact Nat.lt_add_one_of_le (List.length_filter_le _ as)

theorem eraseDups_idem {α} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.eraseDups = xs.eraseDups := by
  simpa using eraseDupsIdem xs

theorem removeAll_self_of_no_mem {α} [BEq α] [LawfulBEq α]
    (xs ys : List α)
    (h : ∀ a ∈ xs, a ∉ ys) :
    xs.removeAll ys = xs := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      have hNot : a ∉ ys := h a (by simp)
      have hTail : ∀ b ∈ xs, b ∉ ys := by
        intro b hb
        exact h b (by simp [hb])
      simp [List.cons_removeAll, hNot, ih hTail]

theorem removeAll_append_left {α} [BEq α] [LawfulBEq α]
    (pre xs zs : List α)
    (h : ∀ a ∈ pre, a ∈ xs) :
    (pre ++ zs).removeAll xs = zs.removeAll xs := by
  induction pre with
  | nil =>
      simp
  | cons a pre ih =>
      have hMem : a ∈ xs := h a (by simp)
      have hTail : ∀ b ∈ pre, b ∈ xs := by
        intro b hb
        exact h b (by simp [hb])
      simp [List.cons_removeAll, hMem, ih hTail]

theorem eraseDups_append_eraseDups_left {α} [BEq α] [LawfulBEq α]
    (xs ys : List α) :
    (xs ++ (xs ++ ys).eraseDups).eraseDups = (xs ++ ys).eraseDups := by
  rw [List.eraseDups_append, List.eraseDups_append]
  have hPrefix : ∀ a ∈ xs.eraseDups, a ∈ xs := by
    intro a ha
    exact (List.mem_eraseDups).1 ha
  have hNoMem : ∀ a ∈ (ys.removeAll xs).eraseDups, a ∉ xs := by
    intro a ha hax
    have ha' : a ∈ ys.removeAll xs := (List.mem_eraseDups).1 ha
    simp [List.removeAll, hax] at ha'
  have hRemovePrefix :
      (xs.eraseDups ++ (ys.removeAll xs).eraseDups).removeAll xs =
        ((ys.removeAll xs).eraseDups).removeAll xs := by
    exact removeAll_append_left xs.eraseDups xs (ys.removeAll xs).eraseDups hPrefix
  rw [hRemovePrefix]
  rw [removeAll_self_of_no_mem (ys.removeAll xs).eraseDups xs hNoMem]
  simpa using (eraseDups_idem (xs := ys.removeAll xs))

private theorem exists_entry_of_mem_keys
    {entries : List (ObjectId × ObjectAuthority)} {obj : ObjectId}
    (hMem : obj ∈ entries.map Prod.fst) :
    ∃ authority, (obj, authority) ∈ entries := by
  rcases (List.mem_map).1 hMem with ⟨entry, hEntry, hEq⟩
  exact ⟨entry.2, by
    cases entry
    simpa using hEq ▸ hEntry⟩

theorem lookupAuthority_pos_of_mem_support_of_positive_entries
    (raw : AuthorityImage)
    (hPos : ∀ entry ∈ raw.entries, 0 < entry.2.authorityLength)
    {obj : ObjectId}
    (hMem : obj ∈ AuthorityImage.support raw) :
    0 < (lookupAuthority raw obj).authorityLength := by
  have hKey : obj ∈ raw.entries.map Prod.fst := (List.mem_eraseDups).1 hMem
  rcases exists_entry_of_mem_keys hKey with ⟨authority, hEntry⟩
  exact Nat.lt_of_lt_of_le
    (hPos (obj, authority) hEntry)
    (lookupAuthorityEntries_ge_of_mem hEntry)

private theorem filterMap_lookupAuthority_of_positive_list
    (raw : AuthorityImage) (xs : List ObjectId)
    (hPos : ∀ obj ∈ xs, 0 < (lookupAuthority raw obj).authorityLength) :
    xs.filterMap (fun obj =>
      let authority := lookupAuthority raw obj
      if authority.authorityLength = 0 then
        none
      else
        some (obj, authority)) =
      xs.map (fun obj => (obj, lookupAuthority raw obj)) := by
  induction xs with
  | nil =>
      simp
  | cons obj rest ih =>
      have hPosObj : 0 < (lookupAuthority raw obj).authorityLength := hPos obj (by simp)
      have hPosRest : ∀ obj' ∈ rest, 0 < (lookupAuthority raw obj').authorityLength := by
        intro obj' hMem
        exact hPos obj' (by simp [hMem])
      simp [Nat.ne_of_gt hPosObj, ih hPosRest]

theorem support_canonicalAuthorityImage_of_positive_entries
    (raw : AuthorityImage)
    (hPos : ∀ entry ∈ raw.entries, 0 < entry.2.authorityLength) :
    AuthorityImage.support (canonicalAuthorityImage raw) = AuthorityImage.support raw := by
  unfold AuthorityImage.support canonicalAuthorityImage
  have hPosSupport : ∀ obj ∈ AuthorityImage.support raw,
      0 < (lookupAuthority raw obj).authorityLength := by
    intro obj hMem
    exact lookupAuthority_pos_of_mem_support_of_positive_entries raw hPos hMem
  rw [filterMap_lookupAuthority_of_positive_list raw (AuthorityImage.support raw) hPosSupport]
  unfold AuthorityImage.keys AuthorityImage.support
  change
    (List.map Prod.fst (List.map (fun obj => (obj, lookupAuthority raw obj)) raw.keys.eraseDups)).eraseDups =
      raw.keys.eraseDups
  rw [List.map_map]
  change (List.map (fun obj => obj) raw.keys.eraseDups).eraseDups = raw.keys.eraseDups
  simp
  simpa using (eraseDups_idem (xs := raw.keys))

theorem authorityLength_pos_of_mem_authorityFromPeerInfo
    (info : PeerInfo) {obj : ObjectId} {authority : ObjectAuthority} :
    (obj, authority) ∈ (authorityFromPeerInfo info).entries →
      0 < authority.authorityLength := by
  intro hMem
  by_cases hPos : 0 < authority.authorityLength
  · exact hPos
  · have hEq : authority.authorityLength = lookupLength (effectivePeerImage info) obj :=
        authorityLength_eq_lookupLength_of_mem_authorityFromPeerInfo info hMem
    have hZero : lookupLength (effectivePeerImage info) obj = 0 := by
      rw [← hEq]
      exact Nat.eq_zero_of_not_pos hPos
    unfold authorityFromPeerInfo authorityFromImage at hMem
    rcases (List.mem_filterMap).1 hMem with ⟨a, _hSupp, hSome⟩
    by_cases hLookupZero : lookupLength (normalizedPeerInfo info).image a = 0
    · simp [hLookupZero] at hSome
    · simp [hLookupZero] at hSome
      rcases hSome with ⟨hEqObj, hEqAuth⟩
      cases hEqObj
      cases hEqAuth
      have : lookupLength (normalizedPeerInfo info).image obj = 0 := by
        simpa [normalizedPeerInfo] using hZero
      exact False.elim (hLookupZero this)

theorem rawAuthoritySources_entries_positive
    (infos : List PeerInfo) (entry : ObjectId × ObjectAuthority)
    (hMem : entry ∈ (rawAuthoritySources infos).entries) :
    0 < entry.2.authorityLength := by
  rcases mem_rawAuthoritySources_entries_exists_peer infos entry hMem with ⟨info, _hInfo, hEntry⟩
  exact authorityLength_pos_of_mem_authorityFromPeerInfo info hEntry

theorem support_authoritativeSources
    (infos : List PeerInfo) :
    AuthorityImage.support (authoritativeSources infos) =
      AuthorityImage.support (rawAuthoritySources infos) := by
  unfold authoritativeSources
  apply support_canonicalAuthorityImage_of_positive_entries
  intro entry hEntry
  exact rawAuthoritySources_entries_positive infos entry hEntry

theorem knownPeerImages_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    knownPeerImages (refreshAuthorityFromKnownPeers snap) = knownPeerImages snap := by
  simp [refreshAuthorityFromKnownPeers, knownPeerImages]

theorem actingReplicaImages_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    actingReplicaImages (refreshAuthorityFromKnownPeers snap) = actingReplicaImages snap := by
  simp [refreshAuthorityFromKnownPeers, actingReplicaImages]

theorem knownPeerImages_refreshRecoveryPlansFromCurrentAuthority
    (snap : Snapshot) :
    knownPeerImages (refreshRecoveryPlansFromCurrentAuthority snap) = knownPeerImages snap := by
  simp [refreshRecoveryPlansFromCurrentAuthority, knownPeerImages]

theorem actingReplicaImages_refreshRecoveryPlansFromCurrentAuthority
    (snap : Snapshot) :
    actingReplicaImages (refreshRecoveryPlansFromCurrentAuthority snap) = actingReplicaImages snap := by
  simp [refreshRecoveryPlansFromCurrentAuthority, actingReplicaImages]

theorem authSeqMatchesKnownPeers_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    authSeqMatchesKnownPeers (refreshAuthorityFromKnownPeers snap) := by
  unfold authSeqMatchesKnownPeers
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshAuthorityFromKnownPeers]

theorem authSeq_eq_authoritativeCommittedSeq_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    (refreshAuthorityFromKnownPeers snap).authSeq =
      authoritativeCommittedSeq (knownPeerImages snap) := by
  simp [refreshAuthorityFromKnownPeers]

theorem authSources_eq_authoritativeSources_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    (refreshAuthorityFromKnownPeers snap).authSources =
      authoritativeSources (knownPeerImages snap) := by
  simp [refreshAuthorityFromKnownPeers]

theorem authImage_eq_authorityImageValues_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    (refreshAuthorityFromKnownPeers snap).authImage =
      authorityImageValues (authoritativeSources (knownPeerImages snap)) := by
  simp [refreshAuthorityFromKnownPeers]

theorem localPeer_mem_knownPeerImages (snap : Snapshot) :
    { osd := snap.whoami
      committedSeq := (normalizedPGInfo snap.localInfo).committedSeq
      committedLength := (normalizedPGInfo snap.localInfo).committedLength
      image := (normalizedPGInfo snap.localInfo).image
      lastEpochStarted := (normalizedPGInfo snap.localInfo).lastEpochStarted
      lastIntervalStarted := (normalizedPGInfo snap.localInfo).lastIntervalStarted
    } ∈ knownPeerImages snap := by
  simp [knownPeerImages]

theorem knownPeerImages_ne_nil (snap : Snapshot) :
    knownPeerImages snap ≠ [] := by
  intro hNil
  have hMem := localPeer_mem_knownPeerImages snap
  rw [hNil] at hMem
  cases hMem

theorem mem_knownPeerRemoteFoldr_of_mem
    (whoami : OsdId) (entries : List (OsdId × PeerInfo))
    (osd : OsdId) (info : PeerInfo)
    (hMem : (osd, info) ∈ entries)
    (hWho : osd ≠ whoami) :
    { (normalizedPeerInfo info) with osd := osd } ∈
      entries.foldr
        (fun entry acc =>
          if entry.1 = whoami then
            acc
          else
            let info := normalizedPeerInfo entry.2
            { info with osd := entry.1 } :: acc)
        [] := by
  induction entries with
  | nil =>
      cases hMem
  | cons head tail ih =>
      cases head with
      | mk osd' info' =>
          simp at hMem
          rcases hMem with hHead | hTail
          · rcases hHead with ⟨rfl, rfl⟩
            simp [hWho]
          · by_cases hEq : osd' = whoami
            · simp [hEq, ih hTail]
            · simp [hEq, ih hTail]

theorem remotePeer_mem_knownPeerImages_of_lookupPeerInfo
    (snap : Snapshot) (osd : OsdId) (info : PeerInfo)
    (hWho : osd ≠ snap.whoami)
    (hLookup : lookupPeerInfo snap.peerInfo osd = some info) :
    { (normalizedPeerInfo info) with osd := osd } ∈ knownPeerImages snap := by
  apply List.mem_append.mpr
  left
  apply mem_knownPeerRemoteFoldr_of_mem snap.whoami
  · simpa [lookupPeerInfo] using
      ((Std.TreeMap.mem_toList_iff_getElem?_eq_some (t := snap.peerInfo) (k := osd) (v := info)).2
        hLookup)
  · exact hWho

theorem localCommittedSeq_le_authSeq_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    (normalizedPGInfo snap.localInfo).committedSeq ≤
      (refreshAuthorityFromKnownPeers snap).authSeq := by
  rw [refreshAuthorityFromKnownPeers]
  simp
  exact committedSeq_le_authoritativeCommittedSeq_of_mem
    (knownPeerImages snap)
    { osd := snap.whoami
      committedSeq := (normalizedPGInfo snap.localInfo).committedSeq
      committedLength := (normalizedPGInfo snap.localInfo).committedLength
      image := (normalizedPGInfo snap.localInfo).image
      lastEpochStarted := (normalizedPGInfo snap.localInfo).lastEpochStarted
      lastIntervalStarted := (normalizedPGInfo snap.localInfo).lastIntervalStarted
    }
    (localPeer_mem_knownPeerImages snap)

theorem localImage_prefix_authImage_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    prefixImage (effectivePGImage snap.localInfo)
      (refreshAuthorityFromKnownPeers snap).authImage := by
  rw [refreshAuthorityFromKnownPeers]
  let localPeer : PeerInfo :=
    { osd := snap.whoami
      committedSeq := (normalizedPGInfo snap.localInfo).committedSeq
      committedLength := (normalizedPGInfo snap.localInfo).committedLength
      image := (normalizedPGInfo snap.localInfo).image
      lastEpochStarted := (normalizedPGInfo snap.localInfo).lastEpochStarted
      lastIntervalStarted := (normalizedPGInfo snap.localInfo).lastIntervalStarted
    }
  have hLocalImage : effectivePeerImage localPeer = effectivePGImage snap.localInfo := by
    let image := effectivePGImage snap.localInfo
    change effectivePeerImage
        { osd := snap.whoami
          committedSeq := (normalizedPGInfo snap.localInfo).committedSeq
          committedLength := primaryLength image
          image := image
          lastEpochStarted := (normalizedPGInfo snap.localInfo).lastEpochStarted
          lastIntervalStarted := (normalizedPGInfo snap.localInfo).lastIntervalStarted } = image
    by_cases h : image.entries = []
    · have hlen : primaryLength image = 0 := by
        simp [primaryLength, lookupLength, lookupLengthEntries, h, image]
      simp [effectivePeerImage, h, hlen]
    · simp [effectivePeerImage, h]
  simpa [localPeer, authoritativeImage, hLocalImage] using
    (prefixImage_authoritativeImage_of_mem
      (knownPeerImages snap)
      localPeer
      (localPeer_mem_knownPeerImages snap))

theorem localWithinAuthority_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    localWithinAuthority (refreshAuthorityFromKnownPeers snap) := by
  constructor
  · simpa [localWithinAuthority, refreshAuthorityFromKnownPeers] using
      localCommittedSeq_le_authSeq_refreshAuthorityFromKnownPeers snap
  · simpa [localWithinAuthority] using
      localImage_prefix_authImage_refreshAuthorityFromKnownPeers snap

theorem actingReplicaWithinAuthority_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    actingReplicaWithinAuthority (refreshAuthorityFromKnownPeers snap) := by
  intro peer hMem
  rw [actingReplicaImages_refreshAuthorityFromKnownPeers] at hMem
  rw [refreshAuthorityFromKnownPeers]
  let step : OsdId → List PeerInfo → List PeerInfo :=
    fun osd acc =>
      if !osdNonneg osd || osd = snap.whoami then
        acc
      else
        match lookupPeerInfo snap.peerInfo osd with
        | some info =>
            let normalized := normalizedPeerInfo info
            { normalized with osd := osd } :: acc
        | none =>
            { osd := osd } :: acc
  have hStep :
      ∀ (osds : List OsdId) peer,
        peer ∈ List.foldr step [] osds →
          peer.committedSeq ≤ authoritativeCommittedSeq (knownPeerImages snap) ∧
            prefixImage (effectivePeerImage peer) (authoritativeImage (knownPeerImages snap)) := by
    intro osds
    induction osds with
    | nil =>
        intro peer hMem
        cases hMem
    | cons osd tail ih =>
        intro peer hMem
        by_cases hNonneg : osdNonneg osd
        · by_cases hSelf : osd = snap.whoami
          · simp [step, hSelf] at hMem
            have hTail : peer ∈ List.foldr step [] tail := by
              simpa [step] using hMem
            exact ih peer hTail
          · cases hLookup : lookupPeerInfo snap.peerInfo osd with
            | none =>
                simp [step, hNonneg, hSelf, hLookup] at hMem
                rcases hMem with rfl | hTail
                · constructor
                  · exact Nat.zero_le _
                  · intro obj
                    simp [effectivePeerImage, lookupLength, lookupLengthEntries]
                · have hTail' : peer ∈ List.foldr step [] tail := by
                    simpa [step] using hTail
                  exact ih peer hTail'
            | some info =>
                simp [step, hNonneg, hSelf, hLookup] at hMem
                rcases hMem with rfl | hTail
                · constructor
                  · exact committedSeq_le_authoritativeCommittedSeq_of_mem
                      (knownPeerImages snap)
                      ({ (normalizedPeerInfo info) with osd := osd })
                      (remotePeer_mem_knownPeerImages_of_lookupPeerInfo snap osd info hSelf hLookup)
                  · simpa [authoritativeImage] using
                      (prefixImage_authoritativeImage_of_mem
                        (knownPeerImages snap)
                        ({ (normalizedPeerInfo info) with osd := osd })
                        (remotePeer_mem_knownPeerImages_of_lookupPeerInfo snap osd info hSelf hLookup))
                · have hTail' : peer ∈ List.foldr step [] tail := by
                    simpa [step] using hTail
                  exact ih peer hTail'
        · simp [step, hNonneg] at hMem
          have hTail : peer ∈ List.foldr step [] tail := by
            simpa [step] using hMem
          exact ih peer hTail
  change peer ∈ List.foldr step [] snap.acting.osds at hMem
  simpa [authoritativeImage] using hStep snap.acting.osds peer hMem

theorem authSourcesBackedByKnownPeers_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    authSourcesBackedByKnownPeers (refreshAuthorityFromKnownPeers snap) := by
  intro entry hEntry
  let known := knownPeerImages snap
  let raw := rawAuthoritySources known
  have hEntry' : entry ∈ (canonicalAuthorityImage raw).entries := by
    simpa [refreshAuthorityFromKnownPeers, authoritativeSources, known, raw] using hEntry
  unfold canonicalAuthorityImage at hEntry'
  rcases (List.mem_filterMap).1 hEntry' with ⟨obj, hObj, hSome⟩
  by_cases hZero : (lookupAuthority raw obj).authorityLength = 0
  · simp [hZero] at hSome
  · simp [hZero] at hSome
    have hPair : (obj, lookupAuthority raw obj) = entry := by
      simpa using hSome
    cases hPair
    unfold authorityEntryBackedByKnownPeer
    have hLookupMem :
        (obj, lookupAuthority raw obj) ∈ raw.entries := by
      apply mem_lookupAuthorityEntries_of_pos
      exact Nat.pos_of_ne_zero hZero
    rcases mem_rawAuthoritySources_entries_exists_peer known
        (obj, lookupAuthority raw obj) hLookupMem with ⟨peer, hPeer, hPeerEntry⟩
    refine ⟨peer, hPeer, ?_⟩
    rw [← authorityLength_eq_lookupLength_of_mem_authorityFromPeerInfo peer hPeerEntry]

theorem authImageMatchesKnownPeers_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    authImageMatchesKnownPeers (refreshAuthorityFromKnownPeers snap) := by
  unfold authImageMatchesKnownPeers
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshAuthorityFromKnownPeers, sameImage_refl]

theorem authSourcesMatchKnownPeers_refreshAuthorityFromKnownPeers
    (snap : Snapshot) :
    authSourcesMatchKnownPeers (refreshAuthorityFromKnownPeers snap) := by
  unfold authSourcesMatchKnownPeers
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshAuthorityFromKnownPeers, sameImage_refl]

theorem peerRecoveryPlansMatchAuthority_refreshRecoveryPlansFromCurrentAuthority
    (snap : Snapshot)
    (hAuthSeq : snap.authSeq = authoritativeCommittedSeq (knownPeerImages snap))
    (hAuthSources : snap.authSources = authoritativeSources (knownPeerImages snap)) :
    peerRecoveryPlansMatchAuthority (refreshRecoveryPlansFromCurrentAuthority snap) := by
  unfold peerRecoveryPlansMatchAuthority
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  rw [actingReplicaImages_refreshRecoveryPlansFromCurrentAuthority]
  simp [refreshRecoveryPlansFromCurrentAuthority, hAuthSeq, hAuthSources]

theorem localRecoveryPlanMatchesAuthority_refreshRecoveryPlansFromCurrentAuthority
    (snap : Snapshot)
    (hAuthSources : snap.authSources = authoritativeSources (knownPeerImages snap)) :
    localRecoveryPlanMatchesAuthority (refreshRecoveryPlansFromCurrentAuthority snap) := by
  unfold localRecoveryPlanMatchesAuthority
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  simp [refreshRecoveryPlansFromCurrentAuthority, hAuthSources,
    pgImageRecoveryPlan, effectivePGImage_normalizedPGInfo]

theorem imageInvariant_refreshRecoveryPlansFromCurrentAuthority
    (snap : Snapshot)
    (hBacked : authSourcesBackedByKnownPeers snap)
    (hAuthImage : authImageMatchesKnownPeers snap)
    (hAuthSeq : snap.authSeq = authoritativeCommittedSeq (knownPeerImages snap))
    (hAuthSources : snap.authSources = authoritativeSources (knownPeerImages snap))
    (hLocal : localWithinAuthority snap)
    (hActing : actingReplicaWithinAuthority snap) :
    ImageInvariant (refreshRecoveryPlansFromCurrentAuthority snap) := by
  constructor
  · simpa [authSourcesBackedByKnownPeers, refreshRecoveryPlansFromCurrentAuthority,
      knownPeerImages_refreshRecoveryPlansFromCurrentAuthority] using hBacked
  constructor
  · simpa [authImageMatchesKnownPeers, refreshRecoveryPlansFromCurrentAuthority,
      knownPeerImages_refreshRecoveryPlansFromCurrentAuthority] using hAuthImage
  constructor
  · simpa [authSeqMatchesKnownPeers, refreshRecoveryPlansFromCurrentAuthority,
      knownPeerImages_refreshRecoveryPlansFromCurrentAuthority] using hAuthSeq
  constructor
  · unfold authSourcesMatchKnownPeers
    rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
    simp [refreshRecoveryPlansFromCurrentAuthority, hAuthSources, sameImage_refl]
  constructor
  · simpa [localWithinAuthority, refreshRecoveryPlansFromCurrentAuthority] using hLocal
  constructor
  · simpa [actingReplicaWithinAuthority, refreshRecoveryPlansFromCurrentAuthority,
      actingReplicaImages_refreshRecoveryPlansFromCurrentAuthority] using hActing
  constructor
  · exact peerRecoveryPlansMatchAuthority_refreshRecoveryPlansFromCurrentAuthority
      snap hAuthSeq hAuthSources
  · exact localRecoveryPlanMatchesAuthority_refreshRecoveryPlansFromCurrentAuthority
      snap hAuthSources

theorem authSeqMatchesKnownPeers_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    authSeqMatchesKnownPeers (refreshImageStateFromKnownPeers snap) := by
  unfold authSeqMatchesKnownPeers
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  exact authSeqMatchesKnownPeers_refreshAuthorityFromKnownPeers snap

theorem authImageMatchesKnownPeers_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    authImageMatchesKnownPeers (refreshImageStateFromKnownPeers snap) := by
  unfold authImageMatchesKnownPeers
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  exact authImageMatchesKnownPeers_refreshAuthorityFromKnownPeers snap

theorem authSourcesMatchKnownPeers_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    authSourcesMatchKnownPeers (refreshImageStateFromKnownPeers snap) := by
  unfold authSourcesMatchKnownPeers
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  exact authSourcesMatchKnownPeers_refreshAuthorityFromKnownPeers snap

theorem authSeq_eq_authoritativeCommittedSeq_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    (refreshImageStateFromKnownPeers snap).authSeq =
      authoritativeCommittedSeq (knownPeerImages (refreshImageStateFromKnownPeers snap)) := by
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshRecoveryPlansFromCurrentAuthority, refreshAuthorityFromKnownPeers]

theorem authSources_eq_authoritativeSources_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    (refreshImageStateFromKnownPeers snap).authSources =
      authoritativeSources (knownPeerImages (refreshImageStateFromKnownPeers snap)) := by
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshRecoveryPlansFromCurrentAuthority, refreshAuthorityFromKnownPeers]

theorem authImage_eq_authorityImageValues_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    (refreshImageStateFromKnownPeers snap).authImage =
      authorityImageValues
        (authoritativeSources (knownPeerImages (refreshImageStateFromKnownPeers snap))) := by
  rw [refreshImageStateFromKnownPeers]
  rw [knownPeerImages_refreshRecoveryPlansFromCurrentAuthority]
  rw [knownPeerImages_refreshAuthorityFromKnownPeers]
  simp [refreshRecoveryPlansFromCurrentAuthority, refreshAuthorityFromKnownPeers]

theorem peerRecoveryPlansMatchAuthority_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    peerRecoveryPlansMatchAuthority (refreshImageStateFromKnownPeers snap) := by
  apply peerRecoveryPlansMatchAuthority_refreshRecoveryPlansFromCurrentAuthority
  · exact authSeqMatchesKnownPeers_refreshAuthorityFromKnownPeers snap
  · rfl

theorem localRecoveryPlanMatchesAuthority_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    localRecoveryPlanMatchesAuthority (refreshImageStateFromKnownPeers snap) := by
  apply localRecoveryPlanMatchesAuthority_refreshRecoveryPlansFromCurrentAuthority
  · rfl

theorem imageInvariant_refreshImageStateFromKnownPeers
    (snap : Snapshot) :
    ImageInvariant (refreshImageStateFromKnownPeers snap) := by
  apply imageInvariant_refreshRecoveryPlansFromCurrentAuthority
  · exact authSourcesBackedByKnownPeers_refreshAuthorityFromKnownPeers snap
  · exact authImageMatchesKnownPeers_refreshAuthorityFromKnownPeers snap
  · exact authSeqMatchesKnownPeers_refreshAuthorityFromKnownPeers snap
  · rw [knownPeerImages_refreshAuthorityFromKnownPeers]
    simp [refreshAuthorityFromKnownPeers]
  · exact localWithinAuthority_refreshAuthorityFromKnownPeers snap
  · exact actingReplicaWithinAuthority_refreshAuthorityFromKnownPeers snap

theorem imageInvariant_update_probe_bookkeeping
    (snap : Snapshot) (peersResponded timedOutProbes : List OsdId) :
    ImageInvariant snap →
      ImageInvariant {
        snap with
          peersResponded := peersResponded
          timedOutProbes := timedOutProbes
      } := by
  intro h
  simpa [ImageInvariant, authSourcesBackedByKnownPeers, authImageMatchesKnownPeers,
    authSeqMatchesKnownPeers, authSourcesMatchKnownPeers, localWithinAuthority,
    actingReplicaWithinAuthority, peerRecoveryPlansMatchAuthority,
    localRecoveryPlanMatchesAuthority, knownPeerImages, actingReplicaImages]
    using h

theorem imageInvariant_update_query_bookkeeping
    (snap : Snapshot) (peersQueried : List OsdId) :
    ImageInvariant snap →
      ImageInvariant {
        snap with
          peersQueried := peersQueried
      } := by
  intro h
  simpa [ImageInvariant, authSourcesBackedByKnownPeers, authImageMatchesKnownPeers,
    authSeqMatchesKnownPeers, authSourcesMatchKnownPeers, localWithinAuthority,
    actingReplicaWithinAuthority, peerRecoveryPlansMatchAuthority,
    localRecoveryPlanMatchesAuthority, knownPeerImages, actingReplicaImages]
    using h

theorem imageInvariant_update_controlFlags
    (snap : Snapshot) (pendingActingChange needUpThru activated : Bool) :
    ImageInvariant snap →
      ImageInvariant {
        snap with
          pendingActingChange := pendingActingChange
          needUpThru := needUpThru
          activated := activated
      } := by
  intro h
  simpa [ImageInvariant, authSourcesBackedByKnownPeers, authImageMatchesKnownPeers,
    authSeqMatchesKnownPeers, authSourcesMatchKnownPeers, localWithinAuthority,
    actingReplicaWithinAuthority, peerRecoveryPlansMatchAuthority,
    localRecoveryPlanMatchesAuthority, knownPeerImages, actingReplicaImages]
    using h

theorem imageInvariant_transitionTo
    (snap : Snapshot) (newState : State) (reason : String) :
    ImageInvariant snap → ImageInvariant (transitionTo snap newState reason).1 := by
  intro h
  unfold transitionTo
  by_cases hEq : snap.state = newState
  · simp [hEq, h]
  · simpa [hEq, ImageInvariant, authSourcesBackedByKnownPeers, authImageMatchesKnownPeers,
      authSeqMatchesKnownPeers, authSourcesMatchKnownPeers, localWithinAuthority,
      actingReplicaWithinAuthority, peerRecoveryPlansMatchAuthority,
      localRecoveryPlanMatchesAuthority, knownPeerImages, actingReplicaImages] using h

theorem imageInvariant_update_epochActingUpPool_sameOsds
    (snap : Snapshot)
    (epoch : Epoch) (acting up : ActingSet)
    (poolSize poolMinSize : Nat)
    (hActing : acting.osds = snap.acting.osds) :
    ImageInvariant snap →
      ImageInvariant {
        snap with
          epoch := epoch
          acting := acting
          up := up
          poolSize := poolSize
          poolMinSize := poolMinSize
      } := by
  intro h
  simpa [ImageInvariant, authSourcesBackedByKnownPeers, authImageMatchesKnownPeers,
    authSeqMatchesKnownPeers, authSourcesMatchKnownPeers, localWithinAuthority,
    actingReplicaWithinAuthority, peerRecoveryPlansMatchAuthority,
    localRecoveryPlanMatchesAuthority, knownPeerImages, actingReplicaImages, hActing]
    using h

private theorem imageInvariant_sendQueries_fold
    (probes : List OsdId) (snap : Snapshot) (fx : List PeeringEffect)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant
      ((probes.foldl
        (fun (accSnap, accFx) osd =>
          if osd ∈ accSnap.peersResponded || osd ∈ accSnap.peersQueried then
            (accSnap, accFx)
          else
            ({ accSnap with peersQueried := osdSetInsert accSnap.peersQueried osd },
             accFx ++ [.sendQuery { target := osd, pgid := accSnap.pgid, epoch := accSnap.epoch }]))
        (snap, fx)).1) := by
  induction probes generalizing snap fx with
  | nil =>
      simpa using hInvariant
  | cons osd probes ih =>
      by_cases hSeen : osd ∈ snap.peersResponded || osd ∈ snap.peersQueried
      · simpa [List.foldl, hSeen] using ih snap fx hInvariant
      · have hInvariant' :
            ImageInvariant { snap with peersQueried := osdSetInsert snap.peersQueried osd } :=
          imageInvariant_update_query_bookkeeping snap (osdSetInsert snap.peersQueried osd)
            hInvariant
        simpa [List.foldl, hSeen] using
          ih
            { snap with peersQueried := osdSetInsert snap.peersQueried osd }
            (fx ++ [.sendQuery { target := osd, pgid := snap.pgid, epoch := snap.epoch }])
            hInvariant'

theorem imageInvariant_sendQueries
    (snap : Snapshot)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (sendQueries snap).1 := by
  unfold sendQueries
  simpa using imageInvariant_sendQueries_fold (buildProbeSet snap) snap [] hInvariant

theorem imageInvariant_prepareChooseActing (snap : Snapshot) :
    ImageInvariant (prepareChooseActing snap) := by
  unfold prepareChooseActing
  exact imageInvariant_refreshImageStateFromKnownPeers
    { snap with
      localInfo := normalizedPGInfo snap.localInfo
      peerInfo := normalizePeerInfoMap snap.peerInfo }

theorem authSeq_eq_authoritativeCommittedSeq_prepareChooseActing
    (snap : Snapshot) :
    (prepareChooseActing snap).authSeq =
      authoritativeCommittedSeq (knownPeerImages (prepareChooseActing snap)) := by
  unfold prepareChooseActing
  exact authSeq_eq_authoritativeCommittedSeq_refreshImageStateFromKnownPeers
    { snap with
      localInfo := normalizedPGInfo snap.localInfo
      peerInfo := normalizePeerInfoMap snap.peerInfo }

theorem authSources_eq_authoritativeSources_prepareChooseActing
    (snap : Snapshot) :
    (prepareChooseActing snap).authSources =
      authoritativeSources (knownPeerImages (prepareChooseActing snap)) := by
  unfold prepareChooseActing
  exact authSources_eq_authoritativeSources_refreshImageStateFromKnownPeers
    { snap with
      localInfo := normalizedPGInfo snap.localInfo
      peerInfo := normalizePeerInfoMap snap.peerInfo }

theorem authImage_eq_authorityImageValues_prepareChooseActing
    (snap : Snapshot) :
    (prepareChooseActing snap).authImage =
      authorityImageValues (authoritativeSources (knownPeerImages (prepareChooseActing snap))) := by
  unfold prepareChooseActing
  exact authImage_eq_authorityImageValues_refreshImageStateFromKnownPeers
    { snap with
      localInfo := normalizedPGInfo snap.localInfo
      peerInfo := normalizePeerInfoMap snap.peerInfo }

theorem imageInvariant_tryActivate_pendingActingChange
    (snap : Snapshot) (hInvariant : ImageInvariant snap)
    (hPending : snap.pendingActingChange = true) :
    ImageInvariant (tryActivate snap).1 := by
  simp [tryActivate, hPending, hInvariant]

theorem imageInvariant_tryActivate_minSizeFailed
    (snap : Snapshot)
    (hInvariant : ImageInvariant snap)
    (hPending : snap.pendingActingChange = false)
    (hAvailLt : tryActivateAvailable snap < snap.poolMinSize) :
    ImageInvariant (tryActivate snap).1 := by
  simp [tryActivate, hPending, hAvailLt]
  exact imageInvariant_transitionTo snap .down "min_size check failed at activation" hInvariant

theorem imageInvariant_tryActivate_success
    (snap : Snapshot)
    (hPending : snap.pendingActingChange = false)
    (hAvailGe : ¬ tryActivateAvailable snap < snap.poolMinSize) :
    ImageInvariant (tryActivate snap).1 := by
  have hPrepared : ImageInvariant (tryActivatePreparedSnap snap) := by
    unfold tryActivatePreparedSnap
    exact imageInvariant_refreshImageStateFromKnownPeers
      { snap with localInfo := tryActivateLocalInfo snap }
  have hActive : ImageInvariant (transitionTo (tryActivatePreparedSnap snap) .active "peering complete").1 :=
    imageInvariant_transitionTo
      (tryActivatePreparedSnap snap)
      .active
      "peering complete"
      hPrepared
  by_cases hRecoveryEmpty : (tryActivateRecoveryTargets snap).isEmpty
  · simp [tryActivate, hPending, hAvailGe, hRecoveryEmpty]
    exact imageInvariant_transitionTo
      (transitionTo (tryActivatePreparedSnap snap) .active "peering complete").1
      .clean
      "all replicas up to date"
      hActive
  · simp [tryActivate, hPending, hAvailGe, hRecoveryEmpty]
    exact imageInvariant_transitionTo
      (transitionTo (tryActivatePreparedSnap snap) .active "peering complete").1
      .recovering
      "replicas need recovery"
      hActive

theorem imageInvariant_tryActivate
    (snap : Snapshot)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (tryActivate snap).1 := by
  cases hPending : snap.pendingActingChange with
  | true =>
      exact imageInvariant_tryActivate_pendingActingChange snap hInvariant hPending
  | false =>
      by_cases hAvailLt : tryActivateAvailable snap < snap.poolMinSize
      · exact imageInvariant_tryActivate_minSizeFailed snap hInvariant hPending hAvailLt
      · exact imageInvariant_tryActivate_success snap hPending hAvailLt

theorem effectivePGImage_tryActivateLocalInfo_clamped
    (snap : Snapshot)
    (hClamp :
      (decide (snap.localInfo.committedSeq >= snap.authSeq) &&
        prefixImage? snap.authImage (effectivePGImage snap.localInfo)) = true) :
    effectivePGImage (tryActivateLocalInfo snap) = snap.authImage := by
  unfold tryActivateLocalInfo tryActivateClampLocalToAuth
  simp [hClamp]
  by_cases hEmpty : snap.authImage.entries = []
  · have hLen : primaryLength snap.authImage = 0 := by
      simp [primaryLength, lookupLength, lookupLengthEntries, hEmpty]
    simp [effectivePGImage, hEmpty, hLen]
  · simp [effectivePGImage, hEmpty]

theorem localWithinAuthority_tryActivateLocalInfo
    (snap : Snapshot) (hLocal : localWithinAuthority snap) :
    localWithinAuthority { snap with localInfo := tryActivateLocalInfo snap } := by
  rcases hLocal with ⟨hSeq, hPrefix⟩
  unfold tryActivateLocalInfo tryActivateClampLocalToAuth
  by_cases hClamp :
      snap.localInfo.committedSeq >= snap.authSeq &&
        prefixImage? snap.authImage (effectivePGImage snap.localInfo)
  · constructor
    · simp [hClamp]
    · intro obj
      have hClampProp :
          snap.authSeq ≤ snap.localInfo.committedSeq ∧
            prefixImage? snap.authImage (effectivePGImage snap.localInfo) = true := by
        simpa using hClamp
      have hEq := effectivePGImage_tryActivateLocalInfo_clamped snap (by simpa using hClamp)
      have hEq' :
          effectivePGImage
            { pgid := snap.localInfo.pgid
              committedSeq := snap.authSeq
              committedLength := primaryLength snap.authImage
              image := snap.authImage
              lastEpochStarted := snap.epoch
              lastIntervalStarted := snap.epoch
              lastEpochClean := snap.localInfo.lastEpochClean
              epochCreated := snap.localInfo.epochCreated
              sameIntervalSince := snap.localInfo.sameIntervalSince
              sameUpSince := snap.localInfo.sameUpSince
              samePrimarySince := snap.localInfo.samePrimarySince } = snap.authImage := by
        simpa [tryActivateLocalInfo, tryActivateClampLocalToAuth, hClampProp] using hEq
      simp [hClampProp, hEq']
  · constructor
    · simpa [hClamp] using hSeq
    · intro obj
      simp [hClamp]
      exact hPrefix obj

theorem sameImage_tryActivateLocalInfo
    (snap : Snapshot) (hLocal : localWithinAuthority snap) :
    sameImage (effectivePGImage (tryActivateLocalInfo snap)) (effectivePGImage snap.localInfo) := by
  rcases hLocal with ⟨hSeq, hPrefix⟩
  cases hClamp : tryActivateClampLocalToAuth snap with
  | false =>
      have hEq :
          effectivePGImage (tryActivateLocalInfo snap) = effectivePGImage snap.localInfo := by
        simp [tryActivateLocalInfo, hClamp, effectivePGImage]
      simpa [hEq] using sameImage_refl (effectivePGImage snap.localInfo)
  | true =>
      have hClampEq :
          (decide (snap.localInfo.committedSeq >= snap.authSeq) &&
            prefixImage? snap.authImage (effectivePGImage snap.localInfo)) = true := by
        simpa [tryActivateClampLocalToAuth] using hClamp
      have hClampParts :
          decide (snap.localInfo.committedSeq >= snap.authSeq) = true ∧
            prefixImage? snap.authImage (effectivePGImage snap.localInfo) = true := by
        have hClampEq' := hClampEq
        rw [Bool.and_eq_true] at hClampEq'
        exact hClampEq'
      have hClampPrefix : prefixImage snap.authImage (effectivePGImage snap.localInfo) := by
        exact prefixImage_of_prefixImage? _ _ hClampParts.2
      have hEq :
          effectivePGImage (tryActivateLocalInfo snap) = snap.authImage := by
        exact effectivePGImage_tryActivateLocalInfo_clamped snap hClampEq
      constructor
      · intro obj
        simpa [hEq] using hClampPrefix obj
      · intro obj
        simpa [hEq] using hPrefix obj

theorem committedSeq_tryActivateLocalInfo
    (snap : Snapshot) (hLocal : localWithinAuthority snap) :
    (normalizedPGInfo (tryActivateLocalInfo snap)).committedSeq =
      (normalizedPGInfo snap.localInfo).committedSeq := by
  rcases hLocal with ⟨hSeq, _hPrefix⟩
  cases hClamp : tryActivateClampLocalToAuth snap with
  | false =>
      simp [tryActivateLocalInfo, hClamp, normalizedPGInfo]
  | true =>
      have hClampEq :
          (decide (snap.localInfo.committedSeq >= snap.authSeq) &&
            prefixImage? snap.authImage (effectivePGImage snap.localInfo)) = true := by
        simpa [tryActivateClampLocalToAuth] using hClamp
      have hClampParts :
          decide (snap.localInfo.committedSeq >= snap.authSeq) = true ∧
            prefixImage? snap.authImage (effectivePGImage snap.localInfo) = true := by
        have hClampEq' := hClampEq
        rw [Bool.and_eq_true] at hClampEq'
        exact hClampEq'
      have hGe : snap.authSeq ≤ snap.localInfo.committedSeq := by
        have hGe' := hClampParts.1
        rwa [decide_eq_true_eq] at hGe'
      have hEqSeq : snap.localInfo.committedSeq = snap.authSeq := Nat.le_antisymm hSeq hGe
      simp [tryActivateLocalInfo, hClamp, normalizedPGInfo, hEqSeq]

theorem authoritativeCommittedSeq_knownPeerImages_update_localInfo
    (snap : Snapshot) (localInfo : PGInfo)
    (hSeq :
      (normalizedPGInfo localInfo).committedSeq =
        (normalizedPGInfo snap.localInfo).committedSeq) :
    authoritativeCommittedSeq (knownPeerImages { snap with localInfo := localInfo }) =
      authoritativeCommittedSeq (knownPeerImages snap) := by
  simp [knownPeerImages, hSeq, authoritativeCommittedSeq]

theorem imageInvariant_tryActivatePreparedSnap
    (snap : Snapshot) :
    ImageInvariant (tryActivatePreparedSnap snap) := by
  unfold tryActivatePreparedSnap
  exact imageInvariant_refreshImageStateFromKnownPeers
    { snap with localInfo := tryActivateLocalInfo snap }

theorem localWithinAuthority_tryActivatePreparedSnap
    (snap : Snapshot) :
    localWithinAuthority (tryActivatePreparedSnap snap) := by
  exact (imageInvariant_tryActivatePreparedSnap snap).2.2.2.2.1

theorem authSeq_eq_authoritativeCommittedSeq_tryActivatePreparedSnap
    (snap : Snapshot) :
    (tryActivatePreparedSnap snap).authSeq =
      authoritativeCommittedSeq (knownPeerImages (tryActivatePreparedSnap snap)) := by
  unfold tryActivatePreparedSnap
  exact authSeq_eq_authoritativeCommittedSeq_refreshImageStateFromKnownPeers
    { snap with localInfo := tryActivateLocalInfo snap }

theorem authSources_eq_authoritativeSources_tryActivatePreparedSnap
    (snap : Snapshot) :
    (tryActivatePreparedSnap snap).authSources =
      authoritativeSources (knownPeerImages (tryActivatePreparedSnap snap)) := by
  unfold tryActivatePreparedSnap
  exact authSources_eq_authoritativeSources_refreshImageStateFromKnownPeers
    { snap with localInfo := tryActivateLocalInfo snap }

theorem authImage_eq_authorityImageValues_tryActivatePreparedSnap
    (snap : Snapshot) :
    (tryActivatePreparedSnap snap).authImage =
      authorityImageValues (authoritativeSources (knownPeerImages (tryActivatePreparedSnap snap))) := by
  unfold tryActivatePreparedSnap
  exact authImage_eq_authorityImageValues_refreshImageStateFromKnownPeers
    { snap with localInfo := tryActivateLocalInfo snap }

theorem imageInvariant_chooseActing_priorTimedOut
    (snap : Snapshot)
    (hPriorTimedOut :
      let snap' := prepareChooseActing snap
      chooseActingPriorTimedOut snap' = true) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages (prepareChooseActing snap) ≠ [] := by
    exact knownPeerImages_ne_nil (prepareChooseActing snap)
  simp [chooseActing, hPriorTimedOut, hKnown]
  exact imageInvariant_transitionTo snap' .down "prior-interval probe timed out" hInvariant

theorem imageInvariant_chooseActing_noPeersAvailable
    (snap : Snapshot)
    (hPriorTimedOut :
      let snap' := prepareChooseActing snap
      chooseActingPriorTimedOut snap' = false)
    (hPoolMin :
      let snap' := prepareChooseActing snap
      0 < snap'.poolMinSize)
    (hAvailZero :
      let snap' := prepareChooseActing snap
      chooseActingAvailable snap' = 0) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages (prepareChooseActing snap) ≠ [] := by
    exact knownPeerImages_ne_nil (prepareChooseActing snap)
  simp [chooseActing, hPriorTimedOut, hKnown, hPoolMin, hAvailZero]
  exact imageInvariant_transitionTo snap' .incomplete "no peers available" hInvariant

theorem imageInvariant_chooseActing_insufficientPeers
    (snap : Snapshot)
    (hPriorTimedOut :
      let snap' := prepareChooseActing snap
      chooseActingPriorTimedOut snap' = false)
    (hAvailLt :
      let snap' := prepareChooseActing snap
      chooseActingAvailable snap' < snap'.poolMinSize)
    (hAvailNonZero :
      let snap' := prepareChooseActing snap
      chooseActingAvailable snap' ≠ 0) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages (prepareChooseActing snap) ≠ [] := by
    exact knownPeerImages_ne_nil (prepareChooseActing snap)
  simp [chooseActing, hPriorTimedOut, hKnown, hAvailLt, hAvailNonZero]
  exact imageInvariant_transitionTo snap' .down "insufficient peers for min_size" hInvariant

theorem imageInvariant_chooseActing_needActingChange
    (snap : Snapshot)
    (hPriorTimedOut :
      let snap' := prepareChooseActing snap
      chooseActingPriorTimedOut snap' = false)
    (hAvailGe :
      let snap' := prepareChooseActing snap
      ¬ chooseActingAvailable snap' < snap'.poolMinSize)
    (hNeedActingChange :
      let snap' := prepareChooseActing snap
      chooseActingNeedActingChange snap' = true) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages (prepareChooseActing snap) ≠ [] := by
    exact knownPeerImages_ne_nil (prepareChooseActing snap)
  simp [chooseActing, hPriorTimedOut, hKnown, hAvailGe, hNeedActingChange]
  exact imageInvariant_update_controlFlags snap' true snap'.needUpThru snap'.activated hInvariant

theorem imageInvariant_chooseActing_waitUpThru
    (snap : Snapshot)
    (hPriorTimedOut :
      let snap' := prepareChooseActing snap
      chooseActingPriorTimedOut snap' = false)
    (hAvailGe :
      let snap' := prepareChooseActing snap
      ¬ chooseActingAvailable snap' < snap'.poolMinSize)
    (hNoActingChange :
      let snap' := prepareChooseActing snap
      chooseActingNeedActingChange snap' = false)
    (hNeedUpThru :
      let snap' := prepareChooseActing snap
      snap'.localInfo.lastIntervalStarted < snap'.epoch) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  let gated : Snapshot := { snap' with pendingActingChange := false, needUpThru := true }
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages (prepareChooseActing snap) ≠ [] := by
    exact knownPeerImages_ne_nil (prepareChooseActing snap)
  have hGated : ImageInvariant gated := by
    exact imageInvariant_update_controlFlags snap' false true snap'.activated hInvariant
  simp [chooseActing, hPriorTimedOut, hKnown, hAvailGe, hNoActingChange, hNeedUpThru]
  exact imageInvariant_transitionTo gated .waitUpThru "need up_thru" hGated

theorem imageInvariant_chooseActing
    (snap : Snapshot) :
    ImageInvariant (chooseActing snap).1 := by
  let snap' := prepareChooseActing snap
  have hInvariant : ImageInvariant snap' := imageInvariant_prepareChooseActing snap
  have hKnown : knownPeerImages snap' ≠ [] := knownPeerImages_ne_nil snap'
  cases hPriorTimedOut : chooseActingPriorTimedOut snap' with
  | true =>
      simpa [snap'] using imageInvariant_chooseActing_priorTimedOut snap hPriorTimedOut
  | false =>
      by_cases hAvailLt : chooseActingAvailable snap' < snap'.poolMinSize
      · by_cases hAvailZero : chooseActingAvailable snap' = 0
        · have hPoolMin : 0 < snap'.poolMinSize := by
            simpa [hAvailZero] using hAvailLt
          simpa [snap'] using
            imageInvariant_chooseActing_noPeersAvailable snap hPriorTimedOut hPoolMin hAvailZero
        · simpa [snap'] using
            imageInvariant_chooseActing_insufficientPeers snap hPriorTimedOut hAvailLt hAvailZero
      · cases hNeedActingChange : chooseActingNeedActingChange snap' with
        | true =>
            simpa [snap'] using
              imageInvariant_chooseActing_needActingChange
                snap hPriorTimedOut hAvailLt hNeedActingChange
        | false =>
            by_cases hNeedUpThru : snap'.localInfo.lastIntervalStarted < snap'.epoch
            · simpa [snap'] using
                imageInvariant_chooseActing_waitUpThru
                  snap hPriorTimedOut hAvailLt hNeedActingChange hNeedUpThru
            · have hReady : ImageInvariant
                  { snap' with pendingActingChange := false } := by
                exact imageInvariant_update_controlFlags
                  snap'
                  false
                  snap'.needUpThru
                  snap'.activated
                  hInvariant
              simpa [snap', chooseActing, hKnown, hPriorTimedOut, hAvailLt,
                hNeedActingChange, hNeedUpThru] using
                imageInvariant_tryActivate { snap' with pendingActingChange := false } hReady

theorem imageInvariant_startPeeringPrimaryRefreshedSnap
    (snap : Snapshot) (priorOsds : List OsdId) :
    ImageInvariant (startPeeringPrimaryRefreshedSnap snap priorOsds) := by
  unfold startPeeringPrimaryRefreshedSnap
  exact imageInvariant_refreshImageStateFromKnownPeers {
    (startPeeringPrimaryEntered snap priorOsds).1 with
      peerInfo := insertPeerInfo
        (startPeeringPrimaryEntered snap priorOsds).1.peerInfo
        (startPeeringPrimaryEntered snap priorOsds).1.whoami
        (startPeeringPrimarySelfInfo snap priorOsds)
      peersResponded := osdSetInsert
        (startPeeringPrimaryEntered snap priorOsds).1.peersResponded
        (startPeeringPrimaryEntered snap priorOsds).1.whoami
  }

theorem imageInvariant_startPeeringPrimaryQueried
    (snap : Snapshot) (priorOsds : List OsdId) :
    ImageInvariant (startPeeringPrimaryQueried snap priorOsds).1 := by
  unfold startPeeringPrimaryQueried
  simpa using imageInvariant_sendQueries
    (startPeeringPrimaryRefreshedSnap snap priorOsds)
    (imageInvariant_startPeeringPrimaryRefreshedSnap snap priorOsds)

theorem imageInvariant_startPeeringPrimary
    (snap : Snapshot) (priorOsds : List OsdId) :
    ImageInvariant (startPeeringPrimary snap priorOsds).1 := by
  have hQueried : ImageInvariant (startPeeringPrimaryQueried snap priorOsds).1 :=
    imageInvariant_startPeeringPrimaryQueried snap priorOsds
  cases hEnough : haveEnoughInfo (startPeeringPrimaryQueried snap priorOsds).1 with
  | false =>
      have hResult :
          (startPeeringPrimary snap priorOsds).1 =
            (startPeeringPrimaryQueried snap priorOsds).1 := by
        unfold startPeeringPrimary
        simp [hEnough]
      rw [hResult]
      exact hQueried
  | true =>
      have hResult :
          (startPeeringPrimary snap priorOsds).1 =
            (chooseActing (startPeeringPrimaryQueried snap priorOsds).1).1 := by
        unfold startPeeringPrimary
        simp [hEnough]
      rw [hResult]
      exact imageInvariant_chooseActing ((startPeeringPrimaryQueried snap priorOsds).1)

theorem imageInvariant_onPeerQueryTimeout_ignored
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap)
    (hState : snap.state ≠ .getPeerInfo) :
    ImageInvariant (onPeerQueryTimeout snap e).1 := by
  simp [onPeerQueryTimeout, hState, hInvariant]

theorem imageInvariant_onPeerQueryTimeout_keepWaiting
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap)
    (hState : snap.state = .getPeerInfo)
    (hEnough : peerQueryTimeoutEnoughInfo snap e.peer = false) :
    ImageInvariant (onPeerQueryTimeout snap e).1 := by
  simp [onPeerQueryTimeout, hState, hEnough]
  exact imageInvariant_update_probe_bookkeeping snap
    (osdSetInsert snap.peersResponded e.peer)
    (osdSetInsert snap.timedOutProbes e.peer)
    hInvariant

theorem imageInvariant_onPeerQueryTimeout_chooseActing_priorTimedOut
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hState : snap.state = .getPeerInfo)
    (hEnough : peerQueryTimeoutEnoughInfo snap e.peer = true)
    (hPriorTimedOut :
      let snap' := prepareChooseActing {
        snap with
          peersResponded := osdSetInsert snap.peersResponded e.peer
          timedOutProbes := osdSetInsert snap.timedOutProbes e.peer
      }
      chooseActingPriorTimedOut snap' = true) :
    ImageInvariant (onPeerQueryTimeout snap e).1 := by
  simp [onPeerQueryTimeout, hState, hEnough]
  simpa [hState] using imageInvariant_chooseActing_priorTimedOut
    { snap with
      peersResponded := osdSetInsert snap.peersResponded e.peer
      timedOutProbes := osdSetInsert snap.timedOutProbes e.peer
    }
    hPriorTimedOut

theorem imageInvariant_onPeerQueryTimeout_chooseActing
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hState : snap.state = .getPeerInfo)
    (hEnough : peerQueryTimeoutEnoughInfo snap e.peer = true) :
    ImageInvariant (onPeerQueryTimeout snap e).1 := by
  simp [onPeerQueryTimeout, hState, hEnough]
  simpa [hState] using imageInvariant_chooseActing
    { snap with
      peersResponded := osdSetInsert snap.peersResponded e.peer
      timedOutProbes := osdSetInsert snap.timedOutProbes e.peer
    }

theorem imageInvariant_onPeerQueryTimeout
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (onPeerQueryTimeout snap e).1 := by
  cases hState : snap.state with
  | getPeerInfo =>
      cases hEnough : peerQueryTimeoutEnoughInfo snap e.peer with
      | true =>
          exact imageInvariant_onPeerQueryTimeout_chooseActing snap e hState hEnough
      | false =>
          exact imageInvariant_onPeerQueryTimeout_keepWaiting snap e hInvariant hState hEnough
  | initial =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | reset =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | waitUpThru =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | active =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | recovering =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | clean =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | stray =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | replicaActive =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | down =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | incomplete =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])
  | deleting =>
      exact imageInvariant_onPeerQueryTimeout_ignored snap e hInvariant (by simp [hState])

theorem imageInvariant_onPeerInfoReceived_ignored_disallowed
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = false) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  simp [onPeerInfoReceived, hAllowed, hInvariant]

theorem imageInvariant_onPeerInfoReceived_ignored_stale
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hStale : e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  simp [onPeerInfoReceived, hAllowed, hStale, hInvariant]

theorem imageInvariant_peerInfoReceivedRefreshedSnap
    (snap : Snapshot) (e : Event.PeerInfoReceived) :
    ImageInvariant (peerInfoReceivedRefreshedSnap snap e) := by
  unfold peerInfoReceivedRefreshedSnap peerInfoReceivedInfo
  exact imageInvariant_refreshImageStateFromKnownPeers {
    snap with
      peerInfo := insertPeerInfo snap.peerInfo e.sender
        (normalizedPeerInfo { e.info with osd := e.sender })
      peersResponded := osdSetInsert snap.peersResponded e.sender
  }

theorem imageInvariant_onPeerInfoReceived_keepWaiting_of_refreshedInvariant
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) = false)
    (hState : (peerInfoReceivedRefreshedSnap snap e).state = .getPeerInfo)
    (hEnough : peerInfoReceivedEnoughInfo (peerInfoReceivedRefreshedSnap snap e) e.sender = false)
    (hInvariant : ImageInvariant (peerInfoReceivedRefreshedSnap snap e)) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  have hResult : (onPeerInfoReceived snap e).1 = peerInfoReceivedRefreshedSnap snap e := by
    unfold onPeerInfoReceived
    simp [hAllowed, hFresh, hState, hEnough]
  rw [hResult]
  exact hInvariant

theorem imageInvariant_onPeerInfoReceived_keepWaiting
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) = false)
    (hState : (peerInfoReceivedRefreshedSnap snap e).state = .getPeerInfo)
    (hEnough : peerInfoReceivedEnoughInfo (peerInfoReceivedRefreshedSnap snap e) e.sender = false) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  apply imageInvariant_onPeerInfoReceived_keepWaiting_of_refreshedInvariant
  · exact hAllowed
  · exact hFresh
  · exact hState
  · exact hEnough
  · exact imageInvariant_peerInfoReceivedRefreshedSnap snap e

theorem imageInvariant_onPeerInfoReceived_chooseActing
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) = false)
    (hState :
      (peerInfoReceivedRefreshedSnap snap e).state = .down ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .incomplete ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .waitUpThru) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  have hState' :
      ((peerInfoReceivedRefreshedSnap snap e).state = .down ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .incomplete) ∨
          (peerInfoReceivedRefreshedSnap snap e).state = .waitUpThru := by
    simpa [or_assoc] using hState
  have hResult :
      (onPeerInfoReceived snap e).1 =
        (chooseActing (peerInfoReceivedRefreshedSnap snap e)).1 := by
    unfold onPeerInfoReceived
    simp [hAllowed, hFresh, hState']
  rw [hResult]
  exact imageInvariant_chooseActing (peerInfoReceivedRefreshedSnap snap e)

theorem imageInvariant_onPeerInfoReceived_chooseActing_getPeerInfo
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) = false)
    (hState : (peerInfoReceivedRefreshedSnap snap e).state = .getPeerInfo)
    (hEnough : peerInfoReceivedEnoughInfo (peerInfoReceivedRefreshedSnap snap e) e.sender = true) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  have hResult :
      (onPeerInfoReceived snap e).1 =
        (chooseActing (peerInfoReceivedRefreshedSnap snap e)).1 := by
    unfold onPeerInfoReceived
    simp [hAllowed, hFresh, hState, hEnough]
  rw [hResult]
  exact imageInvariant_chooseActing (peerInfoReceivedRefreshedSnap snap e)

theorem imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hAllowed : peerInfoReceivedAllowed snap e.sender = true)
    (hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) = false)
    (hNoChoose :
      ¬ ((peerInfoReceivedRefreshedSnap snap e).state = .down ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .incomplete ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .waitUpThru))
    (hNotGet : (peerInfoReceivedRefreshedSnap snap e).state ≠ .getPeerInfo)
    (hInvariant : ImageInvariant (peerInfoReceivedRefreshedSnap snap e)) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  have hNoChoose' :
      ¬ (((peerInfoReceivedRefreshedSnap snap e).state = .down ∨
        (peerInfoReceivedRefreshedSnap snap e).state = .incomplete) ∨
          (peerInfoReceivedRefreshedSnap snap e).state = .waitUpThru) := by
    simpa [or_assoc] using hNoChoose
  have hResult : (onPeerInfoReceived snap e).1 = peerInfoReceivedRefreshedSnap snap e := by
    unfold onPeerInfoReceived
    simp [hAllowed, hFresh, hNoChoose', hNotGet]
  rw [hResult]
  exact hInvariant

theorem imageInvariant_onPeerInfoReceived
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (onPeerInfoReceived snap e).1 := by
  cases hAllowed : peerInfoReceivedAllowed snap e.sender with
  | false =>
      exact imageInvariant_onPeerInfoReceived_ignored_disallowed snap e hInvariant hAllowed
  | true =>
      cases hFresh : (e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset) with
      | true =>
          have hStale : e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset := by
            simpa using hFresh
          exact imageInvariant_onPeerInfoReceived_ignored_stale snap e hInvariant hAllowed hStale
      | false =>
          have hRefreshed : ImageInvariant (peerInfoReceivedRefreshedSnap snap e) :=
            imageInvariant_peerInfoReceivedRefreshedSnap snap e
          cases hState : (peerInfoReceivedRefreshedSnap snap e).state with
          | down =>
              exact imageInvariant_onPeerInfoReceived_chooseActing snap e hAllowed hFresh
                (by simp [hState])
          | incomplete =>
              exact imageInvariant_onPeerInfoReceived_chooseActing snap e hAllowed hFresh
                (by simp [hState])
          | waitUpThru =>
              exact imageInvariant_onPeerInfoReceived_chooseActing snap e hAllowed hFresh
                (by simp [hState])
          | getPeerInfo =>
              cases hEnough : peerInfoReceivedEnoughInfo (peerInfoReceivedRefreshedSnap snap e) e.sender with
              | true =>
                  exact imageInvariant_onPeerInfoReceived_chooseActing_getPeerInfo
                    snap e hAllowed hFresh (by simp [hState]) (by simp [hEnough])
              | false =>
                  exact imageInvariant_onPeerInfoReceived_keepWaiting
                    snap e hAllowed hFresh (by simp [hState]) (by simp [hEnough])
          | initial =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | reset =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | active =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | recovering =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | clean =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | stray =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | replicaActive =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed
          | deleting =>
              exact imageInvariant_onPeerInfoReceived_ignored_of_refreshedInvariant
                snap e hAllowed hFresh (by simp [hState]) (by simp [hState]) hRefreshed

theorem imageInvariant_onAdvanceMap
    (snap : Snapshot) (e : Event.AdvanceMap)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (onAdvanceMap snap e).1 := by
  cases hNewInterval : advanceMapNewInterval snap e with
  | true =>
      have hRestartRefreshed :
          ImageInvariant (refreshImageStateFromKnownPeers (advanceMapRestartBase snap e)) := by
        exact imageInvariant_refreshImageStateFromKnownPeers (advanceMapRestartBase snap e)
      cases hNextPrimary : advanceMapNextIsPrimary snap e with
      | true =>
          have hResult :
              (onAdvanceMap snap e).1 =
                (startPeeringPrimary (advanceMapRestartBase snap e) e.priorOsds).1 := by
            unfold onAdvanceMap
            simp [hNewInterval, hNextPrimary,
              advanceMapIntervalBase, advanceMapPoolBase, advanceMapRestartBase]
          rw [hResult]
          exact imageInvariant_startPeeringPrimary (advanceMapRestartBase snap e) e.priorOsds
      | false =>
          cases hContains : advanceMapNextContainsSelf snap e with
          | true =>
              have hResult :
                  (onAdvanceMap snap e).1 =
                    (transitionTo
                      (refreshImageStateFromKnownPeers (advanceMapRestartBase snap e))
                      .stray
                      "new interval, replica").1 := by
                unfold onAdvanceMap
                simp [hNewInterval, hNextPrimary, hContains,
                  advanceMapIntervalBase, advanceMapPoolBase, advanceMapRestartBase]
              rw [hResult]
              exact imageInvariant_transitionTo
                (refreshImageStateFromKnownPeers (advanceMapRestartBase snap e))
                .stray
                "new interval, replica"
                hRestartRefreshed
          | false =>
              have hResult :
                  (onAdvanceMap snap e).1 =
                    (transitionTo
                      (refreshImageStateFromKnownPeers (advanceMapRestartBase snap e))
                      .stray
                      "new interval, stray").1 := by
                unfold onAdvanceMap
                simp [hNewInterval, hNextPrimary, hContains,
                  advanceMapIntervalBase, advanceMapPoolBase, advanceMapRestartBase]
              rw [hResult]
              exact imageInvariant_transitionTo
                (refreshImageStateFromKnownPeers (advanceMapRestartBase snap e))
                .stray
                "new interval, stray"
                hRestartRefreshed
  | false =>
      have hSame : e.newActing.osds = snap.acting.osds ∧ e.newUp.osds = snap.up.osds := by
        unfold advanceMapNewInterval at hNewInterval
        simp at hNewInterval
        exact hNewInterval
      have hIntervalBase : ImageInvariant (advanceMapIntervalBase snap e) := by
        unfold advanceMapIntervalBase
        simpa using
          imageInvariant_update_epochActingUpPool_sameOsds
            snap e.newEpoch e.newActing e.newUp snap.poolSize snap.poolMinSize
            hSame.1 hInvariant
      have hPoolBase : ImageInvariant (advanceMapPoolBase snap e) := by
        unfold advanceMapPoolBase advanceMapIntervalBase
        exact imageInvariant_update_epochActingUpPool_sameOsds
          snap e.newEpoch e.newActing e.newUp e.newPoolSize e.newPoolMinSize
          hSame.1 hInvariant
      cases hPoolChanged : advanceMapPoolParamsChanged snap e with
      | false =>
          cases hRetry : advanceMapRetryChooseActing snap e with
          | true =>
              have hResult :
                  (onAdvanceMap snap e).1 =
                    (chooseActing (advanceMapIntervalBase snap e)).1 := by
                unfold onAdvanceMap
                rw [hNewInterval, hPoolChanged, hRetry]
                simp [advanceMapIntervalBase]
              rw [hResult]
              exact imageInvariant_chooseActing (advanceMapIntervalBase snap e)
          | false =>
              have hResult :
                  (onAdvanceMap snap e).1 = advanceMapIntervalBase snap e := by
                unfold onAdvanceMap
                rw [hNewInterval, hPoolChanged, hRetry]
                simp [advanceMapIntervalBase]
              rw [hResult]
              exact hIntervalBase
      | true =>
          cases hPrimaryActive : advanceMapPoolChangePrimaryActive snap e with
          | false =>
              cases hRetryDown : advanceMapPoolChangeRetryChoose snap e with
              | true =>
                  have hResult :
                      (onAdvanceMap snap e).1 =
                        (chooseActing (advanceMapPoolBase snap e)).1 := by
                    unfold onAdvanceMap
                    rw [hNewInterval, hPoolChanged, hPrimaryActive, hRetryDown]
                    simp [advanceMapIntervalBase, advanceMapPoolBase]
                  rw [hResult]
                  exact imageInvariant_chooseActing (advanceMapPoolBase snap e)
              | false =>
                  have hResult :
                      (onAdvanceMap snap e).1 = advanceMapPoolBase snap e := by
                    unfold onAdvanceMap
                    rw [hNewInterval, hPoolChanged, hPrimaryActive, hRetryDown]
                    simp [advanceMapIntervalBase, advanceMapPoolBase]
                  rw [hResult]
                  exact hPoolBase
          | true =>
              cases hAvail : advanceMapPoolChangeBelowMinSize snap e with
              | true =>
                  have hDown :
                    ImageInvariant
                      (transitionTo
                        (advanceMapPoolBase snap e)
                        .down
                        "min_size increased, insufficient peers").1 := by
                    exact imageInvariant_transitionTo
                      (advanceMapPoolBase snap e)
                      .down
                      "min_size increased, insufficient peers"
                      hPoolBase
                  cases hRetryChoose : advanceMapMinSizeDecreased snap e with
                  | true =>
                      have hResult :
                      (onAdvanceMap snap e).1 =
                        (chooseActing
                          (transitionTo
                            (advanceMapPoolBase snap e)
                            .down
                            "min_size increased, insufficient peers").1).1 := by
                        unfold onAdvanceMap
                        rw [hNewInterval, hPoolChanged, hPrimaryActive, hAvail, hRetryChoose]
                        simp [advanceMapIntervalBase, advanceMapPoolBase]
                      rw [hResult]
                      exact imageInvariant_chooseActing
                        (transitionTo
                          (advanceMapPoolBase snap e)
                          .down
                          "min_size increased, insufficient peers").1
                  | false =>
                      have hResult :
                      (onAdvanceMap snap e).1 =
                        (transitionTo
                          (advanceMapPoolBase snap e)
                          .down
                          "min_size increased, insufficient peers").1 := by
                        unfold onAdvanceMap
                        rw [hNewInterval, hPoolChanged, hPrimaryActive, hAvail, hRetryChoose]
                        simp [advanceMapIntervalBase, advanceMapPoolBase]
                      rw [hResult]
                      exact hDown
              | false =>
                  cases hRetryDown : advanceMapPoolChangeRetryChoose snap e with
                  | true =>
                      have hResult :
                        (onAdvanceMap snap e).1 =
                          (chooseActing (advanceMapPoolBase snap e)).1 := by
                          unfold onAdvanceMap
                          rw [hNewInterval, hPoolChanged, hPrimaryActive, hAvail, hRetryDown]
                          simp [advanceMapIntervalBase, advanceMapPoolBase]
                      rw [hResult]
                      exact imageInvariant_chooseActing (advanceMapPoolBase snap e)
                  | false =>
                      have hResult :
                        (onAdvanceMap snap e).1 = advanceMapPoolBase snap e := by
                          unfold onAdvanceMap
                          rw [hNewInterval, hPoolChanged, hPrimaryActive, hAvail, hRetryDown]
                          simp [advanceMapIntervalBase, advanceMapPoolBase]
                      rw [hResult]
                      exact hPoolBase

theorem imageInvariant_reduceValidated_peerInfoReceived
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (reduceValidated snap (.peerInfoReceived e)).1 := by
  simpa [reduceValidated] using imageInvariant_onPeerInfoReceived snap e hInvariant

theorem imageInvariant_reduceValidated_advanceMap
    (snap : Snapshot) (e : Event.AdvanceMap)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (reduceValidated snap (.advanceMap e)).1 := by
  simpa [reduceValidated] using imageInvariant_onAdvanceMap snap e hInvariant

theorem imageInvariant_reduceValidated_peerQueryTimeout
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (reduceValidated snap (.peerQueryTimeout e)).1 := by
  simpa [reduceValidated] using imageInvariant_onPeerQueryTimeout snap e hInvariant

theorem imageInvariant_stepWithValidated_peerInfoReceived
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (stepWithValidated snap (.peerInfoReceived e)).after := by
  simpa [stepWithValidated] using
    imageInvariant_reduceValidated_peerInfoReceived snap e hInvariant

theorem imageInvariant_stepWithValidated_advanceMap
    (snap : Snapshot) (e : Event.AdvanceMap)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (stepWithValidated snap (.advanceMap e)).after := by
  simpa [stepWithValidated] using
    imageInvariant_reduceValidated_advanceMap snap e hInvariant

theorem imageInvariant_stepWithValidated_peerQueryTimeout
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (stepWithValidated snap (.peerQueryTimeout e)).after := by
  simpa [stepWithValidated] using
    imageInvariant_reduceValidated_peerQueryTimeout snap e hInvariant

theorem imageInvariant_step_peerInfoReceived
    (snap : Snapshot) (e : Event.PeerInfoReceived)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (step snap (.peerInfoReceived e)).after := by
  unfold step
  unfold validateEvent
  by_cases hFresh : isFreshEpoch snap.lastPeeringReset e.queryEpoch
  · simpa [hFresh, stepWithValidated] using
      imageInvariant_reduceValidated_peerInfoReceived snap e hInvariant
  · simp [hFresh, hInvariant]

theorem imageInvariant_step_advanceMap
    (snap : Snapshot) (e : Event.AdvanceMap)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (step snap (.advanceMap e)).after := by
  simpa [step, validateEvent, stepWithValidated] using
    imageInvariant_reduceValidated_advanceMap snap e hInvariant

theorem imageInvariant_step_peerQueryTimeout
    (snap : Snapshot) (e : Event.PeerQueryTimeout)
    (hInvariant : ImageInvariant snap) :
    ImageInvariant (step snap (.peerQueryTimeout e)).after := by
  simpa [step, validateEvent, stepWithValidated] using
    imageInvariant_reduceValidated_peerQueryTimeout snap e hInvariant

def imageInvariantReduceValidatedSupported (event : ValidatedEvent) : Prop :=
  match event with
  | .advanceMap _ => True
  | .peerInfoReceived _ => True
  | .peerQueryTimeout _ => True
  | _ => False

theorem imageInvariant_reduceValidated_supported
    (snap : Snapshot) (event : ValidatedEvent)
    (hInvariant : ImageInvariant snap)
    (hSupported : imageInvariantReduceValidatedSupported event) :
    ImageInvariant (reduceValidated snap event).1 := by
  cases event <;> simp [imageInvariantReduceValidatedSupported] at hSupported
  · rename_i e
    exact imageInvariant_reduceValidated_advanceMap snap e hInvariant
  · rename_i e
    exact imageInvariant_reduceValidated_peerInfoReceived snap e hInvariant
  · rename_i e
    exact imageInvariant_reduceValidated_peerQueryTimeout snap e hInvariant

theorem imageInvariant_stepWithValidated_supported
    (snap : Snapshot) (event : ValidatedEvent)
    (hInvariant : ImageInvariant snap)
    (hSupported : imageInvariantReduceValidatedSupported event) :
    ImageInvariant (stepWithValidated snap event).after := by
  simpa [stepWithValidated] using
    imageInvariant_reduceValidated_supported snap event hInvariant hSupported

def imageInvariantStepSupported (event : PeeringEvent) : Prop :=
  match event with
  | .advanceMap _ => True
  | .peerInfoReceived _ => True
  | .peerQueryTimeout _ => True
  | _ => False

theorem imageInvariant_step_supported
    (snap : Snapshot) (event : PeeringEvent)
    (hInvariant : ImageInvariant snap)
    (hSupported : imageInvariantStepSupported event) :
    ImageInvariant (step snap event).after := by
  cases event <;> simp [imageInvariantStepSupported] at hSupported
  · rename_i e
    exact imageInvariant_step_advanceMap snap e hInvariant
  · rename_i e
    exact imageInvariant_step_peerInfoReceived snap e hInvariant
  · rename_i e
    exact imageInvariant_step_peerQueryTimeout snap e hInvariant

end Peering
