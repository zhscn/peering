import Peering.Types

namespace Peering

namespace ObjectImage

def keys (image : ObjectImage) : List ObjectId :=
  image.entries.map Prod.fst

def support (image : ObjectImage) : List ObjectId :=
  image.keys.eraseDups

end ObjectImage

namespace AuthorityImage

def keys (image : AuthorityImage) : List ObjectId :=
  image.entries.map Prod.fst

def support (image : AuthorityImage) : List ObjectId :=
  image.keys.eraseDups

end AuthorityImage

def singletonImage (obj : ObjectId) (len : Length) : ObjectImage :=
  if len = 0 then {} else { entries := [(obj, len)] }

def primaryImage (len : Length) : ObjectImage :=
  singletonImage primaryObjectId len

def lookupLengthEntries (obj : ObjectId) : List (ObjectId × Length) → Length
  | [] => 0
  | (obj', len) :: rest =>
      if obj' = obj then
        max len (lookupLengthEntries obj rest)
      else
        lookupLengthEntries obj rest

def lookupLength (image : ObjectImage) (obj : ObjectId) : Length :=
  lookupLengthEntries obj image.entries

def primaryLength (image : ObjectImage) : Length :=
  lookupLength image primaryObjectId

def effectivePeerImage (info : PeerInfo) : ObjectImage :=
  if info.image.entries ≠ [] || info.committedLength = 0 then
    info.image
  else
    primaryImage info.committedLength

def effectivePGImage (info : PGInfo) : ObjectImage :=
  if info.image.entries ≠ [] || info.committedLength = 0 then
    info.image
  else
    primaryImage info.committedLength

def normalizedPeerInfo (info : PeerInfo) : PeerInfo :=
  let image := effectivePeerImage info
  { info with
      image := image
      committedLength := primaryLength image }

def normalizedPGInfo (info : PGInfo) : PGInfo :=
  let image := effectivePGImage info
  { info with
      image := image
      committedLength := primaryLength image }

def joinImage (lhs rhs : ObjectImage) : ObjectImage :=
  { entries := lhs.entries ++ rhs.entries }

def joinImages (images : List ObjectImage) : ObjectImage :=
  images.foldl joinImage {}

def prefixImage (lhs rhs : ObjectImage) : Prop :=
  ∀ obj, lookupLength lhs obj ≤ lookupLength rhs obj

def sameImage (lhs rhs : ObjectImage) : Prop :=
  prefixImage lhs rhs ∧ prefixImage rhs lhs

def clampImageTo (auth image : ObjectImage) : ObjectImage :=
  let entries :=
    (ObjectImage.support image).filterMap fun obj =>
      let bounded := min (lookupLength auth obj) (lookupLength image obj)
      if bounded = 0 then
        none
      else
        some (obj, bounded)
  { entries := entries }

def imageRecoveryGaps (localImage auth : ObjectImage) : List ObjRecovery :=
  (ObjectImage.support auth).filterMap fun obj =>
    let fromLength := lookupLength localImage obj
    let toLength := lookupLength auth obj
    if fromLength < toLength then
      some {
        obj := obj
        fromLength := fromLength
        toLength := toLength
      }
    else
      none

def lookupAuthorityEntries (obj : ObjectId) :
    List (ObjectId × ObjectAuthority) → ObjectAuthority
  | [] => {}
  | (obj', authority) :: rest =>
      let best := lookupAuthorityEntries obj rest
      if obj' = obj && best.authorityLength ≤ authority.authorityLength then
        authority
      else
        best

def lookupAuthority (auth : AuthorityImage) (obj : ObjectId) : ObjectAuthority :=
  lookupAuthorityEntries obj auth.entries

def imageRecoveryGapsFromAuthority (localImage : ObjectImage)
    (auth : AuthorityImage) : List ObjRecovery :=
  (AuthorityImage.support auth).filterMap fun obj =>
    let authority := lookupAuthority auth obj
    let fromLength := lookupLength localImage obj
    let toLength := authority.authorityLength
    if fromLength < toLength then
      some {
        obj := obj
        source := authority.authorityOsd
        fromLength := fromLength
        toLength := toLength
      }
    else
      none

def authorityFromImage (source : OsdId) (image : ObjectImage) : AuthorityImage :=
  let entries :=
    (ObjectImage.support image).filterMap fun obj =>
      let len := lookupLength image obj
      if len = 0 then
        none
      else
        some (obj, { authorityOsd := source, authorityLength := len })
  { entries := entries }

def authorityFromPeerInfo (info : PeerInfo) : AuthorityImage :=
  let normalized := normalizedPeerInfo info
  authorityFromImage normalized.osd normalized.image

def rawAuthoritySources (infos : List PeerInfo) : AuthorityImage :=
  { entries := infos.foldr (fun info acc => (authorityFromPeerInfo info).entries ++ acc) [] }

def canonicalAuthorityImage (raw : AuthorityImage) : AuthorityImage :=
  let entries :=
    (AuthorityImage.support raw).filterMap fun obj =>
      let authority := lookupAuthority raw obj
      if authority.authorityLength = 0 then
        none
      else
        some (obj, authority)
  { entries := entries }

def authorityImageValues (auth : AuthorityImage) : ObjectImage :=
  let entries :=
    (AuthorityImage.support auth).filterMap fun obj =>
      let item := lookupAuthority auth obj
      if item.authorityLength = 0 then
        none
      else
        some (obj, item.authorityLength)
  { entries := entries }

def authoritativeSources (infos : List PeerInfo) : AuthorityImage :=
  canonicalAuthorityImage (rawAuthoritySources infos)

def authoritativeImage (infos : List PeerInfo) : ObjectImage :=
  authorityImageValues (authoritativeSources infos)

def authoritativeCommittedSeq (infos : List PeerInfo) : JournalSeq :=
  infos.foldl (fun best info => max best info.committedSeq) 0

def peerImageRecoveryPlan (auth : AuthorityImage) (peer : PeerInfo) : List ObjRecovery :=
  imageRecoveryGapsFromAuthority (effectivePeerImage peer) auth

def pgImageRecoveryPlan (auth : AuthorityImage) (pg : PGInfo) : List ObjRecovery :=
  imageRecoveryGapsFromAuthority (effectivePGImage pg) auth

def buildPeerRecoveryPlans (auth : AuthorityImage) (authoritativeSeq : JournalSeq)
    (peers : List PeerInfo) :
    List PeerRecoveryPlan :=
  peers.foldr
    (fun raw acc =>
      let peer := normalizedPeerInfo raw
      let gaps := peerImageRecoveryPlan auth peer
      if gaps.isEmpty && peer.committedSeq >= authoritativeSeq then
        acc
      else
        { target := peer.osd
          peerCommittedSeq := peer.committedSeq
          authoritativeSeq := authoritativeSeq
          recoveries := gaps } :: acc)
    []

theorem lookupLengthEntries_append (obj : ObjectId)
    (lhs rhs : List (ObjectId × Length)) :
    lookupLengthEntries obj (lhs ++ rhs) =
      max (lookupLengthEntries obj lhs) (lookupLengthEntries obj rhs) := by
  induction lhs with
  | nil =>
      simp [lookupLengthEntries]
  | cons head tail ih =>
      cases head with
      | mk obj' len =>
          by_cases h : obj' = obj
          · simp [lookupLengthEntries, h, ih, Nat.max_left_comm, Nat.max_comm]
          · simp [lookupLengthEntries, h, ih, Nat.max_comm]

theorem lookupLength_joinImage (lhs rhs : ObjectImage) (obj : ObjectId) :
    lookupLength (joinImage lhs rhs) obj =
      max (lookupLength lhs obj) (lookupLength rhs obj) := by
  simpa [joinImage, lookupLength] using
    lookupLengthEntries_append obj lhs.entries rhs.entries

theorem prefixImage_left_join (lhs rhs : ObjectImage) :
    prefixImage lhs (joinImage lhs rhs) := by
  intro obj
  rw [lookupLength_joinImage]
  exact Nat.le_max_left _ _

theorem prefixImage_right_join (lhs rhs : ObjectImage) :
    prefixImage rhs (joinImage lhs rhs) := by
  intro obj
  rw [lookupLength_joinImage]
  exact Nat.le_max_right _ _

theorem sameImage_implies_prefix (lhs rhs : ObjectImage) :
    sameImage lhs rhs → prefixImage lhs rhs := by
  intro h
  exact h.left

theorem sameImage_refl (image : ObjectImage) : sameImage image image := by
  constructor <;> intro obj <;> exact Nat.le_refl _

theorem lookupLengthEntries_ge_of_mem {entries : List (ObjectId × Length)}
    {obj : ObjectId} {len : Length} :
    (obj, len) ∈ entries → len ≤ lookupLengthEntries obj entries := by
  induction entries with
  | nil =>
      intro h
      cases h
  | cons head tail ih =>
      cases head with
      | mk obj' len' =>
          intro hMem
          by_cases hEq : obj' = obj
          · simp [lookupLengthEntries, hEq] at hMem ⊢
            rcases hMem with rfl | hTail
            · exact Nat.le_max_left _ _
            · exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)
          · simp [lookupLengthEntries, hEq] at hMem ⊢
            rcases hMem with hHead | hTail
            · exact False.elim (hEq hHead.1.symm)
            · exact ih hTail

theorem lookupAuthorityEntries_ge_of_mem
    {entries : List (ObjectId × ObjectAuthority)}
    {obj : ObjectId} {authority : ObjectAuthority} :
    (obj, authority) ∈ entries →
      authority.authorityLength ≤ (lookupAuthorityEntries obj entries).authorityLength := by
  induction entries with
  | nil =>
      intro h
      cases h
  | cons head tail ih =>
      cases head with
      | mk obj' authority' =>
          intro hMem
          by_cases hEq : obj' = obj
          · simp [lookupAuthorityEntries, hEq] at hMem ⊢
            by_cases hLe :
                (lookupAuthorityEntries obj tail).authorityLength ≤ authority'.authorityLength
            · simp [hLe] at hMem ⊢
              rcases hMem with rfl | hTail
              · exact Nat.le_refl _
              · exact Nat.le_trans (ih hTail) hLe
            · simp [hLe] at hMem ⊢
              have hAuthority' :
                  authority'.authorityLength ≤ (lookupAuthorityEntries obj tail).authorityLength :=
                Nat.le_of_not_ge hLe
              rcases hMem with rfl | hTail
              · exact hAuthority'
              · exact ih hTail
          · simp [lookupAuthorityEntries, hEq] at hMem ⊢
            rcases hMem with hHead | hTail
            · exact False.elim (hEq hHead.1.symm)
            · exact ih hTail

theorem mem_lookupAuthorityEntries_of_pos
    {entries : List (ObjectId × ObjectAuthority)} {obj : ObjectId} :
    0 < (lookupAuthorityEntries obj entries).authorityLength →
      (obj, lookupAuthorityEntries obj entries) ∈ entries := by
  induction entries with
  | nil =>
      intro h
      simp [lookupAuthorityEntries] at h
  | cons head tail ih =>
      cases head with
      | mk obj' authority =>
          by_cases hEq : obj' = obj
          · intro hPos
            by_cases hLe :
                (lookupAuthorityEntries obj tail).authorityLength ≤ authority.authorityLength
            · simp [lookupAuthorityEntries, hEq, hLe]
            · simp [lookupAuthorityEntries, hEq, hLe]
              have hTailPos : 0 < (lookupAuthorityEntries obj tail).authorityLength := by
                simpa [lookupAuthorityEntries, hEq, hLe] using hPos
              exact Or.inr (ih hTailPos)
          · intro hPos
            simp [lookupAuthorityEntries, hEq]
            have hTailPos : 0 < (lookupAuthorityEntries obj tail).authorityLength := by
              simpa [lookupAuthorityEntries, hEq] using hPos
            exact Or.inr (ih hTailPos)

theorem mem_keys_of_lookupLengthEntries_pos
    {entries : List (ObjectId × Length)} {obj : ObjectId} :
    0 < lookupLengthEntries obj entries → obj ∈ entries.map Prod.fst := by
  induction entries with
  | nil =>
      intro h
      simp [lookupLengthEntries] at h
  | cons head tail ih =>
      cases head with
      | mk obj' len =>
          by_cases hEq : obj' = obj
          · intro _
            simp [hEq]
          · intro hPos
            have hTail : 0 < lookupLengthEntries obj tail := by
              simpa [lookupLengthEntries, hEq] using hPos
            simp [ih hTail]

theorem mem_support_of_lookupLength_pos (image : ObjectImage) {obj : ObjectId} :
    0 < lookupLength image obj → obj ∈ ObjectImage.support image := by
  intro hPos
  exact (List.mem_eraseDups).2 (mem_keys_of_lookupLengthEntries_pos hPos)

theorem lookupLengthEntries_le_of_forall {entries : List (ObjectId × Length)}
    {obj : ObjectId} {bound : Length}
    (hBound : ∀ {len}, (obj, len) ∈ entries → len ≤ bound) :
    lookupLengthEntries obj entries ≤ bound := by
  induction entries with
  | nil =>
      simp [lookupLengthEntries]
  | cons head tail ih =>
      cases head with
      | mk obj' len =>
          by_cases hEq : obj' = obj
          · cases hEq
            have hHead : len ≤ bound := hBound (by simp)
            have hTail :
                ∀ {len'}, (obj, len') ∈ tail → len' ≤ bound := by
              intro len' hMem
              exact hBound (by simp [hMem])
            have hTailLe := ih hTail
            simpa [lookupLengthEntries] using (Nat.max_le.2 ⟨hHead, hTailLe⟩)
          · have hTail :
                ∀ {len'}, (obj, len') ∈ tail → len' ≤ bound := by
              intro len' hMem
              exact hBound (by simp [hMem])
            simpa [lookupLengthEntries, hEq] using ih hTail

theorem lookupLength_clampImageTo (auth image : ObjectImage) (obj : ObjectId) :
    lookupLength (clampImageTo auth image) obj =
      min (lookupLength auth obj) (lookupLength image obj) := by
  let bound := min (lookupLength auth obj) (lookupLength image obj)
  apply Nat.le_antisymm
  · unfold lookupLength clampImageTo
    apply lookupLengthEntries_le_of_forall
    intro len hMem
    rcases (List.mem_filterMap).1 hMem with ⟨obj', hObj', hSome⟩
    by_cases hZero : min (lookupLength auth obj') (lookupLength image obj') = 0
    · simp [hZero] at hSome
    · simp [hZero] at hSome
      rcases hSome with ⟨hObjEq, hLenEq⟩
      cases hObjEq
      cases hLenEq
      exact Nat.le_refl _
  · by_cases hZero : bound = 0
    · have hLe : 0 ≤ lookupLength (clampImageTo auth image) obj := Nat.zero_le _
      simp [bound, hZero] at hLe ⊢
    · have hBoundPos : 0 < bound := Nat.pos_of_ne_zero hZero
      have hImagePos : 0 < lookupLength image obj := by
        exact Nat.lt_of_lt_of_le hBoundPos (Nat.min_le_right _ _)
      have hEntry :
          (obj, bound) ∈ (clampImageTo auth image).entries := by
        unfold clampImageTo
        apply (List.mem_filterMap).2
        refine ⟨obj, mem_support_of_lookupLength_pos image hImagePos, ?_⟩
        simp [bound, hZero]
      simpa [lookupLength, bound] using lookupLengthEntries_ge_of_mem hEntry

theorem prefixImage_trans (lhs mid rhs : ObjectImage) :
    prefixImage lhs mid → prefixImage mid rhs → prefixImage lhs rhs := by
  intro hLeft hRight obj
  exact Nat.le_trans (hLeft obj) (hRight obj)

theorem prefixImage_clampImageTo_left (auth image : ObjectImage) :
    prefixImage (clampImageTo auth image) auth := by
  intro obj
  rw [lookupLength_clampImageTo]
  exact Nat.min_le_left _ _

theorem prefixImage_clampImageTo_right (auth image : ObjectImage) :
    prefixImage (clampImageTo auth image) image := by
  intro obj
  rw [lookupLength_clampImageTo]
  exact Nat.min_le_right _ _

theorem sameImage_clampImageTo_of_prefix
    (auth image : ObjectImage)
    (hPrefix : prefixImage image auth) :
    sameImage (clampImageTo auth image) image := by
  constructor
  · exact prefixImage_clampImageTo_right auth image
  · intro obj
    rw [lookupLength_clampImageTo]
    simp [Nat.min_eq_right (hPrefix obj)]

theorem mem_keys_of_lookupAuthorityEntries_pos
    {entries : List (ObjectId × ObjectAuthority)} {obj : ObjectId} :
    0 < (lookupAuthorityEntries obj entries).authorityLength →
      obj ∈ entries.map Prod.fst := by
  induction entries with
  | nil =>
      intro h
      simp [lookupAuthorityEntries] at h
  | cons head tail ih =>
      cases head with
      | mk obj' authority =>
          by_cases hEq : obj' = obj
          · intro _
            simp [hEq]
          · intro hPos
            have hTail :
                0 < (lookupAuthorityEntries obj tail).authorityLength := by
              simpa [lookupAuthorityEntries, hEq] using hPos
            simp [ih hTail]

theorem mem_support_of_lookupAuthority_pos (auth : AuthorityImage) {obj : ObjectId} :
    0 < (lookupAuthority auth obj).authorityLength → obj ∈ AuthorityImage.support auth := by
  intro hPos
  exact (List.mem_eraseDups).2 (mem_keys_of_lookupAuthorityEntries_pos hPos)

theorem mem_authorityFromImage_entries_of_lookupLength_pos
    (source : OsdId) (image : ObjectImage) {obj : ObjectId} :
    0 < lookupLength image obj →
      (obj, { authorityOsd := source, authorityLength := lookupLength image obj }) ∈
        (authorityFromImage source image).entries := by
  intro hPos
  unfold authorityFromImage
  apply (List.mem_filterMap).2
  refine ⟨obj, ?_, ?_⟩
  · exact mem_support_of_lookupLength_pos image hPos
  · simp [Nat.ne_of_gt hPos]

theorem mem_authorityImageValues_entries_of_lookupAuthority_pos
    (auth : AuthorityImage) {obj : ObjectId} :
    0 < (lookupAuthority auth obj).authorityLength →
      (obj, (lookupAuthority auth obj).authorityLength) ∈ (authorityImageValues auth).entries := by
  intro hPos
  unfold authorityImageValues
  apply (List.mem_filterMap).2
  refine ⟨obj, ?_, ?_⟩
  · exact mem_support_of_lookupAuthority_pos auth hPos
  · simp [Nat.ne_of_gt hPos]

theorem lookupLength_authorityImageValues_ge_lookupAuthority
    (auth : AuthorityImage) (obj : ObjectId) :
    (lookupAuthority auth obj).authorityLength ≤ lookupLength (authorityImageValues auth) obj := by
  by_cases hPos : 0 < (lookupAuthority auth obj).authorityLength
  · exact lookupLengthEntries_ge_of_mem
      (mem_authorityImageValues_entries_of_lookupAuthority_pos auth hPos)
  · have hZero : (lookupAuthority auth obj).authorityLength = 0 := Nat.eq_zero_of_not_pos hPos
    simp [hZero]

theorem foldlMaxCommittedSeq_mono
    (infos : List PeerInfo) {lhs rhs : JournalSeq} :
    lhs ≤ rhs →
      infos.foldl (fun best info => max best info.committedSeq) lhs ≤
        infos.foldl (fun best info => max best info.committedSeq) rhs := by
  intro h
  induction infos generalizing lhs rhs with
  | nil =>
      simpa using h
  | cons head tail ih =>
      apply ih
      exact (Nat.max_le).mpr
        ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

theorem le_foldlMaxCommittedSeq
    (infos : List PeerInfo) (init : JournalSeq) :
    init ≤ infos.foldl (fun best info => max best info.committedSeq) init := by
  induction infos generalizing init with
  | nil =>
      simp
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem committedSeq_le_authoritativeCommittedSeq_of_mem
    (infos : List PeerInfo) (info : PeerInfo) :
    info ∈ infos → info.committedSeq ≤ authoritativeCommittedSeq infos := by
  intro hMem
  unfold authoritativeCommittedSeq
  induction infos with
  | nil =>
      cases hMem
  | cons head tail ih =>
      simp at hMem ⊢
      cases hMem with
      | inl hEq =>
          have hSeq : head.committedSeq = info.committedSeq := by
            cases hEq
            rfl
          simpa [authoritativeCommittedSeq] using
            (hSeq ▸ le_foldlMaxCommittedSeq tail info.committedSeq)
      | inr hTail =>
          exact Nat.le_trans (ih hTail)
            (by
              simpa [authoritativeCommittedSeq] using
                foldlMaxCommittedSeq_mono tail (lhs := 0) (rhs := head.committedSeq)
                  (Nat.zero_le _))

theorem effectivePeerImage_normalizedPeerInfo (info : PeerInfo) :
    effectivePeerImage (normalizedPeerInfo info) = effectivePeerImage info := by
  let image := effectivePeerImage info
  change effectivePeerImage { info with image := image, committedLength := primaryLength image } = image
  by_cases h : image.entries = []
  · have hlen : primaryLength image = 0 := by
      simp [primaryLength, lookupLength, lookupLengthEntries, h, image]
    simp [effectivePeerImage, h, hlen]
  · simp [effectivePeerImage, h]

theorem effectivePGImage_normalizedPGInfo (info : PGInfo) :
    effectivePGImage (normalizedPGInfo info) = effectivePGImage info := by
  let image := effectivePGImage info
  change effectivePGImage { info with image := image, committedLength := primaryLength image } = image
  by_cases h : image.entries = []
  · have hlen : primaryLength image = 0 := by
      simp [primaryLength, lookupLength, lookupLengthEntries, h, image]
    simp [effectivePGImage, h, hlen]
  · simp [effectivePGImage, h]

theorem mem_rawAuthoritySources_entries_of_mem
    (infos : List PeerInfo) (info : PeerInfo)
    (entry : ObjectId × ObjectAuthority) :
    info ∈ infos →
      entry ∈ (authorityFromPeerInfo info).entries →
      entry ∈ (rawAuthoritySources infos).entries := by
  intro hMem hEntry
  induction infos generalizing info entry with
  | nil =>
      cases hMem
  | cons head tail ih =>
      have hMem' : info = head ∨ info ∈ tail := by
        simpa using hMem
      rcases hMem' with rfl | hTail
      ·
        simpa [rawAuthoritySources] using
          (List.mem_append.mpr (Or.inl hEntry) :
            entry ∈ (authorityFromPeerInfo info).entries ++ (rawAuthoritySources tail).entries)
      ·
        simpa [rawAuthoritySources] using
          (List.mem_append.mpr (Or.inr (ih info entry hTail hEntry)) :
            entry ∈ (authorityFromPeerInfo head).entries ++ (rawAuthoritySources tail).entries)

theorem mem_canonicalAuthorityImage_entries_of_lookupAuthority_pos
    (raw : AuthorityImage) {obj : ObjectId} :
    0 < (lookupAuthority raw obj).authorityLength →
      (obj, lookupAuthority raw obj) ∈ (canonicalAuthorityImage raw).entries := by
  intro hPos
  unfold canonicalAuthorityImage
  apply (List.mem_filterMap).2
  refine ⟨obj, ?_, ?_⟩
  · exact mem_support_of_lookupAuthority_pos raw hPos
  · simp [Nat.ne_of_gt hPos]

theorem lookupAuthority_canonicalAuthorityImage_ge_lookupAuthority
    (raw : AuthorityImage) (obj : ObjectId) :
    (lookupAuthority raw obj).authorityLength ≤
      (lookupAuthority (canonicalAuthorityImage raw) obj).authorityLength := by
  by_cases hPos : 0 < (lookupAuthority raw obj).authorityLength
  · exact lookupAuthorityEntries_ge_of_mem
      (mem_canonicalAuthorityImage_entries_of_lookupAuthority_pos raw hPos)
  · have hZero : (lookupAuthority raw obj).authorityLength = 0 := Nat.eq_zero_of_not_pos hPos
    simp [canonicalAuthorityImage, hZero]

theorem mem_rawAuthoritySources_entries_exists_peer
    (infos : List PeerInfo) (entry : ObjectId × ObjectAuthority) :
    entry ∈ (rawAuthoritySources infos).entries →
      ∃ info ∈ infos, entry ∈ (authorityFromPeerInfo info).entries := by
  intro hMem
  induction infos with
  | nil =>
      simp [rawAuthoritySources] at hMem
  | cons head tail ih =>
      change entry ∈ (authorityFromPeerInfo head).entries ++ (rawAuthoritySources tail).entries at hMem
      rcases List.mem_append.mp hMem with hHead | hTail
      · exact ⟨head, by simp, hHead⟩
      · rcases ih hTail with ⟨info, hInfo, hEntry⟩
        exact ⟨info, by simp [hInfo], hEntry⟩

theorem authorityLength_eq_lookupLength_of_mem_authorityFromImage
    (source : OsdId) (image : ObjectImage) {obj : ObjectId} {authority : ObjectAuthority} :
    (obj, authority) ∈ (authorityFromImage source image).entries →
      authority.authorityLength = lookupLength image obj := by
  intro hMem
  unfold authorityFromImage at hMem
  rcases (List.mem_filterMap).1 hMem with ⟨obj', hObj', hSome⟩
  by_cases hZero : lookupLength image obj' = 0
  · simp [hZero] at hSome
  · simp [hZero] at hSome
    rcases hSome with ⟨hEqObj, hEqAuth⟩
    cases hEqObj
    cases hEqAuth
    rfl

theorem authorityLength_eq_lookupLength_of_mem_authorityFromPeerInfo
    (info : PeerInfo) {obj : ObjectId} {authority : ObjectAuthority} :
    (obj, authority) ∈ (authorityFromPeerInfo info).entries →
      authority.authorityLength = lookupLength (effectivePeerImage info) obj := by
  intro hMem
  simpa [authorityFromPeerInfo, effectivePeerImage_normalizedPeerInfo] using
    authorityLength_eq_lookupLength_of_mem_authorityFromImage
      (normalizedPeerInfo info).osd (normalizedPeerInfo info).image hMem

theorem lookupAuthority_rawAuthoritySources_ge_peerLength
    (infos : List PeerInfo) (info : PeerInfo) (obj : ObjectId)
    (hMem : info ∈ infos) :
    lookupLength (effectivePeerImage info) obj ≤
      (lookupAuthority (rawAuthoritySources infos) obj).authorityLength := by
  by_cases hPos : 0 < lookupLength (effectivePeerImage info) obj
  · have hEntry :
        (obj,
          { authorityOsd := info.osd
            authorityLength := lookupLength (effectivePeerImage info) obj }) ∈
          (authorityFromPeerInfo info).entries := by
      simpa [authorityFromPeerInfo, effectivePeerImage_normalizedPeerInfo] using
        mem_authorityFromImage_entries_of_lookupLength_pos
          info.osd (effectivePeerImage info) hPos
    have hRaw :
        (obj,
          { authorityOsd := info.osd
            authorityLength := lookupLength (effectivePeerImage info) obj }) ∈
          (rawAuthoritySources infos).entries :=
      mem_rawAuthoritySources_entries_of_mem infos info _ hMem hEntry
    exact lookupAuthorityEntries_ge_of_mem hRaw
  · have hZero : lookupLength (effectivePeerImage info) obj = 0 := Nat.eq_zero_of_not_pos hPos
    simp [hZero]

theorem prefixImage_authoritativeImage_of_mem
    (infos : List PeerInfo) (info : PeerInfo)
    (hMem : info ∈ infos) :
    prefixImage (effectivePeerImage info) (authoritativeImage infos) := by
  intro obj
  unfold authoritativeImage authoritativeSources
  exact Nat.le_trans
    (lookupAuthority_rawAuthoritySources_ge_peerLength infos info obj hMem)
    (Nat.le_trans
      (lookupAuthority_canonicalAuthorityImage_ge_lookupAuthority
        (rawAuthoritySources infos) obj)
      (lookupLength_authorityImageValues_ge_lookupAuthority
        (canonicalAuthorityImage (rawAuthoritySources infos)) obj))

end Peering
