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
      if obj' = obj && best.authorityLength < authority.authorityLength then
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
  { entries := infos.foldr (fun info acc => (authorityFromPeerInfo info).entries ++ acc) [] }

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

end Peering
