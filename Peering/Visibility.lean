import Peering.Invariants

namespace Peering

structure ReadResult where
  obj : ObjectId
  fromLength : Length
  toLength : Length
  deriving DecidableEq, Repr

structure AppendAck where
  obj : ObjectId
  fromLength : Length
  toLength : Length
  deriving DecidableEq, Repr

structure AppendResult where
  ack : AppendAck
  image : ObjectImage
  deriving DecidableEq, Repr

structure SealAck where
  obj : ObjectId
  finalLen : Length
  deriving DecidableEq, Repr

structure SealResult where
  ack : SealAck
  blobMeta : BlobMeta
  image : ObjectImage
  deriving DecidableEq, Repr

def readFromReadable? (image : ObjectImage)
    (obj fromLength readLen : Length) : Option ReadResult :=
  let toLength := fromLength + readLen
  if toLength ≤ lookupLength image obj then
    some {
      obj := obj
      fromLength := fromLength
      toLength := toLength
    }
  else
    none

def appendReadable? (blobMeta : BlobMeta) (image : ObjectImage)
    (obj delta : Length) : Option AppendResult :=
  if blobMeta.sealed then
    none
  else
    let fromLength := lookupLength image obj
    let toLength := fromLength + delta
    some {
      ack := {
        obj := obj
        fromLength := fromLength
        toLength := toLength
      }
      image := appendReadablePrefix image obj delta
    }

def sealBlob (blobMeta : BlobMeta) (image : ObjectImage) (obj : ObjectId) :
    SealResult :=
  let finalLen := lookupLength image obj
  {
    ack := {
      obj := obj
      finalLen := finalLen
    }
    blobMeta := { blobMeta with sealed := true, finalLen := some finalLen }
    image := image
  }

theorem ReadSafe
    {visible authority : ObjectImage}
    {obj fromLength readLen : Length}
    {result : ReadResult}
    (hPrefix : prefixImage visible authority) :
    readFromReadable? visible obj fromLength readLen = some result →
      result.obj = obj ∧
        result.fromLength = fromLength ∧
        result.toLength = fromLength + readLen ∧
        result.toLength ≤ lookupLength authority obj := by
  intro hRead
  unfold readFromReadable? at hRead
  by_cases hWithin : fromLength + readLen ≤ lookupLength visible obj
  · simp [hWithin] at hRead
    cases hRead
    exact ⟨rfl, rfl, rfl, Nat.le_trans hWithin (hPrefix obj)⟩
  · simp [hWithin] at hRead

theorem ReadSafeLocal
    {snap : Snapshot}
    (hInvariant : ImageInvariant snap)
    {obj fromLength readLen : Length}
    {result : ReadResult} :
    readFromReadable? (effectivePGImage snap.localInfo) obj fromLength readLen =
        some result →
      result.toLength ≤ lookupLength snap.authImage obj := by
  rcases hInvariant with ⟨_, _, _, _, hLocal, _, _, _⟩
  intro hRead
  rcases ReadSafe hLocal.2 hRead with ⟨_, _, _, hSafe⟩
  exact hSafe

theorem ReadSafeReplica
    {snap : Snapshot}
    (hInvariant : ImageInvariant snap)
    {peer : PeerInfo}
    (hPeer : peer ∈ actingReplicaImages snap)
    {obj fromLength readLen : Length}
    {result : ReadResult} :
    readFromReadable? (effectivePeerImage peer) obj fromLength readLen =
        some result →
      result.toLength ≤ lookupLength snap.authImage obj := by
  rcases hInvariant with ⟨_, _, _, _, _, hActing, _, _⟩
  intro hRead
  rcases ReadSafe (hActing peer hPeer).2 hRead with ⟨_, _, _, hSafe⟩
  exact hSafe

theorem AppendVisible
    {blobMeta : BlobMeta}
    {image : ObjectImage}
    {obj delta : Length}
    {result : AppendResult} :
    appendReadable? blobMeta image obj delta = some result →
      blobMeta.sealed = false ∧
        result.ack.obj = obj ∧
        result.ack.fromLength = lookupLength image obj ∧
        result.ack.toLength = lookupLength image obj + delta ∧
        lookupLength result.image obj = result.ack.toLength ∧
        prefixImage image result.image ∧
        (∀ obj' ≠ obj,
          lookupLength result.image obj' = lookupLength image obj') := by
  intro hAppend
  cases hSeal : blobMeta.sealed <;> simp [appendReadable?, hSeal] at hAppend
  cases hAppend
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa using lookupLength_appendReadablePrefix image obj delta
  · exact prefixImage_appendReadablePrefix image obj delta
  · intro obj' hNe
    simpa using lookupLength_appendReadablePrefix_of_ne image obj obj' delta hNe

theorem SealFinalizes
    (blobMeta : BlobMeta) (image : ObjectImage) (obj : ObjectId) :
    let result := sealBlob blobMeta image obj
    result.ack.obj = obj ∧
      result.ack.finalLen = lookupLength image obj ∧
      result.blobMeta.sealed = true ∧
      result.blobMeta.finalLen = some (lookupLength image obj) ∧
      result.image = image ∧
      (∀ delta, 0 < delta →
        appendReadable? result.blobMeta result.image obj delta = none) := by
  simp [sealBlob, appendReadable?]

end Peering
