import Std

namespace Peering

abbrev Epoch := Nat
abbrev OsdId := Int
abbrev PgId := Nat
abbrev ObjectId := Nat
abbrev Length := Nat
abbrev JournalSeq := Nat

def primaryObjectId : ObjectId := 0

inductive State
  | initial
  | reset
  | getPeerInfo
  | waitUpThru
  | active
  | recovering
  | clean
  | stray
  | replicaActive
  | down
  | incomplete
  | deleting
  deriving DecidableEq, Repr

/-- Objectwise committed readable-prefix lengths.
Missing entries mean readable length `0`. -/
structure ObjectImage where
  entries : List (ObjectId × Length) := []
  deriving DecidableEq, Repr

/-- Authority for one object's committed readable prefix. -/
structure ObjectAuthority where
  authorityOsd : OsdId := -1
  authorityLength : Length := 0
  deriving DecidableEq, Repr

/-- Objectwise authority map for committed readable prefixes. -/
structure AuthorityImage where
  entries : List (ObjectId × ObjectAuthority) := []
  deriving DecidableEq, Repr

/-- Blob-level finalization metadata.
Visibility is carried by readable-prefix images; sealing only records whether
future growth is forbidden and, when known, the terminal length. -/
structure BlobMeta where
  sealed : Bool := false
  finalLen : Option Length := none
  deriving DecidableEq, Repr

/-- Objectwise finalization metadata keyed by blob/object id. -/
structure BlobMetaImage where
  entries : List (ObjectId × BlobMeta) := []
  deriving DecidableEq, Repr

structure ObjRecovery where
  obj : ObjectId
  source : OsdId := -1
  fromLength : Length
  toLength : Length
  deriving DecidableEq, Repr

structure PeerRecoveryPlan where
  target : OsdId
  peerCommittedSeq : JournalSeq := 0
  authoritativeSeq : JournalSeq := 0
  recoveries : List ObjRecovery
  deriving DecidableEq, Repr

structure PeerInfo where
  osd : OsdId := -1
  committedSeq : JournalSeq := 0
  committedLength : Length := 0
  image : ObjectImage := {}
  blobMeta : BlobMetaImage := {}
  lastEpochStarted : Epoch := 0
  lastIntervalStarted : Epoch := 0
  deriving DecidableEq, Repr

structure PGInfo where
  pgid : PgId := 0
  committedSeq : JournalSeq := 0
  committedLength : Length := 0
  image : ObjectImage := {}
  blobMeta : BlobMetaImage := {}
  lastEpochStarted : Epoch := 0
  lastIntervalStarted : Epoch := 0
  lastEpochClean : Epoch := 0
  epochCreated : Epoch := 0
  sameIntervalSince : Epoch := 0
  sameUpSince : Epoch := 0
  samePrimarySince : Epoch := 0
  deriving DecidableEq, Repr

structure ActingSet where
  osds : List OsdId := []
  epoch : Epoch := 0
  deriving DecidableEq, Repr

namespace ActingSet

def primary (acting : ActingSet) : Option OsdId :=
  acting.osds.head?

def size (acting : ActingSet) : Nat :=
  acting.osds.length

def contains (acting : ActingSet) (osd : OsdId) : Bool :=
  osd ∈ acting.osds

end ActingSet

namespace Event

structure AdvanceMap where
  newEpoch : Epoch
  newActing : ActingSet
  newUp : ActingSet
  newPoolSize : Nat
  newPoolMinSize : Nat
  priorOsds : List OsdId
  deriving DecidableEq, Repr

structure Initialize where
  pgid : PgId
  whoami : OsdId
  epoch : Epoch
  acting : ActingSet
  up : ActingSet
  poolSize : Nat
  poolMinSize : Nat
  localInfo : PGInfo
  priorOsds : List OsdId
  deriving DecidableEq, Repr

structure PeerInfoReceived where
  sender : OsdId
  info : PeerInfo
  queryEpoch : Epoch := 0
  deriving DecidableEq, Repr

structure PeerQueryTimeout where
  peer : OsdId
  deriving DecidableEq, Repr

structure UpThruUpdated where
  epoch : Epoch
  deriving DecidableEq, Repr

structure ActivateCommitted where
  deriving DecidableEq, Repr

structure RecoveryComplete where
  peer : OsdId
  epoch : Epoch
  deriving DecidableEq, Repr

structure AllReplicasRecovered where
  epoch : Epoch
  peers : List OsdId
  deriving DecidableEq, Repr

structure ReplicaActivate where
  sender : OsdId
  authInfo : PeerInfo
  authSources : AuthorityImage := {}
  authBlobMeta : BlobMetaImage := {}
  authoritativeSeq : JournalSeq := 0
  activationEpoch : Epoch
  deriving DecidableEq, Repr

structure ReplicaRecoveryComplete where
  newCommittedSeq : JournalSeq := 0
  newCommittedLength : Length
  recoveredImage : ObjectImage
  activationEpoch : Epoch
  deriving DecidableEq, Repr

structure DeleteStart where
  deriving DecidableEq, Repr

structure DeleteComplete where
  deriving DecidableEq, Repr

end Event

inductive PeeringEvent
  | initialize (e : Event.Initialize)
  | advanceMap (e : Event.AdvanceMap)
  | peerInfoReceived (e : Event.PeerInfoReceived)
  | peerQueryTimeout (e : Event.PeerQueryTimeout)
  | upThruUpdated (e : Event.UpThruUpdated)
  | activateCommitted (e : Event.ActivateCommitted)
  | recoveryComplete (e : Event.RecoveryComplete)
  | allReplicasRecovered (e : Event.AllReplicasRecovered)
  | replicaActivate (e : Event.ReplicaActivate)
  | replicaRecoveryComplete (e : Event.ReplicaRecoveryComplete)
  | deleteStart (e : Event.DeleteStart)
  | deleteComplete (e : Event.DeleteComplete)
  deriving DecidableEq, Repr

namespace Effect

structure SendQuery where
  target : OsdId
  pgid : PgId
  epoch : Epoch
  deriving DecidableEq, Repr

structure SendNotify where
  target : OsdId
  pgid : PgId
  info : PeerInfo
  epoch : Epoch
  deriving DecidableEq, Repr

structure SendActivate where
  target : OsdId
  pgid : PgId
  authInfo : PeerInfo
  authSources : AuthorityImage := {}
  authBlobMeta : BlobMetaImage := {}
  authoritativeSeq : JournalSeq := 0
  activationEpoch : Epoch
  deriving DecidableEq, Repr

structure ActivatePG where
  pgid : PgId
  authoritativeSeq : JournalSeq := 0
  authoritativeLength : Length
  authoritativeImage : ObjectImage
  authoritativeBlobMeta : BlobMetaImage := {}
  activationEpoch : Epoch
  deriving DecidableEq, Repr

structure DeactivatePG where
  pgid : PgId
  deriving DecidableEq, Repr

structure RecoveryTarget where
  osd : OsdId
  peerLength : Length
  authoritativeLength : Length
  peerCommittedSeq : JournalSeq := 0
  authoritativeSeq : JournalSeq := 0
  recoveries : List ObjRecovery
  deriving DecidableEq, Repr

structure ScheduleRecovery where
  pgid : PgId
  targets : List RecoveryTarget
  deriving DecidableEq, Repr

structure CancelRecovery where
  pgid : PgId
  deriving DecidableEq, Repr

structure MarkClean where
  pgid : PgId
  deriving DecidableEq, Repr

structure PersistState where
  pgid : PgId
  info : PGInfo
  deriving DecidableEq, Repr

structure RequestUpThru where
  epoch : Epoch
  deriving DecidableEq, Repr

structure UpdateHeartbeats where
  peers : List OsdId
  deriving DecidableEq, Repr

structure PublishStats where
  pgid : PgId
  state : State
  committedSeq : JournalSeq := 0
  authoritativeSeq : JournalSeq := 0
  committedLength : Length
  image : ObjectImage
  authoritativeImage : ObjectImage
  authoritativeBlobMeta : BlobMetaImage := {}
  actingSize : Nat
  upSize : Nat
  deriving DecidableEq, Repr

structure DeletePG where
  pgid : PgId
  deriving DecidableEq, Repr

structure RequestActingChange where
  pgid : PgId
  wantActing : List OsdId
  deriving DecidableEq, Repr

structure LogTransition where
  pgid : PgId
  fromState : State
  toState : State
  reason : String
  deriving DecidableEq, Repr

end Effect

inductive PeeringEffect
  | sendQuery (e : Effect.SendQuery)
  | sendNotify (e : Effect.SendNotify)
  | sendActivate (e : Effect.SendActivate)
  | activatePG (e : Effect.ActivatePG)
  | deactivatePG (e : Effect.DeactivatePG)
  | scheduleRecovery (e : Effect.ScheduleRecovery)
  | cancelRecovery (e : Effect.CancelRecovery)
  | markClean (e : Effect.MarkClean)
  | persistState (e : Effect.PersistState)
  | requestUpThru (e : Effect.RequestUpThru)
  | requestActingChange (e : Effect.RequestActingChange)
  | updateHeartbeats (e : Effect.UpdateHeartbeats)
  | publishStats (e : Effect.PublishStats)
  | deletePG (e : Effect.DeletePG)
  | logTransition (e : Effect.LogTransition)
  deriving DecidableEq, Repr

abbrev ValidatedEvent := PeeringEvent

structure StepResult where
  fromState : State
  toState : State
  effects : List PeeringEffect
  deriving DecidableEq, Repr

end Peering
