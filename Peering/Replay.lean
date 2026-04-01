import Lean.Data.Json
import Lean.Data.Json.Parser
import Peering.Machine

open Lean

namespace Peering

structure SnapshotChecks where
  haveEnoughInfo : Bool
  imageInvariant : Bool
  imageClean : Bool
  imageRecovering : Bool
  deriving DecidableEq, Repr

structure ReplayStep where
  step : Nat
  fromState : State
  toState : State
  event : PeeringEvent
  before : Snapshot
  beforeChecks : SnapshotChecks
  after : Snapshot
  afterChecks : SnapshotChecks
  effects : List PeeringEffect
  deriving DecidableEq, Repr

structure ReplaySummary where
  seed : Nat
  events : Nat
  deriving DecidableEq, Repr

inductive ReplayLine
  | step (line : ReplayStep)
  | summary (line : ReplaySummary)
  deriving DecidableEq, Repr

structure ReplayCursor where
  current : Snapshot := {}
  deriving DecidableEq, Repr

structure ReplayStats where
  steps : Nat := 0
  summaries : Nat := 0
  deriving DecidableEq, Repr

def insertSortedByRepr [Repr α] (item : α) : List α → List α
  | [] => [item]
  | head :: tail =>
      if reprStr item ≤ reprStr head then
        item :: head :: tail
      else
        head :: insertSortedByRepr item tail

def normalizeByRepr [Repr α] (items : List α) : List α :=
  items.foldr insertSortedByRepr []

def normalizeEffects (effects : List PeeringEffect) : List PeeringEffect :=
  normalizeByRepr effects

def normalizeObjectImage (image : ObjectImage) : ObjectImage :=
  { image with entries := normalizeByRepr image.entries }

def normalizeAuthorityImage (auth : AuthorityImage) : AuthorityImage :=
  { auth with entries := normalizeByRepr auth.entries }

def normalizeObjRecovery (item : ObjRecovery) : ObjRecovery :=
  item

def normalizePeerRecoveryPlan (plan : PeerRecoveryPlan) : PeerRecoveryPlan :=
  { plan with recoveries := normalizeByRepr (plan.recoveries.map normalizeObjRecovery) }

def normalizePeerInfo (info : PeerInfo) : PeerInfo :=
  { info with image := normalizeObjectImage info.image }

def normalizePGInfoReplay (info : PGInfo) : PGInfo :=
  { info with image := normalizeObjectImage info.image }

def normalizeSnapshot (snap : Snapshot) : Snapshot :=
  { snap with
    localInfo := normalizePGInfoReplay snap.localInfo
    authImage := normalizeObjectImage snap.authImage
    authSources := normalizeAuthorityImage snap.authSources
    peerInfo := normalizeByRepr (snap.peerInfo.map fun (osd, info) => (osd, normalizePeerInfo info))
    peersQueried := normalizeByRepr snap.peersQueried
    peersResponded := normalizeByRepr snap.peersResponded
    priorOsds := normalizeByRepr snap.priorOsds
    peerRecoveryPlans := normalizeByRepr (snap.peerRecoveryPlans.map normalizePeerRecoveryPlan)
    localRecoveryPlan := normalizeByRepr (snap.localRecoveryPlan.map normalizeObjRecovery)
    recovered := normalizeByRepr snap.recovered
    timedOutProbes := normalizeByRepr snap.timedOutProbes }

def parseStateName (name : String) : Except String State :=
  match name with
  | "Initial" => pure .initial
  | "Reset" => pure .reset
  | "GetPeerInfo" => pure .getPeerInfo
  | "WaitUpThru" => pure .waitUpThru
  | "Active" => pure .active
  | "Recovering" => pure .recovering
  | "Clean" => pure .clean
  | "Stray" => pure .stray
  | "ReplicaActive" => pure .replicaActive
  | "Down" => pure .down
  | "Incomplete" => pure .incomplete
  | "Deleting" => pure .deleting
  | other => throw s!"unknown state name: {other}"

def parseList (json : Json) (f : Json → Except String α) : Except String (List α) := do
  let arr ← json.getArr?
  arr.toList.mapM f

def parseObjectImage (json : Json) : Except String ObjectImage := do
  let entries ← parseList json fun item => do
    pure ((← item.getObjValAs? ObjectId "obj"), (← item.getObjValAs? Length "len"))
  pure { entries := entries }

def parseAuthorityImage (json : Json) : Except String AuthorityImage := do
  let entries ← parseList json fun item => do
    pure ((← item.getObjValAs? ObjectId "obj"), {
      authorityOsd := ← item.getObjValAs? OsdId "osd"
      authorityLength := ← item.getObjValAs? Length "len"
    })
  pure { entries := entries }

def parseActingSet (json : Json) : Except String ActingSet := do
  pure {
    osds := ← json.getObjValAs? (List OsdId) "osds"
    epoch := ← json.getObjValAs? Epoch "epoch"
  }

def parsePeerInfo (json : Json) : Except String PeerInfo := do
  pure {
    osd := ← json.getObjValAs? OsdId "osd"
    committedSeq := ← json.getObjValAs? JournalSeq "committed_seq"
    committedLength := ← json.getObjValAs? Length "committed_length"
    image := ← parseObjectImage (← json.getObjVal? "image")
    lastEpochStarted := ← json.getObjValAs? Epoch "last_epoch_started"
    lastIntervalStarted := ← json.getObjValAs? Epoch "last_interval_started"
  }

def parsePGInfo (json : Json) : Except String PGInfo := do
  pure {
    pgid := ← json.getObjValAs? PgId "pgid"
    committedSeq := ← json.getObjValAs? JournalSeq "committed_seq"
    committedLength := ← json.getObjValAs? Length "committed_length"
    image := ← parseObjectImage (← json.getObjVal? "image")
    lastEpochStarted := ← json.getObjValAs? Epoch "last_epoch_started"
    lastIntervalStarted := ← json.getObjValAs? Epoch "last_interval_started"
    lastEpochClean := ← json.getObjValAs? Epoch "last_epoch_clean"
    epochCreated := ← json.getObjValAs? Epoch "epoch_created"
    sameIntervalSince := ← json.getObjValAs? Epoch "same_interval_since"
    sameUpSince := ← json.getObjValAs? Epoch "same_up_since"
    samePrimarySince := ← json.getObjValAs? Epoch "same_primary_since"
  }

def parseObjRecovery (json : Json) : Except String ObjRecovery := do
  pure {
    obj := ← json.getObjValAs? ObjectId "obj"
    source := ← json.getObjValAs? OsdId "source"
    fromLength := ← json.getObjValAs? Length "from_length"
    toLength := ← json.getObjValAs? Length "to_length"
  }

def parsePeerRecoveryPlan (json : Json) : Except String PeerRecoveryPlan := do
  pure {
    target := ← json.getObjValAs? OsdId "target"
    peerCommittedSeq := ← json.getObjValAs? JournalSeq "peer_committed_seq"
    authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
    recoveries := ← parseList (← json.getObjVal? "recoveries") parseObjRecovery
  }

def parseSnapshotChecks (json : Json) : Except String SnapshotChecks := do
  pure {
    haveEnoughInfo := ← json.getObjValAs? Bool "have_enough_info"
    imageInvariant := ← json.getObjValAs? Bool "image_invariant"
    imageClean := ← json.getObjValAs? Bool "image_clean"
    imageRecovering := ← json.getObjValAs? Bool "image_recovering"
  }

def parseSnapshot (json : Json) : Except String Snapshot := do
  let peerInfos ← parseList (← json.getObjVal? "peer_info") parsePeerInfo
  pure {
    state := ← parseStateName (← json.getObjValAs? String "state")
    pgid := ← json.getObjValAs? PgId "pgid"
    whoami := ← json.getObjValAs? OsdId "whoami"
    epoch := ← json.getObjValAs? Epoch "epoch"
    acting := ← parseActingSet (← json.getObjVal? "acting")
    up := ← parseActingSet (← json.getObjVal? "up")
    poolSize := ← json.getObjValAs? Nat "pool_size"
    poolMinSize := ← json.getObjValAs? Nat "pool_min_size"
    localInfo := ← parsePGInfo (← json.getObjVal? "local_info")
    authSeq := ← json.getObjValAs? JournalSeq "auth_seq"
    authImage := ← parseObjectImage (← json.getObjVal? "auth_image")
    authSources := ← parseAuthorityImage (← json.getObjVal? "auth_sources")
    peerInfo := peerInfos.map fun info => (info.osd, info)
    peersQueried := ← json.getObjValAs? (List OsdId) "peers_queried"
    peersResponded := ← json.getObjValAs? (List OsdId) "peers_responded"
    priorOsds := ← json.getObjValAs? (List OsdId) "prior_osds"
    peerRecoveryPlans := ← parseList (← json.getObjVal? "peer_recovery_plans") parsePeerRecoveryPlan
    localRecoveryPlan := ← parseList (← json.getObjVal? "local_recovery_plan") parseObjRecovery
    recovered := ← json.getObjValAs? (List OsdId) "recovered"
    timedOutProbes := ← json.getObjValAs? (List OsdId) "timed_out_probes"
    needUpThru := ← json.getObjValAs? Bool "need_up_thru"
    activated := ← json.getObjValAs? Bool "activated"
    pendingActingChange := ← json.getObjValAs? Bool "pending_acting_change"
    lastPeeringReset := ← json.getObjValAs? Epoch "last_peering_reset"
  }

def parseEvent (json : Json) : Except String PeeringEvent := do
  match (← json.getObjValAs? String "type") with
  | "Initialize" =>
      pure <| .initialize {
        pgid := ← json.getObjValAs? PgId "pgid"
        whoami := ← json.getObjValAs? OsdId "whoami"
        epoch := ← json.getObjValAs? Epoch "epoch"
        acting := ← parseActingSet (← json.getObjVal? "acting")
        up := ← parseActingSet (← json.getObjVal? "up")
        poolSize := ← json.getObjValAs? Nat "pool_size"
        poolMinSize := ← json.getObjValAs? Nat "pool_min_size"
        localInfo := ← parsePGInfo (← json.getObjVal? "local_info")
        priorOsds := ← json.getObjValAs? (List OsdId) "prior_osds"
      }
  | "AdvanceMap" =>
      pure <| .advanceMap {
        newEpoch := ← json.getObjValAs? Epoch "new_epoch"
        newActing := ← parseActingSet (← json.getObjVal? "new_acting")
        newUp := ← parseActingSet (← json.getObjVal? "new_up")
        newPoolSize := ← json.getObjValAs? Nat "new_pool_size"
        newPoolMinSize := ← json.getObjValAs? Nat "new_pool_min_size"
        priorOsds := ← json.getObjValAs? (List OsdId) "prior_osds"
      }
  | "PeerInfoReceived" =>
      pure <| .peerInfoReceived {
        sender := ← json.getObjValAs? OsdId "from"
        info := ← parsePeerInfo (← json.getObjVal? "info")
        queryEpoch := ← json.getObjValAs? Epoch "query_epoch"
      }
  | "PeerQueryTimeout" =>
      pure <| .peerQueryTimeout {
        peer := ← json.getObjValAs? OsdId "peer"
      }
  | "UpThruUpdated" =>
      pure <| .upThruUpdated {
        epoch := ← json.getObjValAs? Epoch "epoch"
      }
  | "ActivateCommitted" =>
      pure <| .activateCommitted {}
  | "RecoveryComplete" =>
      pure <| .recoveryComplete {
        peer := ← json.getObjValAs? OsdId "peer"
        epoch := ← json.getObjValAs? Epoch "epoch"
      }
  | "AllReplicasRecovered" =>
      pure <| .allReplicasRecovered {
        epoch := ← json.getObjValAs? Epoch "epoch"
        peers := ← json.getObjValAs? (List OsdId) "peers"
      }
  | "ReplicaActivate" =>
      pure <| .replicaActivate {
        sender := ← json.getObjValAs? OsdId "from"
        authInfo := ← parsePeerInfo (← json.getObjVal? "auth_info")
        authSources := ← parseAuthorityImage (← json.getObjVal? "auth_sources")
        authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
        activationEpoch := ← json.getObjValAs? Epoch "activation_epoch"
      }
  | "ReplicaRecoveryComplete" =>
      pure <| .replicaRecoveryComplete {
        newCommittedSeq := ← json.getObjValAs? JournalSeq "new_committed_seq"
        newCommittedLength := ← json.getObjValAs? Length "new_committed_length"
        recoveredImage := ← parseObjectImage (← json.getObjVal? "recovered_image")
        activationEpoch := ← json.getObjValAs? Epoch "activation_epoch"
      }
  | "DeleteStart" =>
      pure <| .deleteStart {}
  | "DeleteComplete" =>
      pure <| .deleteComplete {}
  | other =>
      throw s!"unknown event type: {other}"

def parseRecoveryTarget (json : Json) : Except String Effect.RecoveryTarget := do
  pure {
    osd := ← json.getObjValAs? OsdId "osd"
    peerLength := ← json.getObjValAs? Length "peer_length"
    authoritativeLength := ← json.getObjValAs? Length "authoritative_length"
    peerCommittedSeq := ← json.getObjValAs? JournalSeq "peer_committed_seq"
    authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
    recoveries := ← parseList (← json.getObjVal? "recoveries") parseObjRecovery
  }

def parseEffect (json : Json) : Except String PeeringEffect := do
  match (← json.getObjValAs? String "type") with
  | "SendQuery" =>
      pure <| .sendQuery {
        target := ← json.getObjValAs? OsdId "target"
        pgid := ← json.getObjValAs? PgId "pgid"
        epoch := ← json.getObjValAs? Epoch "epoch"
      }
  | "SendNotify" =>
      pure <| .sendNotify {
        target := ← json.getObjValAs? OsdId "target"
        pgid := ← json.getObjValAs? PgId "pgid"
        info := ← parsePeerInfo (← json.getObjVal? "info")
        epoch := ← json.getObjValAs? Epoch "epoch"
      }
  | "SendActivate" =>
      pure <| .sendActivate {
        target := ← json.getObjValAs? OsdId "target"
        pgid := ← json.getObjValAs? PgId "pgid"
        authInfo := ← parsePeerInfo (← json.getObjVal? "auth_info")
        authSources := ← parseAuthorityImage (← json.getObjVal? "auth_sources")
        authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
        activationEpoch := ← json.getObjValAs? Epoch "activation_epoch"
      }
  | "ActivatePG" =>
      pure <| .activatePG {
        pgid := ← json.getObjValAs? PgId "pgid"
        authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
        authoritativeLength := ← json.getObjValAs? Length "authoritative_length"
        authoritativeImage := ← parseObjectImage (← json.getObjVal? "authoritative_image")
        activationEpoch := ← json.getObjValAs? Epoch "activation_epoch"
      }
  | "DeactivatePG" =>
      pure <| .deactivatePG {
        pgid := ← json.getObjValAs? PgId "pgid"
      }
  | "ScheduleRecovery" =>
      pure <| .scheduleRecovery {
        pgid := ← json.getObjValAs? PgId "pgid"
        targets := ← parseList (← json.getObjVal? "targets") parseRecoveryTarget
      }
  | "CancelRecovery" =>
      pure <| .cancelRecovery {
        pgid := ← json.getObjValAs? PgId "pgid"
      }
  | "MarkClean" =>
      pure <| .markClean {
        pgid := ← json.getObjValAs? PgId "pgid"
      }
  | "PersistState" =>
      pure <| .persistState {
        pgid := ← json.getObjValAs? PgId "pgid"
        info := ← parsePGInfo (← json.getObjVal? "info")
      }
  | "RequestUpThru" =>
      pure <| .requestUpThru {
        epoch := ← json.getObjValAs? Epoch "epoch"
      }
  | "RequestActingChange" =>
      pure <| .requestActingChange {
        pgid := ← json.getObjValAs? PgId "pgid"
        wantActing := ← json.getObjValAs? (List OsdId) "want_acting"
      }
  | "UpdateHeartbeats" =>
      pure <| .updateHeartbeats {
        peers := ← json.getObjValAs? (List OsdId) "peers"
      }
  | "PublishStats" =>
      pure <| .publishStats {
        pgid := ← json.getObjValAs? PgId "pgid"
        state := ← parseStateName (← json.getObjValAs? String "state")
        committedSeq := ← json.getObjValAs? JournalSeq "committed_seq"
        authoritativeSeq := ← json.getObjValAs? JournalSeq "authoritative_seq"
        committedLength := ← json.getObjValAs? Length "committed_length"
        image := ← parseObjectImage (← json.getObjVal? "image")
        authoritativeImage := ← parseObjectImage (← json.getObjVal? "authoritative_image")
        actingSize := ← json.getObjValAs? Nat "acting_size"
        upSize := ← json.getObjValAs? Nat "up_size"
      }
  | "DeletePG" =>
      pure <| .deletePG {
        pgid := ← json.getObjValAs? PgId "pgid"
      }
  | "LogTransition" =>
      pure <| .logTransition {
        pgid := ← json.getObjValAs? PgId "pgid"
        fromState := ← parseStateName (← json.getObjValAs? String "from")
        toState := ← parseStateName (← json.getObjValAs? String "to")
        reason := ← json.getObjValAs? String "reason"
      }
  | other =>
      throw s!"unknown effect type: {other}"

def parseReplayLineJson (json : Json) : Except String ReplayLine := do
  match (← json.getObjValAs? String "kind") with
  | "step" =>
      pure <| .step {
        step := ← json.getObjValAs? Nat "step"
        fromState := ← parseStateName (← json.getObjValAs? String "from_state")
        toState := ← parseStateName (← json.getObjValAs? String "to_state")
        event := ← parseEvent (← json.getObjVal? "event")
        before := ← parseSnapshot (← json.getObjVal? "before")
        beforeChecks := ← parseSnapshotChecks (← json.getObjVal? "before_checks")
        after := ← parseSnapshot (← json.getObjVal? "after")
        afterChecks := ← parseSnapshotChecks (← json.getObjVal? "after_checks")
        effects := ← parseList (← json.getObjVal? "effects") parseEffect
      }
  | "summary" =>
      pure <| .summary {
        seed := ← json.getObjValAs? Nat "seed"
        events := ← json.getObjValAs? Nat "events"
      }
  | other =>
      throw s!"unknown replay line kind: {other}"

def parseReplayLine (line : String) : Except String (Option ReplayLine) := do
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    pure none
  else if !trimmed.startsWith "{" then
    pure none
  else
    let json ← Json.parse trimmed
    some <$> parseReplayLineJson json

def parseReplayLines (input : String) : Except String (List ReplayLine) := do
  let lines := input.splitOn "\n"
  let rec go (lineNo : Nat) (rest : List String) (acc : List ReplayLine) :
      Except String (List ReplayLine) :=
    match rest with
    | [] => pure acc.reverse
    | line :: tail =>
        match parseReplayLine line with
        | .ok none => go (lineNo + 1) tail acc
        | .ok (some parsed) => go (lineNo + 1) tail (parsed :: acc)
        | .error err => throw s!"line {lineNo}: {err}"
  go 1 lines []

def compareReplayStep (expected : ReplayStep) (actual : SnapshotStepResult) : Except String Unit := do
  let expectedBefore := normalizeSnapshot expected.before
  let actualBefore := normalizeSnapshot actual.before
  if actualBefore ≠ expectedBefore then
    throw s!"before snapshot mismatch at step {expected.step}\nexpected: {reprStr expectedBefore}\nactual: {reprStr actualBefore}"
  if actual.fromState ≠ expected.fromState then
    throw s!"from-state mismatch at step {expected.step}\nexpected: {reprStr expected.fromState}\nactual: {reprStr actual.fromState}"
  let expectedAfter := normalizeSnapshot expected.after
  let actualAfter := normalizeSnapshot actual.after
  if actualAfter ≠ expectedAfter then
    throw s!"after snapshot mismatch at step {expected.step}\nexpected: {reprStr expectedAfter}\nactual: {reprStr actualAfter}"
  if actual.toState ≠ expected.toState then
    throw s!"to-state mismatch at step {expected.step}\nexpected: {reprStr expected.toState}\nactual: {reprStr actual.toState}"
  let expectedEffects := normalizeEffects expected.effects
  let actualEffects := normalizeEffects actual.effects
  if actualEffects ≠ expectedEffects then
    throw s!"effects mismatch at step {expected.step}\nexpected: {reprStr expectedEffects}\nactual: {reprStr actualEffects}"

def replayObservedStep (cursor : ReplayCursor) (entry : ReplayStep) : Except String ReplayCursor := do
  let expectedBefore := normalizeSnapshot entry.before
  let actualBefore := normalizeSnapshot cursor.current
  if actualBefore ≠ expectedBefore then
    throw s!"input snapshot mismatch before step {entry.step}\ntrace: {reprStr expectedBefore}\nreplayed: {reprStr actualBefore}"
  let actual := step cursor.current entry.event
  compareReplayStep entry actual
  pure { current := normalizeSnapshot actual.after }

def replayLines (lines : List ReplayLine) : Except String ReplayCursor := do
  lines.foldlM
    (fun cursor line =>
      match line with
      | .step item =>
          replayObservedStep cursor item
      | .summary _ =>
          pure cursor)
    {}

def replayStats (lines : List ReplayLine) : ReplayStats :=
  lines.foldl
    (fun stats line =>
      match line with
      | .step _ => { stats with steps := stats.steps + 1 }
      | .summary _ => { stats with summaries := stats.summaries + 1 })
    {}

def replayTrace (input : String) : Except String (ReplayStats × ReplayCursor) := do
  let lines ← parseReplayLines input
  let cursor ← replayLines lines
  pure (replayStats lines, cursor)

end Peering
