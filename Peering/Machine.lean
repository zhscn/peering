import Peering.Image

namespace Peering

structure Snapshot where
  state : State := .initial
  pgid : PgId := 0
  whoami : OsdId := -1
  epoch : Epoch := 0
  acting : ActingSet := {}
  up : ActingSet := {}
  poolSize : Nat := 0
  poolMinSize : Nat := 0
  localInfo : PGInfo := {}
  authSeq : JournalSeq := 0
  authImage : ObjectImage := {}
  authSources : AuthorityImage := {}
  peerInfo : List (OsdId × PeerInfo) := []
  peersQueried : List OsdId := []
  peersResponded : List OsdId := []
  priorOsds : List OsdId := []
  peerRecoveryPlans : List PeerRecoveryPlan := []
  localRecoveryPlan : List ObjRecovery := []
  recovered : List OsdId := []
  timedOutProbes : List OsdId := []
  needUpThru : Bool := false
  activated : Bool := false
  pendingActingChange : Bool := false
  lastPeeringReset : Epoch := 0
  deriving DecidableEq, Repr

structure SnapshotStepResult where
  before : Snapshot
  after : Snapshot
  fromState : State
  toState : State
  effects : List PeeringEffect
  deriving DecidableEq, Repr

namespace Snapshot

def isPrimary (snap : Snapshot) : Bool :=
  decide (snap.acting.primary = some snap.whoami)

def isActive (snap : Snapshot) : Bool :=
  decide (snap.state = .active || snap.state = .recovering ||
    snap.state = .clean || snap.state = .replicaActive)

end Snapshot

def osdNonneg (osd : OsdId) : Bool :=
  decide (osd >= 0)

def boolAnd (xs : List Bool) : Bool :=
  xs.foldl (· && ·) true

def osdSetInsert (xs : List OsdId) (osd : OsdId) : List OsdId :=
  if osd ∈ xs then xs else osd :: xs

def osdSetUnion (xs ys : List OsdId) : List OsdId :=
  ys.foldl osdSetInsert xs

def osdSetEq (xs ys : List OsdId) : Bool :=
  boolAnd ((xs.eraseDups.map fun osd => decide (osd ∈ ys)) ++
    (ys.eraseDups.map fun osd => decide (osd ∈ xs)))

def lookupPeerInfo : List (OsdId × PeerInfo) → OsdId → Option PeerInfo
  | [], _ => none
  | (key, value) :: rest, osd =>
      if key = osd then some value else lookupPeerInfo rest osd

def insertPeerInfo (entries : List (OsdId × PeerInfo))
    (osd : OsdId) (info : PeerInfo) : List (OsdId × PeerInfo) :=
  (osd, info) :: entries.filter (fun entry => entry.1 ≠ osd)

def upsertRecoveredPeerInfo (entries : List (OsdId × PeerInfo))
    (osd : OsdId) (authSeq : JournalSeq) (authImage : ObjectImage) :
    List (OsdId × PeerInfo) :=
  let updated :=
    match lookupPeerInfo entries osd with
    | some info =>
        let normalized := normalizedPeerInfo info
        { normalized with
          osd := osd
          committedSeq := authSeq
          committedLength := primaryLength authImage
          image := authImage }
    | none =>
        { osd := osd
          committedSeq := authSeq
          committedLength := primaryLength authImage
          image := authImage }
  insertPeerInfo entries osd updated

def prefixImage? (lhs rhs : ObjectImage) : Bool :=
  (ObjectImage.support lhs).all fun obj =>
    lookupLength lhs obj ≤ lookupLength rhs obj

def sameImage? (lhs rhs : ObjectImage) : Bool :=
  prefixImage? lhs rhs && prefixImage? rhs lhs

def authorityImageEmpty (auth : AuthorityImage) : Bool :=
  auth.entries.isEmpty

def objectImageEmpty (img : ObjectImage) : Bool :=
  img.entries.isEmpty

def recoveryTargetsFromPlans (peerPlans : List PeerRecoveryPlan)
    (localPlan : List ObjRecovery)
    (localCommittedSeq authoritativeSeq : JournalSeq)
    (whoami : OsdId) : List OsdId :=
  let peerTargets := peerPlans.map PeerRecoveryPlan.target
  if localPlan.isEmpty && localCommittedSeq >= authoritativeSeq then
    peerTargets.eraseDups
  else
    osdSetInsert peerTargets.eraseDups whoami

def knownPeerImages (snap : Snapshot) : List PeerInfo :=
  let remote :=
    snap.peerInfo.foldr
      (fun (entry : OsdId × PeerInfo) acc =>
        if entry.1 = snap.whoami then
          acc
        else
          let info := normalizedPeerInfo entry.2
          { info with osd := entry.1 } :: acc)
      []
  let localInfo := normalizedPGInfo snap.localInfo
  remote ++ [{
    osd := snap.whoami
    committedSeq := localInfo.committedSeq
    committedLength := localInfo.committedLength
    image := localInfo.image
    lastEpochStarted := localInfo.lastEpochStarted
    lastIntervalStarted := localInfo.lastIntervalStarted
  }]

def actingReplicaImages (snap : Snapshot) : List PeerInfo :=
  snap.acting.osds.foldr
    (fun osd acc =>
      if !osdNonneg osd || osd = snap.whoami then
        acc
      else
        match lookupPeerInfo snap.peerInfo osd with
        | some info =>
            let normalized := normalizedPeerInfo info
            { normalized with osd := osd } :: acc
        | none =>
            { osd := osd } :: acc)
    []

def refreshAuthorityFromKnownPeers (snap : Snapshot) : Snapshot :=
  let known := knownPeerImages snap
  let authSources := authoritativeSources known
  { snap with
    authSeq := authoritativeCommittedSeq known
    authSources := authSources
    authImage := authorityImageValues authSources }

def refreshRecoveryPlansFromCurrentAuthority (snap : Snapshot) : Snapshot :=
  let localInfo := normalizedPGInfo snap.localInfo
  { snap with
    peerRecoveryPlans := buildPeerRecoveryPlans snap.authSources snap.authSeq
      (actingReplicaImages snap)
    localRecoveryPlan := pgImageRecoveryPlan snap.authSources localInfo }

def refreshImageStateFromKnownPeers (snap : Snapshot) : Snapshot :=
  refreshRecoveryPlansFromCurrentAuthority (refreshAuthorityFromKnownPeers snap)

def imageRecoveryTargets (snap : Snapshot) : List OsdId :=
  recoveryTargetsFromPlans snap.peerRecoveryPlans snap.localRecoveryPlan
    snap.localInfo.committedSeq snap.authSeq snap.whoami

def isImageRecoveryTarget (snap : Snapshot) (peer : OsdId) : Bool :=
  decide (peer ∈ imageRecoveryTargets snap)

def buildProbeSet (snap : Snapshot) : List OsdId :=
  let actingPeers :=
    snap.acting.osds.foldl
      (fun acc osd =>
        if osdNonneg osd && osd ≠ snap.whoami then osdSetInsert acc osd else acc)
      []
  let upPeers :=
    snap.up.osds.foldl
      (fun acc osd =>
        if osdNonneg osd && osd ≠ snap.whoami then osdSetInsert acc osd else acc)
      actingPeers
  snap.priorOsds.foldl
    (fun acc osd =>
      if osdNonneg osd && osd ≠ snap.whoami then osdSetInsert acc osd else acc)
    upPeers

def haveEnoughInfo (snap : Snapshot) : Bool :=
  boolAnd (snap.peersQueried.map fun osd => decide (osd ∈ snap.peersResponded)) &&
    boolAnd (snap.acting.osds.map fun osd =>
      if osdNonneg osd && osd ≠ snap.whoami then
        decide (osd ∈ snap.peersResponded)
      else
        true)

def effectPersist (snap : Snapshot) : PeeringEffect :=
  .persistState {
    pgid := snap.pgid
    info := normalizedPGInfo snap.localInfo
  }

def effectPublishStats (snap : Snapshot) : PeeringEffect :=
  .publishStats {
    pgid := snap.pgid
    state := snap.state
    committedSeq := snap.localInfo.committedSeq
    authoritativeSeq := snap.authSeq
    committedLength := primaryLength (effectivePGImage snap.localInfo)
    image := effectivePGImage snap.localInfo
    authoritativeImage := snap.authImage
    actingSize := snap.acting.size
    upSize := snap.up.size
  }

def transitionTo (snap : Snapshot) (newState : State) (reason : String) :
    Snapshot × List PeeringEffect :=
  if snap.state = newState then
    (snap, [])
  else
    ({ snap with state := newState }, [
      .logTransition {
        pgid := snap.pgid
        fromState := snap.state
        toState := newState
        reason := reason
      }
    ])

def resetPeeringState (snap : Snapshot) : Snapshot :=
  { snap with
    peerInfo := []
    peersQueried := []
    peersResponded := []
    priorOsds := []
    authSeq := 0
    authImage := {}
    authSources := {}
    peerRecoveryPlans := []
    localRecoveryPlan := []
    recovered := []
    timedOutProbes := []
    needUpThru := false
    activated := false
    pendingActingChange := false }

def sendQueries (snap : Snapshot) : Snapshot × List PeeringEffect :=
  let probes := buildProbeSet snap
  probes.foldl
    (fun (accSnap, accFx) osd =>
      if osd ∈ accSnap.peersResponded || osd ∈ accSnap.peersQueried then
        (accSnap, accFx)
      else
        ({ accSnap with peersQueried := osdSetInsert accSnap.peersQueried osd },
         accFx ++ [.sendQuery { target := osd, pgid := accSnap.pgid, epoch := accSnap.epoch }]))
    (snap, [])

def tryActivate (snap : Snapshot) : Snapshot × List PeeringEffect :=
  if snap.pendingActingChange then
    (snap, [])
  else
    let available :=
      snap.acting.osds.foldl
        (fun count osd =>
          if osdNonneg osd && (lookupPeerInfo snap.peerInfo osd).isSome then
            count + 1
          else
            count)
        0
    if available < snap.poolMinSize then
      let (snap', fx) := transitionTo snap .down "min_size check failed at activation"
      (snap', fx ++ [effectPublishStats snap'])
    else
      let clampLocalToAuth :=
        snap.localInfo.committedSeq >= snap.authSeq &&
          prefixImage? snap.authImage (effectivePGImage snap.localInfo)
      let activateReplicas :=
        snap.acting.osds.filter (fun osd => osdNonneg osd && osd ≠ snap.whoami)
      let peerTargets :=
        snap.peerRecoveryPlans.map fun plan =>
          let peerLength :=
            match lookupPeerInfo snap.peerInfo plan.target with
            | some info => primaryLength (effectivePeerImage info)
            | none => 0
          let peerSeq :=
            match lookupPeerInfo snap.peerInfo plan.target with
            | some info => info.committedSeq
            | none => 0
          {
            osd := plan.target
            peerLength := peerLength
            authoritativeLength := primaryLength snap.authImage
            peerCommittedSeq := peerSeq
            authoritativeSeq := snap.authSeq
            recoveries := plan.recoveries
          }
      let localTargets :=
        if snap.localRecoveryPlan.isEmpty && snap.localInfo.committedSeq >= snap.authSeq then
          []
        else
          [{
            osd := snap.whoami
            peerLength := primaryLength (effectivePGImage snap.localInfo)
            authoritativeLength := primaryLength snap.authImage
            peerCommittedSeq := snap.localInfo.committedSeq
            authoritativeSeq := snap.authSeq
            recoveries := snap.localRecoveryPlan
          }]
      let recoveryTargets := peerTargets ++ localTargets
      let localInfo :=
        let updated := {
          snap.localInfo with
            lastEpochStarted := snap.epoch
            lastIntervalStarted := snap.epoch
        }
        if clampLocalToAuth then
          {
            updated with
              image := snap.authImage
              committedSeq := snap.authSeq
              committedLength := primaryLength snap.authImage
          }
        else
          updated
      let snap := refreshRecoveryPlansFromCurrentAuthority { snap with localInfo := localInfo }
      let (snap, transitionFx) := transitionTo snap .active "peering complete"
      let activateFx := activateReplicas.map fun osd =>
        .sendActivate {
          target := osd
          pgid := snap.pgid
          authInfo := {
            osd := snap.whoami
            committedSeq := snap.authSeq
            committedLength := primaryLength snap.authImage
            image := snap.authImage
            lastEpochStarted := snap.epoch
            lastIntervalStarted := snap.epoch
          }
          authSources := snap.authSources
          authoritativeSeq := snap.authSeq
          activationEpoch := snap.epoch
        }
      let baseFx :=
        transitionFx ++
        activateFx ++
        [.activatePG {
          pgid := snap.pgid
          authoritativeSeq := snap.authSeq
          authoritativeLength := primaryLength snap.authImage
          authoritativeImage := snap.authImage
          activationEpoch := snap.epoch
        },
        effectPersist snap,
        effectPublishStats snap]
      if recoveryTargets.isEmpty then
        let (snap, cleanFx) := transitionTo snap .clean "all replicas up to date"
        (snap, baseFx ++ cleanFx ++ [.markClean { pgid := snap.pgid }])
      else
        let (snap, recoveringFx) := transitionTo snap .recovering "replicas need recovery"
        (snap, baseFx ++ recoveringFx ++ [.scheduleRecovery {
          pgid := snap.pgid
          targets := recoveryTargets
        }])

def chooseActing (snap : Snapshot) : Snapshot × List PeeringEffect :=
  let localInfo := normalizedPGInfo snap.localInfo
  let peers := snap.peerInfo.map fun entry => (entry.1, normalizedPeerInfo entry.2)
  let known := knownPeerImages { snap with localInfo := localInfo, peerInfo := peers }
  if known.isEmpty then
    let (snap', fx) := transitionTo snap .incomplete "no valid peer info"
    (snap', fx ++ [effectPublishStats snap'])
  else
    let authSeq := authoritativeCommittedSeq known
    let authSources := authoritativeSources known
    let authImage := authorityImageValues authSources
    let peerRecoveryPlans := buildPeerRecoveryPlans authSources authSeq
      (actingReplicaImages { snap with peerInfo := peers })
    let localRecoveryPlan := pgImageRecoveryPlan authSources localInfo
    let snap := { snap with
      authSeq := authSeq
      authSources := authSources
      authImage := authImage
      peerRecoveryPlans := peerRecoveryPlans
      localRecoveryPlan := localRecoveryPlan }
    let priorTimedOut := snap.timedOutProbes.any fun osd =>
      decide (osd ∈ snap.priorOsds) && (lookupPeerInfo snap.peerInfo osd).isNone
    if priorTimedOut then
      let (snap', fx) := transitionTo snap .down "prior-interval probe timed out"
      (snap', fx ++ [effectPublishStats snap'])
    else
      let desiredPrimary := snap.acting.primary.getD snap.whoami
      let addPeer := fun (acc : List OsdId × List OsdId) (osd : OsdId) =>
        let (want, inWant) := acc
        if !osdNonneg osd || decide (osd ∈ inWant) || want.length >= snap.poolSize then
          (want, inWant)
        else if lookupPeerInfo snap.peerInfo osd |>.isNone then
          (want, inWant)
        else
          (want ++ [osd], osdSetInsert inWant osd)
      let isCompletePeer := fun (osd : OsdId) =>
        match lookupPeerInfo snap.peerInfo osd with
        | some info =>
            info.committedSeq >= authSeq &&
              sameImage? (effectivePeerImage info) authImage
        | none => false
      let seedWant : List OsdId := [desiredPrimary]
      let seedSeen : List OsdId := [desiredPrimary]
      let completePass :=
        (snap.acting.osds ++ snap.up.osds ++ snap.priorOsds).foldl
          (fun acc osd => if isCompletePeer osd then addPeer acc osd else acc)
          (seedWant, seedSeen)
      let (wantActing, _) :=
        (snap.acting.osds ++ snap.up.osds ++ snap.priorOsds).foldl addPeer completePass
      let available := wantActing.length
      if available < snap.poolMinSize then
        if available = 0 then
          let (snap', fx) := transitionTo snap .incomplete "no peers available"
          (snap', fx ++ [effectPublishStats snap'])
        else
          let (snap', fx) := transitionTo snap .down "insufficient peers for min_size"
          (snap', fx ++ [effectPublishStats snap'])
      else
        let needActingChange := wantActing.any fun osd => !(snap.acting.contains osd)
        if needActingChange then
          ({ snap with pendingActingChange := true }, [
            .requestActingChange { pgid := snap.pgid, wantActing := wantActing }
          ])
        else if snap.localInfo.lastIntervalStarted < snap.epoch then
          let snap := { snap with pendingActingChange := false, needUpThru := true }
          let (snap', fx) := transitionTo snap .waitUpThru "need up_thru"
          (snap', fx ++ [.requestUpThru { epoch := snap'.epoch }])
        else
          tryActivate { snap with pendingActingChange := false }

def startPeeringPrimary (snap : Snapshot) (priorOsds : List OsdId) :
    Snapshot × List PeeringEffect :=
  let prior :=
    priorOsds.foldl
      (fun acc osd =>
        if osdNonneg osd && osd ≠ snap.whoami then osdSetInsert acc osd else acc)
      []
  let (snap, transitionFx) := transitionTo { snap with priorOsds := prior }
    .getPeerInfo "start peering as primary"
  let selfInfo : PeerInfo := {
    osd := snap.whoami
    committedSeq := snap.localInfo.committedSeq
    committedLength := snap.localInfo.committedLength
    image := effectivePGImage snap.localInfo
    lastEpochStarted := snap.localInfo.lastEpochStarted
    lastIntervalStarted := snap.localInfo.lastIntervalStarted
  }
  let snap :=
    refreshImageStateFromKnownPeers {
      snap with
        peerInfo := insertPeerInfo snap.peerInfo snap.whoami selfInfo
        peersResponded := osdSetInsert snap.peersResponded snap.whoami
    }
  let (snap, queryFx) := sendQueries snap
  let fx := transitionFx ++ queryFx
  if haveEnoughInfo snap then
    let (snap, chooseFx) := chooseActing snap
    (snap, fx ++ chooseFx)
  else
    (snap, fx)

def onInitialize (snap : Snapshot) (e : Event.Initialize) :
    Snapshot × List PeeringEffect :=
  let base : Snapshot := {
    state := snap.state
    pgid := e.pgid
    whoami := e.whoami
    epoch := e.epoch
    acting := e.acting
    up := e.up
    poolSize := e.poolSize
    poolMinSize := e.poolMinSize
    localInfo := normalizedPGInfo e.localInfo
  }
  let base := refreshImageStateFromKnownPeers (resetPeeringState base)
  let base := { base with lastPeeringReset := e.epoch }
  let (snap, fx) :=
    if e.acting.primary = some e.whoami then
      startPeeringPrimary base e.priorOsds
    else
      transitionTo base .stray
        (if e.acting.contains e.whoami then "initialize as replica"
         else "initialize as stray")
  (snap, fx ++ [.updateHeartbeats { peers := snap.acting.osds }])

def onPeerInfoReceived (snap : Snapshot) (e : Event.PeerInfoReceived) :
    Snapshot × List PeeringEffect :=
  let allowed :=
    decide (e.sender ∈ snap.peersQueried) ||
    snap.acting.contains e.sender ||
    snap.up.contains e.sender ||
    decide (e.sender ∈ snap.priorOsds)
  if !allowed then
    (snap, [])
  else if e.queryEpoch > 0 && e.queryEpoch < snap.lastPeeringReset then
    (snap, [])
  else
    let info := normalizedPeerInfo { e.info with osd := e.sender }
    let snap := refreshImageStateFromKnownPeers {
      snap with
        peerInfo := insertPeerInfo snap.peerInfo e.sender info
        peersResponded := osdSetInsert snap.peersResponded e.sender
    }
    if snap.state = .down || snap.state = .incomplete || snap.state = .waitUpThru then
      chooseActing snap
    else if snap.state ≠ .getPeerInfo then
      (snap, [])
    else
      let enoughInfo :=
        boolAnd (snap.peersQueried.map fun osd =>
          if osd = e.sender then true else decide (osd ∈ snap.peersResponded)) &&
        boolAnd (snap.acting.osds.map fun osd =>
          if osdNonneg osd && osd ≠ snap.whoami && osd ≠ e.sender then
            decide (osd ∈ snap.peersResponded)
          else
            true)
      if enoughInfo then chooseActing snap else (snap, [])

def onPeerQueryTimeout (snap : Snapshot) (e : Event.PeerQueryTimeout) :
    Snapshot × List PeeringEffect :=
  if snap.state ≠ .getPeerInfo then
    (snap, [])
  else
    let enoughInfo :=
      boolAnd (snap.peersQueried.map fun osd =>
        if osd = e.peer then true else decide (osd ∈ snap.peersResponded)) &&
      boolAnd (snap.acting.osds.map fun osd =>
        if osdNonneg osd && osd ≠ snap.whoami && osd ≠ e.peer then
          decide (osd ∈ snap.peersResponded)
        else
          true)
    let snap := {
      snap with
        peersResponded := osdSetInsert snap.peersResponded e.peer
        timedOutProbes := osdSetInsert snap.timedOutProbes e.peer
    }
    if enoughInfo then chooseActing snap else (snap, [])

def onUpThruUpdated (snap : Snapshot) (e : Event.UpThruUpdated) :
    Snapshot × List PeeringEffect :=
  if snap.state ≠ .waitUpThru || e.epoch ≠ snap.epoch then
    (snap, [])
  else
    let localInfo :=
      if snap.localInfo.lastIntervalStarted < snap.epoch then
        { snap.localInfo with lastIntervalStarted := snap.epoch }
      else
        snap.localInfo
    tryActivate { snap with needUpThru := false, localInfo := localInfo }

def onActivateCommitted (snap : Snapshot) :
    Snapshot × List PeeringEffect :=
  if snap.isActive then
    let snap := { snap with activated := true }
    (snap, [effectPersist snap])
  else
    (snap, [])

def onRecoveryComplete (snap : Snapshot) (e : Event.RecoveryComplete) :
    Snapshot × List PeeringEffect :=
  if snap.state ≠ .recovering then
    (snap, [])
  else if e.epoch < snap.lastPeeringReset || !isImageRecoveryTarget snap e.peer then
    (snap, [])
  else
    let completed := osdSetInsert snap.recovered e.peer
    let clean := osdSetEq completed (imageRecoveryTargets snap)
    let peerInfo :=
      upsertRecoveredPeerInfo snap.peerInfo e.peer snap.authSeq snap.authImage
    let localInfo :=
      if e.peer = snap.whoami then
        {
          snap.localInfo with
            image := snap.authImage
            committedSeq := snap.authSeq
            committedLength := primaryLength snap.authImage
        }
      else
        snap.localInfo
    let snap := refreshRecoveryPlansFromCurrentAuthority {
      snap with peerInfo := peerInfo, localInfo := localInfo, recovered := completed
    }
    if clean then
      let snap := { snap with peerRecoveryPlans := [], localRecoveryPlan := [], recovered := [] }
      let (snap, fx) := transitionTo snap .clean "all replicas recovered"
      (snap, fx ++ [.markClean { pgid := snap.pgid }, effectPersist snap, effectPublishStats snap])
    else
      (snap, [])

def onAllReplicasRecovered (snap : Snapshot) (e : Event.AllReplicasRecovered) :
    Snapshot × List PeeringEffect :=
  if snap.state ≠ .recovering && snap.state ≠ .active then
    (snap, [])
  else if e.epoch < snap.lastPeeringReset then
    (snap, [])
  else if !boolAnd (e.peers.map fun peer => isImageRecoveryTarget snap peer) then
    (snap, [])
  else
    let completed := osdSetUnion snap.recovered e.peers
    if !osdSetEq completed (imageRecoveryTargets snap) then
      (snap, [])
    else
      let peerInfo :=
        e.peers.foldl
          (fun entries peer =>
            upsertRecoveredPeerInfo entries peer snap.authSeq snap.authImage)
          snap.peerInfo
      let localInfo := {
        snap.localInfo with
          image := snap.authImage
          committedSeq := snap.authSeq
          committedLength := primaryLength snap.authImage
      }
      let snap := {
        refreshRecoveryPlansFromCurrentAuthority {
          snap with
            peerInfo := peerInfo
            localInfo := localInfo
            recovered := completed
        } with
        peerRecoveryPlans := []
        localRecoveryPlan := []
        recovered := []
      }
      let (snap, fx) := transitionTo snap .clean "all replicas recovered (batch)"
      (snap, fx ++ [.markClean { pgid := snap.pgid }, effectPersist snap, effectPublishStats snap])

def onReplicaActivate (snap : Snapshot) (e : Event.ReplicaActivate) :
    Snapshot × List PeeringEffect :=
  if snap.state ≠ .stray && snap.state ≠ .replicaActive then
    (snap, [])
  else if !(snap.acting.contains snap.whoami) then
    (snap, [])
  else if e.activationEpoch ≠ snap.epoch || e.sender ≠ snap.acting.primary.getD (-1) then
    (snap, [])
  else
    let authInfo := normalizedPeerInfo e.authInfo
    let authSeq := if e.authoritativeSeq > 0 then e.authoritativeSeq else authInfo.committedSeq
    let authSources :=
      if authorityImageEmpty e.authSources then authorityFromPeerInfo authInfo else e.authSources
    let authImage :=
      if authorityImageEmpty authSources then authInfo.image else authorityImageValues authSources
    let advanceHistory :=
      authSeq ≤ snap.localInfo.committedSeq &&
        prefixImage? authImage (effectivePGImage snap.localInfo)
    let localImage := clampImageTo authImage (effectivePGImage snap.localInfo)
    let localCommittedSeq :=
      if advanceHistory then authSeq else min snap.localInfo.committedSeq authSeq
    let localInfo := {
      snap.localInfo with
        image := localImage
        committedSeq := localCommittedSeq
        committedLength := primaryLength localImage
        lastEpochStarted :=
          if advanceHistory then e.activationEpoch else snap.localInfo.lastEpochStarted
        lastIntervalStarted :=
          if advanceHistory then e.activationEpoch else snap.localInfo.lastIntervalStarted
    }
    let snap := refreshRecoveryPlansFromCurrentAuthority {
      snap with
        authSeq := authSeq
        authSources := authSources
        authImage := authImage
        localInfo := localInfo
    }
    let (snap, fx) := transitionTo snap .replicaActive "activated by primary"
    (snap, fx ++ [effectPersist snap, effectPublishStats snap])

def onReplicaRecoveryComplete (snap : Snapshot)
    (e : Event.ReplicaRecoveryComplete) : Snapshot × List PeeringEffect :=
  if snap.state ≠ .replicaActive then
    (snap, [])
  else if e.activationEpoch < snap.lastPeeringReset then
    (snap, [])
  else
    let recoveredImage :=
      if objectImageEmpty e.recoveredImage && e.newCommittedLength > 0 then
        primaryImage e.newCommittedLength
      else
        e.recoveredImage
    let merged := joinImage (effectivePGImage snap.localInfo) recoveredImage
    let clamped := clampImageTo snap.authImage merged
    let recoveredSeq :=
      if e.newCommittedSeq = 0 && !objectImageEmpty recoveredImage &&
          sameImage? recoveredImage snap.authImage then
        snap.authSeq
      else
        e.newCommittedSeq
    if !prefixImage? (effectivePGImage snap.localInfo) clamped then
      (snap, [])
    else if e.activationEpoch < snap.localInfo.lastEpochStarted then
      (snap, [])
    else if recoveredSeq < snap.localInfo.committedSeq || recoveredSeq > snap.authSeq then
      (snap, [])
    else
      let snap := refreshRecoveryPlansFromCurrentAuthority {
        snap with
          localInfo := {
            snap.localInfo with
              image := clamped
              committedSeq := recoveredSeq
              committedLength := primaryLength clamped
              lastEpochStarted := e.activationEpoch
              lastIntervalStarted := e.activationEpoch
          }
      }
      (snap, [effectPersist snap, effectPublishStats snap])

def onDeleteStart (snap : Snapshot) : Snapshot × List PeeringEffect :=
  let baseFx :=
    (if snap.isActive then [.deactivatePG { pgid := snap.pgid }] else []) ++
    (if snap.state == .recovering then [.cancelRecovery { pgid := snap.pgid }] else [])
  let (snap, fx) := transitionTo snap .deleting "delete requested"
  (snap, baseFx ++ fx ++ [.deletePG { pgid := snap.pgid }])

def reduceValidated (snap : Snapshot) (event : ValidatedEvent) :
    Snapshot × List PeeringEffect :=
  match event with
  | .initialize e => onInitialize snap e
  | .peerInfoReceived e => onPeerInfoReceived snap e
  | .peerQueryTimeout e => onPeerQueryTimeout snap e
  | .upThruUpdated e => onUpThruUpdated snap e
  | .activateCommitted _ => onActivateCommitted snap
  | .recoveryComplete e => onRecoveryComplete snap e
  | .allReplicasRecovered e => onAllReplicasRecovered snap e
  | .replicaActivate e => onReplicaActivate snap e
  | .replicaRecoveryComplete e => onReplicaRecoveryComplete snap e
  | .deleteStart _ => onDeleteStart snap
  | .advanceMap _ | .deleteComplete _ => (snap, [])

def isFreshEpoch (reset msgEpoch : Epoch) : Bool :=
  msgEpoch = 0 || msgEpoch >= reset

def validateEvent (reset : Epoch) (event : PeeringEvent) : Option ValidatedEvent :=
  match event with
  | .peerInfoReceived e =>
      if isFreshEpoch reset e.queryEpoch then some (.peerInfoReceived e) else none
  | .recoveryComplete e =>
      if isFreshEpoch reset e.epoch then some (.recoveryComplete e) else none
  | .allReplicasRecovered e =>
      if isFreshEpoch reset e.epoch then some (.allReplicasRecovered e) else none
  | .replicaActivate e =>
      if isFreshEpoch reset e.activationEpoch then some (.replicaActivate e) else none
  | .replicaRecoveryComplete e =>
      if isFreshEpoch reset e.activationEpoch then
        some (.replicaRecoveryComplete e)
      else
        none
  | other => some other

def stepWithValidated (snapshot : Snapshot)
    (validatedEvent : ValidatedEvent) : SnapshotStepResult :=
  let fromState := snapshot.state
  let (after, effects) := reduceValidated snapshot validatedEvent
  {
    before := snapshot
    after := after
    fromState := fromState
    toState := after.state
    effects := effects
  }

def step (snapshot : Snapshot) (event : PeeringEvent) : SnapshotStepResult :=
  match validateEvent snapshot.lastPeeringReset event with
  | some validated => stepWithValidated snapshot validated
  | none =>
      {
        before := snapshot
        after := snapshot
        fromState := snapshot.state
        toState := snapshot.state
        effects := []
      }

end Peering
