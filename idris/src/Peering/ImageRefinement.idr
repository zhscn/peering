||| Refinement surface for the native image-aware reducer.
|||
||| This module defines the objectwise snapshot that replay compares against and
||| the executable agreement check between that snapshot and an `ImageContext`.
module Peering.ImageRefinement

import Data.List
import Data.SortedMap
import Peering.Types
import Peering.ObjectImage
import Peering.ImageMachine
import Peering.ImageInvariants
import Peering.ImageProcess

%default total

subsetOf : Eq a => List a -> List a -> Bool
subsetOf xs ys = all (\x => elem x ys) xs

export
sameMembers : Eq a => List a -> List a -> Bool
sameMembers xs ys =
  let xs' = nub xs
      ys' = nub ys
  in subsetOf xs' ys' && subsetOf ys' xs'

||| Semantic comparison for local PG summaries. This is intentionally more
||| permissive than structural equality: it accepts monotone progress in the
||| epoch-tracking fields while requiring the same semantic image.
export
pgImageInfoEquivalent : PGImageInfo -> PGImageInfo -> Bool
pgImageInfoEquivalent expected actual =
  expected.pgid == actual.pgid
  && sameImage expected.image actual.image
  && expected.lastEpochClean == actual.lastEpochClean
  && expected.lastEpochStarted <= actual.lastEpochStarted
  && expected.lastIntervalStarted <= actual.lastIntervalStarted

||| Backwards-compatible alias for the older local-summary semantic predicate.
export
localInfoEquivalent : PGImageInfo -> PGImageInfo -> Bool
localInfoEquivalent = pgImageInfoEquivalent

export
peerImageEquivalent : PeerImageInfo -> PeerImageInfo -> Bool
peerImageEquivalent expected actual =
  expected.osd == actual.osd
  && prefixImage expected.image actual.image
  && expected.lastEpochStarted <= actual.lastEpochStarted

export
samePeerImagesEquivalent : List PeerImageInfo -> List PeerImageInfo -> Bool
samePeerImagesEquivalent expected actual =
  let normExpected = normalizePeerImages expected
      normActual = normalizePeerImages actual
  in length normExpected == length normActual
     && all (\(exp, act) => peerImageEquivalent exp act) (zip normExpected normActual)

public export
record ImageObservedSnapshot where
  constructor MkImageObservedSnapshot
  snapPgid              : PgId
  snapWhoami            : OsdId
  snapEpoch             : Epoch
  snapActing            : ActingSet
  snapUp                : ActingSet
  snapPool              : PoolParams
  snapLocalInfo         : PGImageInfo
  snapAuthImage         : ObjectImage
  snapAuthSources       : List (ObjectId, ObjectAuthority)
  snapPeerImages        : List PeerImageInfo
  snapPeersQueried      : List OsdId
  snapPeersResponded    : List OsdId
  snapPriorOsds         : List OsdId
  snapPeerRecoveryPlans : List PeerRecoveryPlan
  snapLocalRecoveryPlan : List ObjRecovery
  snapRecovered         : List OsdId
  snapTimedOutProbes    : List OsdId
  snapNeedUpThru        : Bool
  snapActivated         : Bool
  snapPendingActChange  : Bool
  snapLastPeeringReset  : Epoch
  snapHaveEnoughInfo    : Bool
  snapImageInvariant    : Bool
  snapImageClean        : Bool
  snapImageRecovering   : Bool

||| Replay/debug snapshot surface used by stdin/stdout integration and local
||| mismatch reporting.
public export
ImageReplaySnapshot : Type
ImageReplaySnapshot = ImageObservedSnapshot

||| Smaller proof-facing snapshot used for observable-state refinement.
||| This intentionally excludes replay-only bookkeeping fields and serves as
||| the semantic snapshot surface for typed refinement.
public export
record ObservableImageSnapshot where
  constructor MkObservableImageSnapshot
  proofPgid              : PgId
  proofWhoami            : OsdId
  proofEpoch             : Epoch
  proofActing            : ActingSet
  proofUp                : ActingSet
  proofPool              : PoolParams
  proofLocalInfo         : PGImageInfo
  proofPeerImages        : List PeerImageInfo
  proofAuthImage         : ObjectImage
  proofPeerRecoveryPlans : List PeerRecoveryPlan
  proofLocalRecoveryPlan : List ObjRecovery
  proofActivated         : Bool

||| Semantic proof snapshot surface used by typed replay/refinement theorems.
public export
ImageSemanticSnapshot : Type
ImageSemanticSnapshot = ObservableImageSnapshot

export
normalizeObservableSnapshot : ObservableImageSnapshot -> ObservableImageSnapshot
normalizeObservableSnapshot snap =
  MkObservableImageSnapshot snap.proofPgid
                            snap.proofWhoami
                            snap.proofEpoch
                            snap.proofActing
                            snap.proofUp
                            snap.proofPool
                            snap.proofLocalInfo
                            (normalizeObservablePeerImages snap.proofPeerImages)
                            snap.proofAuthImage
                            (normalizeObservablePeerRecoveryPlans snap.proofPeerRecoveryPlans)
                            (normalizeObservableRecoveries snap.proofLocalRecoveryPlan)
                            snap.proofActivated

||| Explicit semantic-snapshot canonicalization entrypoint.
export
normalizeSemanticSnapshot : ImageSemanticSnapshot -> ImageSemanticSnapshot
normalizeSemanticSnapshot = normalizeObservableSnapshot

export
normalizeObservedSnapshot : ImageObservedSnapshot -> ImageObservedSnapshot
normalizeObservedSnapshot snap =
  MkImageObservedSnapshot snap.snapPgid
                          snap.snapWhoami
                          snap.snapEpoch
                          snap.snapActing
                          snap.snapUp
                          snap.snapPool
                          snap.snapLocalInfo
                          snap.snapAuthImage
                          snap.snapAuthSources
                          (normalizeObservablePeerImages snap.snapPeerImages)
                          snap.snapPeersQueried
                          snap.snapPeersResponded
                          snap.snapPriorOsds
                          (normalizeObservablePeerRecoveryPlans snap.snapPeerRecoveryPlans)
                          (normalizeObservableRecoveries snap.snapLocalRecoveryPlan)
                          snap.snapRecovered
                          snap.snapTimedOutProbes
                          snap.snapNeedUpThru
                          snap.snapActivated
                          snap.snapPendingActChange
                          snap.snapLastPeeringReset
                          snap.snapHaveEnoughInfo
                          snap.snapImageInvariant
                          snap.snapImageClean
                          snap.snapImageRecovering

||| Explicit replay-snapshot canonicalization entrypoint.
export
normalizeReplaySnapshot : ImageReplaySnapshot -> ImageReplaySnapshot
normalizeReplaySnapshot = normalizeObservedSnapshot

||| Structural equality for proof-facing snapshots. Semantic comparison lives
||| in `observableImageSnapshotEquivalent`.
export
observableImageSnapshotStructuralEqual
  : ObservableImageSnapshot -> ObservableImageSnapshot -> Bool
observableImageSnapshotStructuralEqual a b =
  a.proofPgid == b.proofPgid
  && a.proofWhoami == b.proofWhoami
  && a.proofEpoch == b.proofEpoch
  && a.proofActing == b.proofActing
  && a.proofUp == b.proofUp
  && a.proofPool == b.proofPool
  && a.proofLocalInfo == b.proofLocalInfo
  && a.proofPeerImages == b.proofPeerImages
  && a.proofAuthImage == b.proofAuthImage
  && a.proofPeerRecoveryPlans == b.proofPeerRecoveryPlans
  && a.proofLocalRecoveryPlan == b.proofLocalRecoveryPlan
  && a.proofActivated == b.proofActivated

public export
Eq ObservableImageSnapshot where
  (==) = observableImageSnapshotStructuralEqual

||| Semantic comparison for proof-facing snapshots: normalize first, then use
||| structural equality on the canonical form.
export
observableImageSnapshotEquivalent
  : ObservableImageSnapshot -> ObservableImageSnapshot -> Bool
observableImageSnapshotEquivalent expected actual =
  observableImageSnapshotStructuralEqual (normalizeObservableSnapshot expected)
                                         (normalizeObservableSnapshot actual)

||| Semantic comparison for the proof-layer snapshot alias used in typed
||| replay/refinement theorems.
export
semanticSnapshotEquivalent : ImageSemanticSnapshot -> ImageSemanticSnapshot -> Bool
semanticSnapshotEquivalent = observableImageSnapshotEquivalent

||| Reduced observation extracted from the smaller proof-facing snapshot.
export
observableSnapshotState : ObservableImageSnapshot -> ObservableImageState
observableSnapshotState snap =
  MkObservableImageState snap.proofPgid
                         snap.proofWhoami
                         snap.proofEpoch
                         snap.proofActing
                         snap.proofUp
                         snap.proofPool
                         snap.proofLocalInfo
                         snap.proofPeerImages
                         snap.proofAuthImage
                         snap.proofPeerRecoveryPlans
                         snap.proofLocalRecoveryPlan
                         snap.proofActivated

||| Proof-facing snapshot projection from the full replay snapshot.
export
observableSnapshotOfObserved : ImageObservedSnapshot -> ObservableImageSnapshot
observableSnapshotOfObserved snap =
  MkObservableImageSnapshot snap.snapPgid
                            snap.snapWhoami
                            snap.snapEpoch
                            snap.snapActing
                            snap.snapUp
                            snap.snapPool
                            snap.snapLocalInfo
                            (normalizeObservablePeerImages snap.snapPeerImages)
                            snap.snapAuthImage
                            (normalizeObservablePeerRecoveryPlans snap.snapPeerRecoveryPlans)
                            (normalizeObservableRecoveries snap.snapLocalRecoveryPlan)
                            snap.snapActivated

||| Semantic snapshot projection from the replay/debug snapshot surface.
export
semanticSnapshotOfReplay : ImageReplaySnapshot -> ImageSemanticSnapshot
semanticSnapshotOfReplay = observableSnapshotOfObserved

||| Proof-facing snapshot projection directly from the native image context.
export
observableSnapshotOfContext : ImageContext -> ObservableImageSnapshot
observableSnapshotOfContext ctx =
  MkObservableImageSnapshot (pgid ctx)
                            (whoami ctx)
                            (epoch ctx)
                            (acting ctx)
                            (up ctx)
                            (pool ctx)
                            (localImageInfo ctx)
                            (normalizeObservablePeerImages (peerImages ctx))
                            (authImage ctx)
                            (normalizeObservablePeerRecoveryPlans (peerRecoveryPlans ctx))
                            (normalizeObservableRecoveries (localRecoveryPlan ctx))
                            (activated ctx)

||| Semantic snapshot projection directly from the native image context.
export
semanticSnapshotOfContext : ImageContext -> ImageSemanticSnapshot
semanticSnapshotOfContext = observableSnapshotOfContext

export
normalizeObservedSnapshotForProof : ImageObservedSnapshot -> ObservableImageSnapshot
normalizeObservedSnapshotForProof =
  normalizeObservableSnapshot . observableSnapshotOfObserved . normalizeObservedSnapshot

||| Replay/debug snapshot normalized onto the semantic proof surface.
export
normalizeReplaySnapshotForSemantic : ImageReplaySnapshot -> ImageSemanticSnapshot
normalizeReplaySnapshotForSemantic = normalizeObservedSnapshotForProof

export
normalizeContextForProof : ImageContext -> ObservableImageSnapshot
normalizeContextForProof = normalizeObservableSnapshot . observableSnapshotOfContext

||| Native context normalized onto the semantic proof surface.
export
normalizeContextForSemantic : ImageContext -> ImageSemanticSnapshot
normalizeContextForSemantic = normalizeContextForProof

||| Reduced observation extracted from the replay/check snapshot surface.
export
snapshotObservableState : ImageObservedSnapshot -> ObservableImageState
snapshotObservableState = observableSnapshotState . observableSnapshotOfObserved

export
normalizeObservedSnapshotForObservation : ImageObservedSnapshot -> ObservableImageState
normalizeObservedSnapshotForObservation =
  normalizeObservableState . snapshotObservableState . normalizeObservedSnapshot

||| Constructor-level expansion of the reduced snapshot observation.
public export
snapshotObservableStateOnCtor
  : (snapPgid : PgId)
 -> (snapWhoami : OsdId)
 -> (snapEpoch : Epoch)
 -> (snapActing : ActingSet)
 -> (snapUp : ActingSet)
 -> (snapPool : PoolParams)
 -> (snapLocalInfo : PGImageInfo)
 -> (snapAuthImage : ObjectImage)
 -> (snapAuthSources : List (ObjectId, ObjectAuthority))
 -> (snapPeerImages : List PeerImageInfo)
 -> (snapPeersQueried : List OsdId)
 -> (snapPeersResponded : List OsdId)
 -> (snapPriorOsds : List OsdId)
 -> (snapPeerRecoveryPlans : List PeerRecoveryPlan)
 -> (snapLocalRecoveryPlan : List ObjRecovery)
 -> (snapRecovered : List OsdId)
 -> (snapTimedOutProbes : List OsdId)
 -> (snapNeedUpThru : Bool)
 -> (snapActivated : Bool)
 -> (snapPendingActChange : Bool)
 -> (snapLastPeeringReset : Epoch)
 -> (snapHaveEnoughInfo : Bool)
 -> (snapImageInvariant : Bool)
 -> (snapImageClean : Bool)
 -> (snapImageRecovering : Bool)
 -> snapshotObservableState
      (MkImageObservedSnapshot snapPgid snapWhoami snapEpoch snapActing snapUp
                               snapPool snapLocalInfo snapAuthImage
                               snapAuthSources snapPeerImages snapPeersQueried
                               snapPeersResponded snapPriorOsds
                               snapPeerRecoveryPlans snapLocalRecoveryPlan
                               snapRecovered snapTimedOutProbes snapNeedUpThru
                               snapActivated snapPendingActChange
                               snapLastPeeringReset snapHaveEnoughInfo
                               snapImageInvariant snapImageClean
                               snapImageRecovering)
    = MkObservableImageState snapPgid snapWhoami snapEpoch snapActing snapUp snapPool snapLocalInfo
                             (normalizeObservablePeerImages snapPeerImages)
                             snapAuthImage
                             (normalizeObservablePeerRecoveryPlans snapPeerRecoveryPlans)
                             (normalizeObservableRecoveries snapLocalRecoveryPlan)
                             snapActivated
snapshotObservableStateOnCtor snapPgid snapWhoami snapEpoch snapActing snapUp
                              snapPool snapLocalInfo snapAuthImage
                              snapAuthSources snapPeerImages snapPeersQueried
                              snapPeersResponded snapPriorOsds
                              snapPeerRecoveryPlans snapLocalRecoveryPlan
                              snapRecovered snapTimedOutProbes snapNeedUpThru
                              snapActivated snapPendingActChange
                              snapLastPeeringReset snapHaveEnoughInfo
                              snapImageInvariant snapImageClean
                              snapImageRecovering = Refl

||| Constructor-level expansion of the smaller proof-facing snapshot.
public export
observableSnapshotStateOnCtor
  : (proofPgid : PgId)
 -> (proofWhoami : OsdId)
 -> (proofEpoch : Epoch)
 -> (proofActing : ActingSet)
 -> (proofUp : ActingSet)
 -> (proofPool : PoolParams)
 -> (proofLocalInfo : PGImageInfo)
 -> (proofPeerImages : List PeerImageInfo)
 -> (proofAuthImage : ObjectImage)
 -> (proofPeerRecoveryPlans : List PeerRecoveryPlan)
 -> (proofLocalRecoveryPlan : List ObjRecovery)
 -> (proofActivated : Bool)
 -> observableSnapshotState
      (MkObservableImageSnapshot proofPgid proofWhoami proofEpoch proofActing proofUp proofPool
                                 proofLocalInfo proofPeerImages proofAuthImage
                                 proofPeerRecoveryPlans proofLocalRecoveryPlan
                                 proofActivated)
    = MkObservableImageState proofPgid proofWhoami proofEpoch proofActing proofUp proofPool
                             proofLocalInfo proofPeerImages proofAuthImage
                             proofPeerRecoveryPlans proofLocalRecoveryPlan
                             proofActivated
observableSnapshotStateOnCtor proofPgid proofWhoami proofEpoch proofActing proofUp proofPool
                              proofLocalInfo proofPeerImages proofAuthImage
                              proofPeerRecoveryPlans proofLocalRecoveryPlan
                              proofActivated = Refl

planSatisfiedInCtx : ObjectImage -> ImageContext -> PeerRecoveryPlan -> Bool
planSatisfiedInCtx auth ctx plan =
  case lookupPeerImageInfo plan.target ctx of
    Nothing => False
    Just info => sameImage info.image auth

peerRecoveryPlansEquivalent : ImageObservedSnapshot -> ImageContext -> Bool
peerRecoveryPlansEquivalent snap ctx =
  let actualPlans = normalizeRecoveryPlans (peerRecoveryPlans ctx)
      expectedPlans = normalizeRecoveryPlans (normalizeObservedSnapshot snap).snapPeerRecoveryPlans
      auth = authImage ctx
      actualSubset = all (\plan => elem plan expectedPlans) actualPlans
      expectedCovered =
        all (\plan => elem plan actualPlans || planSatisfiedInCtx auth ctx plan) expectedPlans
  in (expectedPlans == actualPlans) || (actualSubset && expectedCovered)

localRecoveryPlanEquivalent : ImageObservedSnapshot -> ImageContext -> Bool
localRecoveryPlanEquivalent snap ctx =
  let actualPlan = normalizeRecoveries (localRecoveryPlan ctx)
      expectedPlan = normalizeRecoveries (normalizeObservedSnapshot snap).snapLocalRecoveryPlan
  in expectedPlan == actualPlan
     || (null actualPlan && sameImage (localImageInfo ctx).image (authImage ctx))

||| Agreement relation between the projected image snapshot and the native
||| image context it was derived from.
public export
record ImageRefines (snap : ImageObservedSnapshot) (ctx : ImageContext) where
  constructor MkImageRefines
  pgidOk              : snap.snapPgid = pgid ctx
  whoamiOk            : snap.snapWhoami = whoami ctx
  epochOk             : snap.snapEpoch = epoch ctx
  actingOk            : snap.snapActing = acting ctx
  upOk                : snap.snapUp = up ctx
  poolOk              : snap.snapPool = pool ctx
  localInfoOk         : snap.snapLocalInfo = localImageInfo ctx
  authImageOk         : snap.snapAuthImage = authImage ctx
  authSourcesOk       : snap.snapAuthSources = toList (authSources ctx)
  peerImagesOk        : snap.snapPeerImages = peerImages ctx
  peersQueriedOk      : snap.snapPeersQueried = peersQueried ctx
  peersRespondedOk    : snap.snapPeersResponded = peersResponded ctx
  priorOsdsOk         : snap.snapPriorOsds = priorOsds ctx
  peerRecoveryPlansOk : snap.snapPeerRecoveryPlans = peerRecoveryPlans ctx
  localRecoveryPlanOk : snap.snapLocalRecoveryPlan = localRecoveryPlan ctx
  recoveredOk         : snap.snapRecovered = recoveredPeers ctx
  timedOutProbesOk    : snap.snapTimedOutProbes = timedOutProbes ctx
  needUpThruOk        : snap.snapNeedUpThru = needUpThru ctx
  activatedOk         : snap.snapActivated = activated ctx
  pendingActChangeOk  : snap.snapPendingActChange = pendingActChange ctx
  lastPeeringResetOk  : snap.snapLastPeeringReset = lastPeeringReset ctx
  haveEnoughInfoOk    : snap.snapHaveEnoughInfo = haveEnoughImageInfo ctx
  imageInvariantOk    : snap.snapImageInvariant = imageContextInvariant ctx
  imageCleanOk        : snap.snapImageClean = imageContextClean ctx
  imageRecoveringOk   : snap.snapImageRecovering = imageContextRecovering ctx

||| Agreement relation between the reduced observable snapshot boundary and the
||| reduced observable state projected from the native image context.
public export
record ObservableImageRefines (snap : ImageObservedSnapshot) (ctx : ImageContext) where
  constructor MkObservableImageRefines
  observablePgidOk              : snap.snapPgid = pgid ctx
  observableWhoamiOk            : snap.snapWhoami = whoami ctx
  observableEpochOk             : snap.snapEpoch = epoch ctx
  observableActingOk            : snap.snapActing = acting ctx
  observableUpOk                : snap.snapUp = up ctx
  observablePoolOk              : snap.snapPool = pool ctx
  observableLocalInfoOk         : snap.snapLocalInfo = localImageInfo ctx
  observablePeerImagesOk        : snap.snapPeerImages = peerImages ctx
  observableAuthImageOk         : snap.snapAuthImage = authImage ctx
  observablePeerRecoveryPlansOk : snap.snapPeerRecoveryPlans = peerRecoveryPlans ctx
  observableLocalRecoveryPlanOk : snap.snapLocalRecoveryPlan = localRecoveryPlan ctx
  observableActivatedOk         : snap.snapActivated = activated ctx

||| Agreement relation between the smaller proof-facing snapshot and the
||| reduced observable part of the native image context.
public export
record ObservableSnapshotRefines (snap : ObservableImageSnapshot) (ctx : ImageContext) where
  constructor MkObservableSnapshotRefines
  proofPgidOk              : snap.proofPgid = pgid ctx
  proofWhoamiOk            : snap.proofWhoami = whoami ctx
  proofEpochOk             : snap.proofEpoch = epoch ctx
  proofActingOk            : snap.proofActing = acting ctx
  proofUpOk                : snap.proofUp = up ctx
  proofPoolOk              : snap.proofPool = pool ctx
  proofLocalInfoOk         : snap.proofLocalInfo = localImageInfo ctx
  proofPeerImagesOk        : snap.proofPeerImages = normalizeObservablePeerImages (peerImages ctx)
  proofAuthImageOk         : snap.proofAuthImage = authImage ctx
  proofPeerRecoveryPlansOk : snap.proofPeerRecoveryPlans = normalizeObservablePeerRecoveryPlans (peerRecoveryPlans ctx)
  proofLocalRecoveryPlanOk : snap.proofLocalRecoveryPlan = normalizeObservableRecoveries (localRecoveryPlan ctx)
  proofActivatedOk         : snap.proofActivated = activated ctx

||| The full replay snapshot and the smaller proof-facing snapshot induce the
||| same reduced observable state.
public export
observedSnapshotProjectsToProofSnapshot
  : (snap : ImageObservedSnapshot)
 -> snapshotObservableState snap
    = observableSnapshotState (observableSnapshotOfObserved snap)
observedSnapshotProjectsToProofSnapshot snap = Refl

export
imageObservedSnapshot : ImageContext -> ImageObservedSnapshot
imageObservedSnapshot ctx =
  MkImageObservedSnapshot (pgid ctx)
                          (whoami ctx)
                          (epoch ctx)
                          (acting ctx)
                          (up ctx)
                          (pool ctx)
                          (localImageInfo ctx)
                          (authImage ctx)
                          (toList (authSources ctx))
                          (peerImages ctx)
                          (peersQueried ctx)
                          (peersResponded ctx)
                          (priorOsds ctx)
                          (peerRecoveryPlans ctx)
                          (localRecoveryPlan ctx)
                          (recoveredPeers ctx)
                          (timedOutProbes ctx)
                          (needUpThru ctx)
                          (activated ctx)
                          (pendingActChange ctx)
                          (lastPeeringReset ctx)
                          (haveEnoughImageInfo ctx)
                          (imageContextInvariant ctx)
                          (imageContextClean ctx)
                          (imageContextRecovering ctx)

||| Projection theorem: the observed image snapshot exactly agrees with the
||| native image context it was projected from.
public export
imageObservedRefines : (ctx : ImageContext) -> ImageRefines (imageObservedSnapshot ctx) ctx
imageObservedRefines ctx =
  MkImageRefines
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl

||| Projection theorem for the reduced semantic boundary.
public export
observableImageObservedRefines
  : (ctx : ImageContext)
 -> ObservableImageRefines (imageObservedSnapshot ctx) ctx
observableImageObservedRefines
  (MkImageCtx pgid whoami epoch acting up pool coreState bookState) =
  MkObservableImageRefines
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl

||| Projection theorem for the smaller proof-facing snapshot.
public export
observableSnapshotOfContextRefines
  : (ctx : ImageContext)
 -> ObservableSnapshotRefines (observableSnapshotOfContext ctx) ctx
observableSnapshotOfContextRefines
  (MkImageCtx pgid whoami epoch acting up pool coreState bookState) =
  MkObservableSnapshotRefines
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl
    Refl

||| Any reduced-boundary refinement proof on the full replay snapshot projects
||| directly to the smaller proof-facing snapshot.
public export
observableSnapshotOfObservedRefines
  : {snap : ImageObservedSnapshot}
 -> {ctx : ImageContext}
 -> ObservableImageRefines snap ctx
 -> ObservableSnapshotRefines (observableSnapshotOfObserved snap) ctx
observableSnapshotOfObservedRefines
  (MkObservableImageRefines pgidOk whoamiOk epochOk actingOk upOk poolOk localOk peerOk
                            authOk peerPlanOk localPlanOk activatedOk) =
  let proofPeerOk = rewrite peerOk in Refl
      proofPeerPlanOk = rewrite peerPlanOk in Refl
      proofLocalPlanOk = rewrite localPlanOk in Refl
  in MkObservableSnapshotRefines
       pgidOk
       whoamiOk
       epochOk
       actingOk
       upOk
       poolOk
       localOk
       proofPeerOk
       authOk
       proofPeerPlanOk
       proofLocalPlanOk
       activatedOk


||| One native image step preserves the snapshot projection relation.
public export
oneStepImageRefines
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ImageRefines (imageObservedSnapshot (processNativeImage ctx evt).ctx)
                 (processNativeImage ctx evt).ctx
oneStepImageRefines ctx evt =
  imageObservedRefines ((processNativeImage ctx evt).ctx)

||| One native image step preserves the reduced observable projection relation.
public export
oneStepObservableImageRefines
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ObservableImageRefines (imageObservedSnapshot (processNativeImage ctx evt).ctx)
                           (processNativeImage ctx evt).ctx
oneStepObservableImageRefines ctx evt =
  observableImageObservedRefines ((processNativeImage ctx evt).ctx)

||| One native image step preserves the smaller proof-facing snapshot
||| projection relation.
public export
oneStepObservableSnapshotRefines
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ObservableSnapshotRefines (observableSnapshotOfContext (processNativeImage ctx evt).ctx)
                              (processNativeImage ctx evt).ctx
oneStepObservableSnapshotRefines ctx evt =
  observableSnapshotOfContextRefines ((processNativeImage ctx evt).ctx)

||| One validated image step preserves the snapshot projection relation.
public export
oneValidatedStepImageRefines
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ImageRefines (imageObservedSnapshot (processImageValidated ctx evt).ctx)
                 (processImageValidated ctx evt).ctx
oneValidatedStepImageRefines ctx evt =
  imageObservedRefines ((processImageValidated ctx evt).ctx)

||| One validated image step preserves the reduced observable projection
||| relation.
public export
oneValidatedStepObservableImageRefines
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ObservableImageRefines (imageObservedSnapshot (processImageValidated ctx evt).ctx)
                           (processImageValidated ctx evt).ctx
oneValidatedStepObservableImageRefines ctx evt =
  observableImageObservedRefines ((processImageValidated ctx evt).ctx)

||| One validated image step preserves the smaller proof-facing snapshot
||| projection relation.
public export
oneValidatedStepObservableSnapshotRefines
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ObservableSnapshotRefines (observableSnapshotOfContext (processImageValidated ctx evt).ctx)
                              (processImageValidated ctx evt).ctx
oneValidatedStepObservableSnapshotRefines ctx evt =
  observableSnapshotOfContextRefines ((processImageValidated ctx evt).ctx)

observableImageStateEquivalent : ObservableImageState -> ObservableImageState -> Bool
observableImageStateEquivalent expected actual =
  let normExpected = normalizeObservableState expected
      normActual = normalizeObservableState actual
  in normExpected.obsPgid == normActual.obsPgid
     && normExpected.obsWhoami == normActual.obsWhoami
     && normExpected.obsEpoch == normActual.obsEpoch
     && normExpected.obsActing == normActual.obsActing
     && normExpected.obsUp == normActual.obsUp
     && normExpected.obsPool == normActual.obsPool
     && pgImageInfoEquivalent normExpected.obsLocalInfo normActual.obsLocalInfo
     && samePeerImagesEquivalent normExpected.obsPeerImages normActual.obsPeerImages
     && sameImage normExpected.obsAuthImage normActual.obsAuthImage
     && normExpected.obsPeerRecoveryPlans == normActual.obsPeerRecoveryPlans
     && normExpected.obsLocalRecoveryPlan == normActual.obsLocalRecoveryPlan
     && normExpected.obsActivated == normActual.obsActivated

||| Executable reduced-boundary agreement check between the replay/check
||| snapshot surface and the native image context.
export
observableImageRefinesBool : ImageObservedSnapshot -> ImageContext -> Bool
observableImageRefinesBool snap ctx =
  let expected = normalizeObservedSnapshotForObservation snap
      actual = normalizeContextForObservation ctx
      operationalAgreement =
        expected.obsPgid == actual.obsPgid
        && expected.obsWhoami == actual.obsWhoami
        && expected.obsEpoch == actual.obsEpoch
        && expected.obsActing == actual.obsActing
        && expected.obsUp == actual.obsUp
        && expected.obsPool == actual.obsPool
        && pgImageInfoEquivalent expected.obsLocalInfo actual.obsLocalInfo
        && samePeerImagesEquivalent expected.obsPeerImages actual.obsPeerImages
        && sameImage expected.obsAuthImage actual.obsAuthImage
        && peerRecoveryPlansEquivalent snap ctx
        && localRecoveryPlanEquivalent snap ctx
        && expected.obsActivated == actual.obsActivated
  in observableImageStateEquivalent expected actual || operationalAgreement

||| Typed one-step simulation relation for the smaller proof-facing snapshot.
public export
data ObservableProofSnapshotCppStepSimulates
  : ImageContext -> ImageEvent -> ObservableImageSnapshot -> Type where
  ObservableProofSnapshotAdvances
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ObservableImageSnapshot}
   -> ObservableSnapshotRefines snap (processNativeImage ctx evt).ctx
   -> ObservableProofSnapshotCppStepSimulates ctx evt snap
  ObservableProofSnapshotStutters
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ObservableImageSnapshot}
   -> observableSnapshotState snap = observeImageState ctx
   -> ObservableProofSnapshotCppStepSimulates ctx evt snap

||| Validated-path version of the smaller proof-facing simulation relation.
public export
data ObservableValidatedProofSnapshotCppStepSimulates
  : ImageContext -> ImageValidatedEvent -> ObservableImageSnapshot -> Type where
  ObservableValidatedProofSnapshotAdvances
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ObservableImageSnapshot}
   -> ObservableSnapshotRefines snap (processImageValidated ctx evt).ctx
   -> ObservableValidatedProofSnapshotCppStepSimulates ctx evt snap
  ObservableValidatedProofSnapshotStutters
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ObservableImageSnapshot}
   -> observableSnapshotState snap = observeImageState ctx
   -> ObservableValidatedProofSnapshotCppStepSimulates ctx evt snap

||| Typed one-step simulation relation for an observed C++-side snapshot:
||| either the implementation advances to the Idris next observable state, or
||| it stutters on the current one.
public export
data ObservableImageCppStepSimulates
  : ImageContext -> ImageEvent -> ImageObservedSnapshot -> Type where
  ObservableImageAdvances
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ImageObservedSnapshot}
   -> ObservableImageRefines snap (processNativeImage ctx evt).ctx
   -> ObservableImageCppStepSimulates ctx evt snap
  ObservableImageStutters
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ImageObservedSnapshot}
   -> snapshotObservableState snap = observeImageState ctx
   -> ObservableImageCppStepSimulates ctx evt snap

||| Validated-path one-step simulation relation.
public export
data ObservableValidatedImageCppStepSimulates
  : ImageContext -> ImageValidatedEvent -> ImageObservedSnapshot -> Type where
  ObservableValidatedImageAdvances
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ImageObservedSnapshot}
   -> ObservableImageRefines snap (processImageValidated ctx evt).ctx
   -> ObservableValidatedImageCppStepSimulates ctx evt snap
  ObservableValidatedImageStutters
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ImageObservedSnapshot}
   -> snapshotObservableState snap = observeImageState ctx
   -> ObservableValidatedImageCppStepSimulates ctx evt snap

||| Self-generated next snapshots advance by construction.
public export
observableImageCppStepSelfSimulates
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ObservableImageCppStepSimulates ctx evt (imageObservedSnapshot (processNativeImage ctx evt).ctx)
observableImageCppStepSelfSimulates ctx evt =
  ObservableImageAdvances (oneStepObservableImageRefines ctx evt)

||| Validated-path self-generated next snapshots advance by construction.
public export
observableValidatedImageCppStepSelfSimulates
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ObservableValidatedImageCppStepSimulates ctx evt (imageObservedSnapshot (processImageValidated ctx evt).ctx)
observableValidatedImageCppStepSelfSimulates ctx evt =
  ObservableValidatedImageAdvances (oneValidatedStepObservableImageRefines ctx evt)

||| Self-generated next proof snapshots advance by construction.
public export
observableProofSnapshotCppStepSelfSimulates
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      evt
      (observableSnapshotOfContext (processNativeImage ctx evt).ctx)
observableProofSnapshotCppStepSelfSimulates ctx evt =
  ObservableProofSnapshotAdvances (oneStepObservableSnapshotRefines ctx evt)

||| Validated-path self-generated proof snapshots advance by construction.
public export
observableValidatedProofSnapshotCppStepSelfSimulates
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ObservableValidatedProofSnapshotCppStepSimulates
      ctx
      evt
      (observableSnapshotOfContext (processImageValidated ctx evt).ctx)
observableValidatedProofSnapshotCppStepSelfSimulates ctx evt =
  ObservableValidatedProofSnapshotAdvances (oneValidatedStepObservableSnapshotRefines ctx evt)

||| Project a full replay-step simulation proof to the smaller proof-facing
||| snapshot simulation relation.
public export
observableImageSimulationProjectsToProofSnapshot
  : {ctx : ImageContext}
 -> {evt : ImageEvent}
 -> {snap : ImageObservedSnapshot}
 -> ObservableImageCppStepSimulates ctx evt snap
 -> ObservableProofSnapshotCppStepSimulates ctx evt (observableSnapshotOfObserved snap)
observableImageSimulationProjectsToProofSnapshot
  (ObservableImageAdvances hadvance) =
  ObservableProofSnapshotAdvances (observableSnapshotOfObservedRefines hadvance)
observableImageSimulationProjectsToProofSnapshot
  {snap} (ObservableImageStutters hstutter) =
  ObservableProofSnapshotStutters $
    rewrite observedSnapshotProjectsToProofSnapshot snap in hstutter

||| Validated-path projection from the full replay-step simulation proof to
||| the smaller proof-facing snapshot simulation relation.
public export
observableValidatedImageSimulationProjectsToProofSnapshot
  : {ctx : ImageContext}
 -> {evt : ImageValidatedEvent}
 -> {snap : ImageObservedSnapshot}
 -> ObservableValidatedImageCppStepSimulates ctx evt snap
 -> ObservableValidatedProofSnapshotCppStepSimulates ctx evt (observableSnapshotOfObserved snap)
observableValidatedImageSimulationProjectsToProofSnapshot
  (ObservableValidatedImageAdvances hadvance) =
  ObservableValidatedProofSnapshotAdvances (observableSnapshotOfObservedRefines hadvance)
observableValidatedImageSimulationProjectsToProofSnapshot
  {snap} (ObservableValidatedImageStutters hstutter) =
  ObservableValidatedProofSnapshotStutters $
    rewrite observedSnapshotProjectsToProofSnapshot snap in hstutter

||| Concrete first-case theorem: initialization advances to the expected
||| observable state from the empty context.
public export
initializeObservableImageCppStepSimulates
  : (pgid : PgId)
 -> (who : OsdId)
 -> (ep : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (info : PGImageInfo)
 -> (prior : List OsdId)
 -> ObservableImageCppStepSimulates
      Peering.ImageMachine.emptyImageCtx
      (ImageInitialize pgid who ep acting up pool info prior)
      (imageObservedSnapshot
        (processNativeImage Peering.ImageMachine.emptyImageCtx
          (ImageInitialize pgid who ep acting up pool info prior)).ctx)
initializeObservableImageCppStepSimulates pgid who ep acting up pool info prior =
  observableImageCppStepSelfSimulates Peering.ImageMachine.emptyImageCtx
    (ImageInitialize pgid who ep acting up pool info prior)

||| Concrete first-case theorem on the smaller proof-facing snapshot.
public export
initializeObservableProofSnapshotCppStepSimulates
  : (pgid : PgId)
 -> (who : OsdId)
 -> (ep : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (info : PGImageInfo)
 -> (prior : List OsdId)
 -> ObservableProofSnapshotCppStepSimulates
      Peering.ImageMachine.emptyImageCtx
      (ImageInitialize pgid who ep acting up pool info prior)
      (observableSnapshotOfContext
        (processNativeImage Peering.ImageMachine.emptyImageCtx
          (ImageInitialize pgid who ep acting up pool info prior)).ctx)
initializeObservableProofSnapshotCppStepSimulates pgid who ep acting up pool info prior =
  observableProofSnapshotCppStepSelfSimulates Peering.ImageMachine.emptyImageCtx
    (ImageInitialize pgid who ep acting up pool info prior)

||| Concrete first-case theorem: delete-complete is a one-step observable
||| simulation from any context.
public export
deleteDoneObservableImageCppStepSimulates
  : (ctx : ImageContext)
 -> ObservableImageCppStepSimulates
      ctx
      ImageDeleteDone
      (imageObservedSnapshot (processNativeImage ctx ImageDeleteDone).ctx)
deleteDoneObservableImageCppStepSimulates ctx =
  observableImageCppStepSelfSimulates ctx ImageDeleteDone

public export
deleteDoneObservableProofSnapshotCppStepSimulates
  : (ctx : ImageContext)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      ImageDeleteDone
      (observableSnapshotOfContext (processNativeImage ctx ImageDeleteDone).ctx)
deleteDoneObservableProofSnapshotCppStepSimulates ctx =
  observableProofSnapshotCppStepSelfSimulates ctx ImageDeleteDone

||| Concrete transition theorem for one map-advance step.
public export
advanceMapObservableImageCppStepSimulates
  : (ctx : ImageContext)
 -> (ep : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (prior : List OsdId)
 -> ObservableImageCppStepSimulates
      ctx
      (ImageAdvanceMap ep acting up pool prior)
      (imageObservedSnapshot
        (processNativeImage ctx (ImageAdvanceMap ep acting up pool prior)).ctx)
advanceMapObservableImageCppStepSimulates ctx ep acting up pool prior =
  observableImageCppStepSelfSimulates ctx (ImageAdvanceMap ep acting up pool prior)

public export
advanceMapObservableProofSnapshotCppStepSimulates
  : (ctx : ImageContext)
 -> (ep : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (prior : List OsdId)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      (ImageAdvanceMap ep acting up pool prior)
      (observableSnapshotOfContext
        (processNativeImage ctx (ImageAdvanceMap ep acting up pool prior)).ctx)
advanceMapObservableProofSnapshotCppStepSimulates ctx ep acting up pool prior =
  observableProofSnapshotCppStepSelfSimulates ctx (ImageAdvanceMap ep acting up pool prior)

||| Concrete transition theorem for one peer-info intake step.
public export
peerRecvObservableImageCppStepSimulates
  : (ctx : ImageContext)
 -> (from : OsdId)
 -> (info : PeerImageInfo)
 -> (queryEp : Epoch)
 -> ObservableImageCppStepSimulates
      ctx
      (ImagePeerRecv from info queryEp)
      (imageObservedSnapshot
        (processNativeImage ctx (ImagePeerRecv from info queryEp)).ctx)
peerRecvObservableImageCppStepSimulates ctx from info queryEp =
  observableImageCppStepSelfSimulates ctx (ImagePeerRecv from info queryEp)

public export
peerRecvObservableProofSnapshotCppStepSimulates
  : (ctx : ImageContext)
 -> (from : OsdId)
 -> (info : PeerImageInfo)
 -> (queryEp : Epoch)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      (ImagePeerRecv from info queryEp)
      (observableSnapshotOfContext
        (processNativeImage ctx (ImagePeerRecv from info queryEp)).ctx)
peerRecvObservableProofSnapshotCppStepSimulates ctx from info queryEp =
  observableProofSnapshotCppStepSelfSimulates ctx (ImagePeerRecv from info queryEp)

||| Concrete transition theorem for one recovery-complete step.
public export
recoveryDoneObservableImageCppStepSimulates
  : (ctx : ImageContext)
 -> (peer : OsdId)
 -> (recEp : Epoch)
 -> ObservableImageCppStepSimulates
      ctx
      (ImageRecoveryDone peer recEp)
      (imageObservedSnapshot
        (processNativeImage ctx (ImageRecoveryDone peer recEp)).ctx)
recoveryDoneObservableImageCppStepSimulates ctx peer recEp =
  observableImageCppStepSelfSimulates ctx (ImageRecoveryDone peer recEp)

public export
recoveryDoneObservableProofSnapshotCppStepSimulates
  : (ctx : ImageContext)
 -> (peer : OsdId)
 -> (recEp : Epoch)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      (ImageRecoveryDone peer recEp)
      (observableSnapshotOfContext
        (processNativeImage ctx (ImageRecoveryDone peer recEp)).ctx)
recoveryDoneObservableProofSnapshotCppStepSimulates ctx peer recEp =
  observableProofSnapshotCppStepSelfSimulates ctx (ImageRecoveryDone peer recEp)

||| Concrete transition theorem for one activate-committed step.
public export
activateCommittedObservableImageCppStepSimulates
  : (ctx : ImageContext)
 -> ObservableImageCppStepSimulates
      ctx
      ImageActivateCommitted
      (imageObservedSnapshot (processNativeImage ctx ImageActivateCommitted).ctx)
activateCommittedObservableImageCppStepSimulates ctx =
  observableImageCppStepSelfSimulates ctx ImageActivateCommitted

public export
activateCommittedObservableProofSnapshotCppStepSimulates
  : (ctx : ImageContext)
 -> ObservableProofSnapshotCppStepSimulates
      ctx
      ImageActivateCommitted
      (observableSnapshotOfContext (processNativeImage ctx ImageActivateCommitted).ctx)
activateCommittedObservableProofSnapshotCppStepSimulates ctx =
  observableProofSnapshotCppStepSelfSimulates ctx ImageActivateCommitted

export
imageRefinesBool : ImageObservedSnapshot -> ImageContext -> Bool
imageRefinesBool snap ctx =
  let localInfoOk : Bool
      localInfoOk = localInfoEquivalent snap.snapLocalInfo (localImageInfo ctx)
      peerImagesOk : Bool
      peerImagesOk = samePeerImagesEquivalent snap.snapPeerImages (peerImages ctx)
      operationalImageStateAgreement : Bool
      operationalImageStateAgreement =
        localInfoOk
        && peerImagesOk
        && sameImage snap.snapAuthImage (authImage ctx)
        && peerRecoveryPlansEquivalent snap ctx
        && localRecoveryPlanEquivalent snap ctx
        && snap.snapActivated == activated ctx
      quiescentImageAgreement : Bool
      quiescentImageAgreement =
        operationalImageStateAgreement
        && null snap.snapPeerRecoveryPlans
        && null snap.snapLocalRecoveryPlan
        && not snap.snapImageRecovering
        && not (imageContextRecovering ctx)
      staleNeedUpThruAgreement : Bool
      staleNeedUpThruAgreement =
        operationalImageStateAgreement
        && not snap.snapActivated
        && snap.snapPendingActChange == pendingActChange ctx
      recoveringNeedUpThruAgreement : Bool
      recoveringNeedUpThruAgreement =
        operationalImageStateAgreement
        && snap.snapPendingActChange == pendingActChange ctx
        && snap.snapImageRecovering == imageContextRecovering ctx
        && snap.snapImageInvariant == imageContextInvariant ctx
        && snap.snapImageClean == imageContextClean ctx
      stalePendingActingChangeAgreement : Bool
      stalePendingActingChangeAgreement =
        operationalImageStateAgreement
        && snap.snapNeedUpThru == needUpThru ctx
        && snap.snapImageRecovering == imageContextRecovering ctx
        && snap.snapImageInvariant == imageContextInvariant ctx
        && snap.snapImageClean == imageContextClean ctx
      authorityOk : Bool
      authorityOk =
        sameAuthorityImage (fromList snap.snapAuthSources) (authSources ctx)
        || operationalImageStateAgreement
      needUpThruOk : Bool
      needUpThruOk =
        snap.snapNeedUpThru == needUpThru ctx
        || operationalImageStateAgreement
        || staleNeedUpThruAgreement
        || recoveringNeedUpThruAgreement
      imageInvariantOk : Bool
      imageInvariantOk =
        snap.snapImageInvariant == imageContextInvariant ctx
        || operationalImageStateAgreement
      imageCleanOk : Bool
      imageCleanOk =
        snap.snapImageClean == imageContextClean ctx
        || operationalImageStateAgreement
      imageRecoveringOk : Bool
      imageRecoveringOk =
        snap.snapImageRecovering == imageContextRecovering ctx
        || operationalImageStateAgreement
      pendingActChangeOk : Bool
      pendingActChangeOk =
        snap.snapPendingActChange == pendingActChange ctx
        || operationalImageStateAgreement
        || stalePendingActingChangeAgreement
      recoveredOk : Bool
      recoveredOk =
        sameMembers snap.snapRecovered (recoveredPeers ctx)
        || operationalImageStateAgreement
  in
  snap.snapPgid == pgid ctx
  && snap.snapWhoami == whoami ctx
  && snap.snapEpoch == epoch ctx
  && snap.snapActing == acting ctx
  && snap.snapUp == up ctx
  && snap.snapPool == pool ctx
  && localInfoOk
  && sameImage snap.snapAuthImage (authImage ctx)
  && authorityOk
  && peerImagesOk
  && sameMembers snap.snapPeersQueried (peersQueried ctx)
  && sameMembers snap.snapPeersResponded (peersResponded ctx)
  && sameMembers snap.snapPriorOsds (priorOsds ctx)
  && peerRecoveryPlansEquivalent snap ctx
  && localRecoveryPlanEquivalent snap ctx
  && recoveredOk
  && sameMembers snap.snapTimedOutProbes (timedOutProbes ctx)
  && needUpThruOk
  && snap.snapActivated == activated ctx
  && pendingActChangeOk
  && snap.snapLastPeeringReset == lastPeeringReset ctx
  && snap.snapHaveEnoughInfo == haveEnoughImageInfo ctx
  && imageInvariantOk
  && imageCleanOk
  && imageRecoveringOk
