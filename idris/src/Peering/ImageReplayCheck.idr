||| Typed replay-check helpers for the image-native executable boundary.
module Peering.ImageReplayCheck

import public Peering.ImageProofs
import Peering.ImageInvariants
import Peering.ImageMachine
import Peering.ImageProcess
import Peering.ImageRefinement
import Peering.Types

%default total

showBoolFlag : Bool -> String
showBoolFlag True = "1"
showBoolFlag False = "0"

||| Exact replay agreement between a replay/debug snapshot and the semantic
||| proof-facing snapshot surface.
export
observedSnapshotMatchesNext
  : ImageReplaySnapshot -> ImageContext -> Bool
observedSnapshotMatchesNext snap ctx =
  normalizeReplaySnapshotForSemantic snap == normalizeContextForSemantic ctx

public export
data NativeImageReplayFailure
  = ExpectedSnapshotMismatch
  | CurrentInvariantUnavailable
  | CurrentSemanticBoundaryUnavailable
  | CurrentObservableBoundaryUnavailable
  | NextInvariantUnavailable
  | NextSemanticBoundaryUnavailable
  | NextObservableBoundaryUnavailable
  | NextObservableSnapshotUnsafe
  | TraceRefinementUnavailable

public export
showNativeImageReplayFailure : NativeImageReplayFailure -> String
showNativeImageReplayFailure ExpectedSnapshotMismatch =
  "expected replay snapshot does not match the Idris next observable snapshot"
showNativeImageReplayFailure CurrentInvariantUnavailable =
  "current Idris context does not provide typed invariant evidence"
showNativeImageReplayFailure CurrentSemanticBoundaryUnavailable =
  "current Idris context does not provide typed semantic-boundary evidence"
showNativeImageReplayFailure CurrentObservableBoundaryUnavailable =
  "current Idris context does not provide typed observable-boundary evidence"
showNativeImageReplayFailure NextInvariantUnavailable =
  "failed to recover typed next-step invariant evidence"
showNativeImageReplayFailure NextSemanticBoundaryUnavailable =
  "failed to recover typed next-step semantic-boundary evidence"
showNativeImageReplayFailure NextObservableBoundaryUnavailable =
  "failed to recover typed next-step observable-boundary evidence"
showNativeImageReplayFailure NextObservableSnapshotUnsafe =
  "failed to recover typed observable-snapshot safety evidence"
showNativeImageReplayFailure TraceRefinementUnavailable =
  "failed to recover a typed semantic trace-refinement witness for the replay sequence"

public export
showImageInvariantBreakdown : ImageContext -> String
showImageInvariantBreakdown ctx =
  "inv[authority=" ++ showBoolFlag (authorityDerivedCorrectly ctx)
  ++ " local=" ++ showBoolFlag (localImageSafe ctx)
  ++ " acting=" ++ showBoolFlag (actingImagesSafe ctx)
  ++ " peerPlans=" ++ showBoolFlag (peerRecoveryPlansCorrect ctx)
  ++ " localPlan=" ++ showBoolFlag (localRecoveryPlanCorrect ctx)
  ++ "]"

public export
showImageSemanticBoundaryBreakdown : ImageContext -> String
showImageSemanticBoundaryBreakdown ctx =
  "semantic[inv=" ++ showBoolFlag (imageContextInvariant ctx)
  ++ " authorityBacked=" ++ showBoolFlag (authorityBackedByKnownPeer ctx)
  ++ " realGaps=" ++ showBoolFlag (peerRecoveryPlansTargetRealGaps ctx)
  ++ " localGapWitness=" ++ showBoolFlag (localRecoveryPlanWitnessesGap ctx)
  ++ " serving=" ++ showBoolFlag (activatedServingSafe ctx)
  ++ " observable=" ++ showBoolFlag (contextObservableStateSafe ctx)
  ++ "]"

public export
showImageObservableBoundaryBreakdown : ImageContext -> String
showImageObservableBoundaryBreakdown ctx =
  showContextObservableStateBreakdown ctx

||| Successful typed replay check for one native step.
public export
record NativeImageReplayStepOk
    (ctx : ImageContext)
    (evt : ImageEvent)
    (expected : ImageReplaySnapshot) where
  constructor MkNativeImageReplayStepOk
  nextInvariant
    : ImageInvariant (processNativeImage ctx evt).ctx
  nextSemanticBoundary
    : ImageSemanticBoundary (processNativeImage ctx evt).ctx
  nextProofBoundary
    : ImageObservableBoundary (processNativeImage ctx evt).ctx
  actualNextSafe
    : ObservedObservableSnapshotBoundary
        (observableSnapshotOfContext (processNativeImage ctx evt).ctx)

||| Check one native replay step against the typed proof-facing observable
||| boundary.
public export
checkNativeImageReplayStep
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> (expected : ImageReplaySnapshot)
 -> Either NativeImageReplayFailure (NativeImageReplayStepOk ctx evt expected)
checkNativeImageReplayStep ctx evt expected =
  let nextCtx = (processNativeImage ctx evt).ctx in
  if observedSnapshotMatchesNext expected nextCtx
     then
       case decImageInvariant ctx of
         No _ => Left CurrentInvariantUnavailable
         Yes startInvariant =>
           case buildImageStepInvariant ctx evt startInvariant of
             Nothing => Left NextInvariantUnavailable
             Just nextInvariant =>
               case decImageSemanticBoundary ctx of
                 No _ => Left CurrentSemanticBoundaryUnavailable
                 Yes startSemanticBoundary =>
                   case buildImageStepSemanticBoundary ctx evt startSemanticBoundary of
                     Nothing => Left NextSemanticBoundaryUnavailable
                     Just nextSemanticBoundary =>
                       case decImageObservableBoundary ctx of
                         No _ => Left CurrentObservableBoundaryUnavailable
                         Yes startObservableBoundary =>
                           case buildImageStepObservableBoundary
                                  ctx
                                  evt
                                  startObservableBoundary of
                             Nothing => Left NextObservableBoundaryUnavailable
                             Just nextProofBoundary =>
                               let actualNextSafe =
                                     observedObservableSnapshotBoundary
                                       ((processNativeImage ctx evt).ctx)
                                       nextProofBoundary
                               in Right (MkNativeImageReplayStepOk
                                           nextInvariant
                                           nextSemanticBoundary
                                           nextProofBoundary
                                           actualNextSafe)
     else Left ExpectedSnapshotMismatch

||| Recover the typed semantic trace-refinement witness for a replay-successful
||| native event sequence. Replay/debug snapshots are used only for local
||| mismatch reporting; the final success condition is the smaller semantic
||| proof trace.
public export
buildNativeImageReplayEventTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> Either NativeImageReplayFailure
      (ObservedSemanticSnapshotTraceRefinement
         ctx
         (semanticSnapshotTraceOf ctx evts))
buildNativeImageReplayEventTraceRefinement ctx evts =
  case decImageObservableBoundary ctx of
    No _ => Left CurrentObservableBoundaryUnavailable
    Yes obs =>
      case buildSelfObservedSemanticSnapshotTraceRefinement ctx evts obs of
        Nothing => Left TraceRefinementUnavailable
        Just hrefine => Right hrefine
