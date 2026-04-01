||| Observable append-only image semantics for refinement proofs.
|||
||| This module projects the full image-native peering context down to the
||| fields that matter for append-only storage semantics. Internal peering
||| bookkeeping such as timeout residue, recovered-peer markers, up-thru flags,
||| and pending acting-change bits are intentionally excluded here.
module Peering.ImageObservation

import Data.List
import Peering.ImageMachine
import Peering.ImageInvariants
import Peering.Types

%default total

public export
record ObservableImageState where
  constructor MkObservableImageState
  obsPgid              : PgId
  obsWhoami            : OsdId
  obsEpoch             : Epoch
  obsActing            : ActingSet
  obsUp                : ActingSet
  obsPool              : PoolParams
  obsLocalImage        : PGImageInfo
  obsAuthImage         : ObjectImage
  obsPeerImages        : List PeerImageInfo
  obsPeerRecoveryPlans : List PeerRecoveryPlan
  obsLocalRecoveryPlan : List ObjRecovery
  obsActivated         : Bool

export
observableImageState : ImageContext -> ObservableImageState
observableImageState ctx =
  normalizeObservableState $
    MkObservableImageState (pgid ctx)
                           (whoami ctx)
                           (epoch ctx)
                           (acting ctx)
                           (up ctx)
                           (pool ctx)
                           (localImageInfo ctx)
                           (authImage ctx)
                           (peerImages ctx)
                           (peerRecoveryPlans ctx)
                           (localRecoveryPlan ctx)
                           (activated ctx)

export
normalizeObservableState : ObservableImageState -> ObservableImageState
normalizeObservableState obs =
  MkObservableImageState (obsPgid obs)
                         (obsWhoami obs)
                         (obsEpoch obs)
                         (obsActing obs)
                         (obsUp obs)
                         (obsPool obs)
                         (obsLocalImage obs)
                         (obsAuthImage obs)
                         (normalizePeerImages (obsPeerImages obs))
                         (normalizeRecoveryPlans (obsPeerRecoveryPlans obs))
                         (normalizeRecoveries (obsLocalRecoveryPlan obs))
                         (obsActivated obs)

||| Named semantic comparison for observable states. Raw structural equality is
||| intentionally left to fieldwise comparisons on the record itself.
export
observableStateEquivalent : ObservableImageState -> ObservableImageState -> Bool
observableStateEquivalent left right =
  let normLeft = normalizeObservableState left
      normRight = normalizeObservableState right
  in obsPgid normLeft == obsPgid normRight
     && obsWhoami normLeft == obsWhoami normRight
     && obsEpoch normLeft == obsEpoch normRight
     && obsActing normLeft == obsActing normRight
     && obsUp normLeft == obsUp normRight
     && obsPool normLeft == obsPool normRight
     && obsLocalImage normLeft == obsLocalImage normRight
     && sameImage (obsAuthImage normLeft) (obsAuthImage normRight)
     && obsPeerImages normLeft == obsPeerImages normRight
     && obsPeerRecoveryPlans normLeft == obsPeerRecoveryPlans normRight
     && obsLocalRecoveryPlan normLeft == obsLocalRecoveryPlan normRight
     && obsActivated normLeft == obsActivated normRight

||| Backwards-compatible alias for the older semantic-comparison name.
export
observableStateEq : ObservableImageState -> ObservableImageState -> Bool
observableStateEq = observableStateEquivalent

||| Observable append-only safety: no stored image exceeds authority.
export
observablePrefixSafe : ObservableImageState -> Bool
observablePrefixSafe obs =
  let localOk = pgImageIsPrefixOf (obsAuthImage obs) (obsLocalImage obs)
      actingPeers = filter (\info => elem (osd info) (osds (obsActing obs))) (obsPeerImages obs)
      peersOk = allPeerImagesPrefixOf (obsAuthImage obs) actingPeers
  in localOk && peersOk

||| Observable clean means there are no remaining objectwise gaps anywhere in
||| the acting set and the local image equals the authority image.
export
observableClean : ObservableImageState -> Bool
observableClean obs =
  let actingPeers = filter (\info => elem (osd info) (osds (obsActing obs))) (obsPeerImages obs)
  in observablePrefixSafe obs
     && null (obsPeerRecoveryPlans obs)
     && null (obsLocalRecoveryPlan obs)
     && pgImageIsRecovered (obsAuthImage obs) (obsLocalImage obs)
     && allPeerImagesRecovered (obsAuthImage obs) actingPeers

||| Observable recovering means the system is still safe, but at least one
||| local or peer gap remains.
export
observableRecovering : ObservableImageState -> Bool
observableRecovering obs =
  observablePrefixSafe obs
  && not (observableClean obs)
  && (not (null (obsPeerRecoveryPlans obs)) || not (null (obsLocalRecoveryPlan obs)))
