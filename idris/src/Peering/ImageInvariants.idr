||| Executable objectwise invariants for the image-aware peering scaffold.
|||
||| These checks are intentionally Boolean for now. They give the next migration
||| phase a precise target before dependent proofs are rebuilt around the
||| multi-object state.
module Peering.ImageInvariants

import Data.List
import Data.Maybe
import Data.SortedMap
import Peering.ImageMachine
import Peering.Types

%default total

export
normalizeRecoveries : List ObjRecovery -> List ObjRecovery
normalizeRecoveries =
  sortBy (\left, right =>
            compare (obj left, fromLen left, toLen left)
                    (obj right, fromLen right, toLen right))

export
normalizePeerImages : List PeerImageInfo -> List PeerImageInfo
normalizePeerImages =
  sortBy (\left, right => compare left.osd right.osd)

export
normalizeRecoveryPlans : List PeerRecoveryPlan -> List PeerRecoveryPlan
normalizeRecoveryPlans =
  sortBy (\left, right => compare left.target right.target)
  . map (\plan => { recoveries := normalizeRecoveries plan.recoveries } plan)

export
normalizeObservableRecoveries : List ObjRecovery -> List ObjRecovery
normalizeObservableRecoveries = normalizeRecoveries

export
normalizeObservablePeerImages : List PeerImageInfo -> List PeerImageInfo
normalizeObservablePeerImages = normalizePeerImages

export
normalizeObservablePeerRecoveryPlans : List PeerRecoveryPlan -> List PeerRecoveryPlan
normalizeObservablePeerRecoveryPlans = normalizeRecoveryPlans

public export
record ObservableImageState where
  constructor MkObservableImageState
  obsPgid              : PgId
  obsWhoami            : OsdId
  obsEpoch             : Epoch
  obsActing            : ActingSet
  obsUp                : ActingSet
  obsPool              : PoolParams
  obsLocalInfo         : PGImageInfo
  obsPeerImages        : List PeerImageInfo
  obsAuthImage         : ObjectImage
  obsPeerRecoveryPlans : List PeerRecoveryPlan
  obsLocalRecoveryPlan : List ObjRecovery
  obsActivated         : Bool

export
normalizeObservableState : ObservableImageState -> ObservableImageState
normalizeObservableState st =
  MkObservableImageState st.obsPgid
                         st.obsWhoami
                         st.obsEpoch
                         st.obsActing
                         st.obsUp
                         st.obsPool
                         st.obsLocalInfo
                         (normalizePeerImages st.obsPeerImages)
                         st.obsAuthImage
                         (normalizeRecoveryPlans st.obsPeerRecoveryPlans)
                         (normalizeRecoveries st.obsLocalRecoveryPlan)
                         st.obsActivated

||| Reduced projection used for the semantic-boundary safety layer and the
||| upcoming one-step refinement theorem.
export
observeImageState : ImageContext -> ObservableImageState
observeImageState (MkImageCtx pgid whoami epoch acting up pool coreState bookState) =
  normalizeObservableState $
    MkObservableImageState pgid
                           whoami
                           epoch
                           acting
                           up
                           pool
                           (coreLocalImageInfo coreState)
                           (corePeerImages coreState)
                           (coreAuthImage coreState)
                           (corePeerRecoveryPlans coreState)
                           (coreLocalRecoveryPlan coreState)
                           (coreActivated coreState)

export
normalizeContextForObservation : ImageContext -> ObservableImageState
normalizeContextForObservation = normalizeObservableState . observeImageState

||| Constructor-level expansion of the reduced observation.
public export
observeImageStateOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> observeImageState
      (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = MkObservableImageState pgid whoami epoch acting up pool
                             (localImageInfo (MkImageCtx pgid whoami epoch acting up pool coreState bookState))
                             (normalizeObservablePeerImages (peerImages (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                             (authImage (MkImageCtx pgid whoami epoch acting up pool coreState bookState))
                             (normalizeObservablePeerRecoveryPlans (peerRecoveryPlans (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                             (normalizeObservableRecoveries (localRecoveryPlan (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                             (activated (MkImageCtx pgid whoami epoch acting up pool coreState bookState))
observeImageStateOnCtor pgid whoami epoch acting up pool coreState bookState =
  rewrite localImageInfoOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite peerImagesOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite authImageOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite peerRecoveryPlansOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite localRecoveryPlanOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite activatedOnCtor pgid whoami epoch acting up pool coreState bookState in
    Refl

observablePeerImageOrEmpty : ObservableImageState -> OsdId -> PeerImageInfo
observablePeerImageOrEmpty st osd =
  if osd == st.obsWhoami
     then MkPeerImageInfo osd st.obsLocalInfo.image st.obsLocalInfo.lastEpochStarted
     else fromMaybe (MkPeerImageInfo osd emptyImage 0)
                    (find (\info => info.osd == osd) st.obsPeerImages)

observableActingPeerImages : ObservableImageState -> List PeerImageInfo
observableActingPeerImages st =
  map (observablePeerImageOrEmpty st)
      (filter (\osd => osd /= st.obsWhoami) st.obsActing.osds)

observableAuthorityBackedByKnownPeer : ObservableImageState -> Bool
observableAuthorityBackedByKnownPeer st =
  let backedByKnown =
        all (\(obj, len) =>
              lookupLength obj st.obsLocalInfo.image == len
              || any (\peer => lookupLength obj peer.image == len) st.obsPeerImages)
            (imageToList st.obsAuthImage)
      backedByActingPrimary =
        case primary st.obsActing of
          Nothing => null (imageToList st.obsAuthImage)
          Just prim => prim /= st.obsWhoami
  in backedByKnown || backedByActingPrimary

observablePeerRecoveryPlansCorrect : ObservableImageState -> Bool
observablePeerRecoveryPlansCorrect st =
  st.obsPeerRecoveryPlans
    == normalizeObservablePeerRecoveryPlans
         (buildPeerRecoveryPlans st.obsAuthImage (observableActingPeerImages st))

observableLocalRecoveryPlanCorrect : ObservableImageState -> Bool
observableLocalRecoveryPlanCorrect st =
  st.obsLocalRecoveryPlan
    == normalizeObservableRecoveries
         (pgImageRecoveryPlan st.obsAuthImage st.obsLocalInfo)

observableServingSafe : ObservableImageState -> Bool
observableServingSafe st =
  if st.obsActivated
     then pgImageIsPrefixOf st.obsAuthImage st.obsLocalInfo
          && allPeerImagesPrefixOf st.obsAuthImage (observableActingPeerImages st)
     else True

||| Executable safety check over the reduced semantic boundary that the C++
||| implementation will refine.
export
observableImageStateSafe : ObservableImageState -> Bool
observableImageStateSafe st =
  pgImageIsPrefixOf st.obsAuthImage st.obsLocalInfo
  && allPeerImagesPrefixOf st.obsAuthImage (observableActingPeerImages st)
  && observableAuthorityBackedByKnownPeer st
  && observablePeerRecoveryPlansCorrect st
  && observableLocalRecoveryPlanCorrect st
  && observableServingSafe st

||| Convenience wrapper for the reduced semantic boundary on a full context.
export
contextObservableStateSafe : ImageContext -> Bool
contextObservableStateSafe (MkImageCtx pgid whoami epoch acting up pool coreState bookState) =
  observableImageStateSafe
    (MkObservableImageState pgid whoami epoch acting up pool
                            (coreLocalImageInfo coreState)
                            (normalizeObservablePeerImages (corePeerImages coreState))
                            (coreAuthImage coreState)
                            (normalizeObservablePeerRecoveryPlans (corePeerRecoveryPlans coreState))
                            (normalizeObservableRecoveries (coreLocalRecoveryPlan coreState))
                            (coreActivated coreState))

||| Constructor-level expansion of the reduced observable safety wrapper.
public export
contextObservableStateSafeOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> contextObservableStateSafe
      (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = observableImageStateSafe
        (MkObservableImageState pgid whoami epoch acting up pool
                                (localImageInfo (MkImageCtx pgid whoami epoch acting up pool coreState bookState))
                                (normalizeObservablePeerImages (peerImages (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                                (authImage (MkImageCtx pgid whoami epoch acting up pool coreState bookState))
                                (normalizeObservablePeerRecoveryPlans (peerRecoveryPlans (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                                (normalizeObservableRecoveries (localRecoveryPlan (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
                                (activated (MkImageCtx pgid whoami epoch acting up pool coreState bookState)))
contextObservableStateSafeOnCtor pgid whoami epoch acting up pool coreState bookState =
  rewrite localImageInfoOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite peerImagesOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite authImageOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite peerRecoveryPlansOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite localRecoveryPlanOnCtor pgid whoami epoch acting up pool coreState bookState in
  rewrite activatedOnCtor pgid whoami epoch acting up pool coreState bookState in
    Refl

showBoolFlag : Bool -> String
showBoolFlag True = "1"
showBoolFlag False = "0"

||| Exact reduced-observable breakdown for debugging proof-facing failures.
export
showContextObservableStateBreakdown : ImageContext -> String
showContextObservableStateBreakdown ctx =
  let st = observeImageState ctx in
  "reducedObservable[prefixLocal="
    ++ showBoolFlag (pgImageIsPrefixOf st.obsAuthImage st.obsLocalInfo)
    ++ " prefixActing="
    ++ showBoolFlag (allPeerImagesPrefixOf st.obsAuthImage (observableActingPeerImages st))
    ++ " authorityBacked="
    ++ showBoolFlag (observableAuthorityBackedByKnownPeer st)
    ++ " peerPlans="
    ++ showBoolFlag (observablePeerRecoveryPlansCorrect st)
    ++ " localPlan="
    ++ showBoolFlag (observableLocalRecoveryPlanCorrect st)
    ++ " serving="
    ++ showBoolFlag (observableServingSafe st)
    ++ "]"

||| Central same-image-based semantic check between a stored authority image
||| and an authority-source map.
export
%inline
authorityImageSemanticallyMatches : ObjectImage -> AuthorityImage -> Bool
authorityImageSemanticallyMatches image auth =
  image == authorityImageValues auth
  || sameImage image (authorityImageValues auth)

public export
authorityImageSemanticallyMatchesUnfold
  : (image : ObjectImage)
 -> (auth : AuthorityImage)
 -> authorityImageSemanticallyMatches image auth
    = (image == authorityImageValues auth
       || sameImage image (authorityImageValues auth))
authorityImageSemanticallyMatchesUnfold image auth = Refl

||| The image induced by stored authority sources should semantically match the
||| recomputed authority image from known peers.
export
%inline
authorityStoredSourcesMatchKnownPeers : ImageContext -> Bool
authorityStoredSourcesMatchKnownPeers ctx =
  authorityImageSemanticallyMatches
    (authorityImageValues (authSources ctx))
    (authoritativeSources (knownPeerImages ctx))

public export
authorityStoredSourcesMatchKnownPeersUnfold
  : (ctx : ImageContext)
 -> authorityStoredSourcesMatchKnownPeers ctx
    = authorityImageSemanticallyMatches
        (authorityImageValues (authSources ctx))
        (authoritativeSources (knownPeerImages ctx))
authorityStoredSourcesMatchKnownPeersUnfold ctx = Refl

||| The current authoritative image should semantically match the recomputed
||| authority image from known peers.
export
%inline
authorityCurrentImageMatchesKnownPeers : ImageContext -> Bool
authorityCurrentImageMatchesKnownPeers ctx =
  authorityImageSemanticallyMatches
    (authImage ctx)
    (authoritativeSources (knownPeerImages ctx))

public export
authorityCurrentImageMatchesKnownPeersUnfold
  : (ctx : ImageContext)
 -> authorityCurrentImageMatchesKnownPeers ctx
    = authorityImageSemanticallyMatches
        (authImage ctx)
        (authoritativeSources (knownPeerImages ctx))
authorityCurrentImageMatchesKnownPeersUnfold ctx = Refl

||| The stored authority-source map should structurally agree with
||| recomputation from known peers. This is a stronger executable proxy for the
||| older per-entry backing check.
export
%inline
authorityEntriesBackedByKnownPeers : ImageContext -> Bool
authorityEntriesBackedByKnownPeers ctx =
  sameAuthorityImage (authSources ctx) (authoritativeSources (knownPeerImages ctx))

public export
authorityEntriesBackedByKnownPeersUnfold
  : (ctx : ImageContext)
 -> authorityEntriesBackedByKnownPeers ctx
    = sameAuthorityImage (authSources ctx) (authoritativeSources (knownPeerImages ctx))
authorityEntriesBackedByKnownPeersUnfold ctx = Refl

||| The authority state is derived from known peers when both same-image
||| semantic checks hold and every authority entry is backed by known peer
||| state.
export
%inline
authorityDerivedFromKnownPeers : ImageContext -> Bool
authorityDerivedFromKnownPeers ctx =
  authorityStoredSourcesMatchKnownPeers ctx
  && authorityCurrentImageMatchesKnownPeers ctx
  && authorityEntriesBackedByKnownPeers ctx

public export
authorityDerivedFromKnownPeersUnfold
  : (ctx : ImageContext)
 -> authorityDerivedFromKnownPeers ctx
    = (authorityStoredSourcesMatchKnownPeers ctx
       && authorityCurrentImageMatchesKnownPeers ctx
       && authorityEntriesBackedByKnownPeers ctx)
authorityDerivedFromKnownPeersUnfold ctx = Refl

||| Fallback authority check used when the acting primary is remote and the
||| local model only observes its chosen authority image.
export
%inline
authorityMatchesActingPrimaryFallback : ImageContext -> Bool
authorityMatchesActingPrimaryFallback ctx =
  case primary ctx.acting of
    Nothing => null (Data.SortedMap.toList (authSources ctx))
    Just prim =>
      not (isImagePrimary ctx)
        && authorityImageSemanticallyMatches (authImage ctx) (authSources ctx)
        && all (\(obj, auth) =>
                  auth.authorityOsd == prim
                    && authorityLength auth == lookupLength obj (authImage ctx))
               (Data.SortedMap.toList (authSources ctx))

||| The stored authority map should agree with recomputation from known peers.
export
%inline
authorityDerivedCorrectly : ImageContext -> Bool
authorityDerivedCorrectly ctx =
  authorityDerivedFromKnownPeers ctx || authorityMatchesActingPrimaryFallback ctx

public export
authorityDerivedCorrectlyUnfold
  : (ctx : ImageContext)
 -> authorityDerivedCorrectly ctx
    = (authorityDerivedFromKnownPeers ctx || authorityMatchesActingPrimaryFallback ctx)
authorityDerivedCorrectlyUnfold ctx = Refl

||| The local image must remain a prefix of the authoritative image.
export
localImageSafe : ImageContext -> Bool
localImageSafe ctx = pgImageIsPrefixOf (authImage ctx) (localImageInfo ctx)

||| All acting replicas must remain prefixes of the authoritative image.
export
actingImagesSafe : ImageContext -> Bool
actingImagesSafe ctx = allPeerImagesPrefixOf (authImage ctx) (actingImages ctx)

||| Every stored peer recovery plan should match the gaps induced by auth image.
export
peerRecoveryPlansCorrect : ImageContext -> Bool
peerRecoveryPlansCorrect ctx =
  let expected = buildPeerRecoveryPlans (authImage ctx) (actingReplicaImages ctx)
  in peerRecoveryPlans ctx == expected

||| The stored local recovery plan should match the current local image gaps.
export
localRecoveryPlanCorrect : ImageContext -> Bool
localRecoveryPlanCorrect ctx =
  localRecoveryPlan ctx == pgImageRecoveryPlan (authImage ctx) (localImageInfo ctx)

||| Core objectwise safety condition for the image-aware context.
export
imageContextInvariant : ImageContext -> Bool
imageContextInvariant ctx =
  authorityDerivedCorrectly ctx
  && localImageSafe ctx
  && actingImagesSafe ctx
  && peerRecoveryPlansCorrect ctx
  && localRecoveryPlanCorrect ctx

||| A clean image context has no pending recovery and all acting replicas match
||| the authoritative image pointwise.
export
imageContextClean : ImageContext -> Bool
imageContextClean ctx =
  imageContextInvariant ctx
  && null (peerRecoveryPlans ctx)
  && null (localRecoveryPlan ctx)
  && allPeerImagesRecovered (authImage ctx) (actingImages ctx)
  && pgImageIsRecovered (authImage ctx) (localImageInfo ctx)

||| A recovering image context still satisfies safety but has remaining object
||| recovery work for at least one acting replica or the local image.
export
imageContextRecovering : ImageContext -> Bool
imageContextRecovering ctx =
  let peerPlans = peerRecoveryPlans ctx
      localPlan = localRecoveryPlan ctx
  in imageContextInvariant ctx
     && not (imageContextClean ctx)
     && (not (null peerPlans) || not (null localPlan))

||| Authority must not invent bytes beyond what some known peer currently
||| exposes. This is the core append-only safety boundary for authority choice.
export
authorityBackedByKnownPeer : ImageContext -> Bool
authorityBackedByKnownPeer ctx =
  let backedByKnown =
        all (\(obj, auth) =>
              any (\peer => lookupLength obj peer.image == authorityLength auth)
                  (knownPeerImages ctx))
            (Data.SortedMap.toList (authSources ctx))
      backedByActingPrimary =
        case primary ctx.acting of
          Nothing => null (Data.SortedMap.toList (authSources ctx))
          Just prim =>
            not (isImagePrimary ctx)
              && all (\(obj, auth) =>
                        auth.authorityOsd == prim
                          && authorityLength auth == lookupLength obj (authImage ctx))
                     (Data.SortedMap.toList (authSources ctx))
  in backedByKnown || backedByActingPrimary

||| Every stored peer recovery plan must target an acting replica that is
||| strictly behind on at least one object.
export
peerRecoveryPlansTargetRealGaps : ImageContext -> Bool
peerRecoveryPlansTargetRealGaps ctx =
  all (\plan =>
        let peer = actingPeerImageOrEmpty ctx plan.target
        in not (null plan.recoveries)
           && elem plan.target ctx.acting.osds
           && not (peerImageIsRecovered (authImage ctx) peer))
      (peerRecoveryPlans ctx)

||| When the local recovery plan is empty, the local image must already match
||| the authoritative image pointwise.
export
localRecoveryPlanWitnessesGap : ImageContext -> Bool
localRecoveryPlanWitnessesGap ctx =
  if null (localRecoveryPlan ctx)
     then pgImageIsRecovered (authImage ctx) (localImageInfo ctx)
     else not (pgImageIsRecovered (authImage ctx) (localImageInfo ctx))

||| Observable append-only serving safety: once the PG is activated, every
||| acting replica and the local image remain prefixes of the authority image.
export
activatedServingSafe : ImageContext -> Bool
activatedServingSafe ctx =
  if activated ctx
     then localImageSafe ctx && actingImagesSafe ctx
     else True

||| Strengthened executable safety bundle for the upcoming observable-state
||| refinement proof.
export
imageSemanticBoundarySafe : ImageContext -> Bool
imageSemanticBoundarySafe ctx =
  imageContextInvariant ctx
  && authorityBackedByKnownPeer ctx
  && peerRecoveryPlansTargetRealGaps ctx
  && localRecoveryPlanWitnessesGap ctx
  && activatedServingSafe ctx
  && contextObservableStateSafe ctx
