||| Image-aware append-only reducer.
|||
||| This module is the native objectwise execution boundary for the current
||| Idris model. It validates image events at the boundary and updates image
||| context bookkeeping directly.
module Peering.ImageProcess

import Peering.ImageInvariants
import Peering.ImageMachine
import Peering.Types
import Data.Nat
import Data.List
import Data.SortedMap
import Data.Maybe

%default total

isFresh : Epoch -> Epoch -> Bool
isFresh resetEp msgEp =
  case isLTE resetEp msgEp of
    Yes _ => True
    No _  => False

||| A one-step image-result record.
public export
record ImageStepResult where
  constructor MkImageStepResult
  ctx : ImageContext

||| Native raw events for the image-aware reducer.
public export
data ImageEvent : Type where
  ImageInitialize : PgId -> OsdId -> Epoch -> ActingSet -> ActingSet
                 -> PoolParams -> PGImageInfo -> List OsdId -> ImageEvent
  ImageAdvanceMap : Epoch -> ActingSet -> ActingSet -> PoolParams
                 -> List OsdId -> ImageEvent
  ImagePeerRecv : OsdId -> PeerImageInfo -> Epoch -> ImageEvent
  ImagePeerTimeout : OsdId -> ImageEvent
  ImageUpThruOk : Epoch -> ImageEvent
  ImageActivateCommitted : ImageEvent
  ImageRecoveryDone : OsdId -> Epoch -> ImageEvent
  ImageAllRecovered : Epoch -> List OsdId -> ImageEvent
  ImageReplicaActivate : OsdId -> PeerImageInfo -> Epoch -> ImageEvent
  ImageReplicaRecovDone : ObjectImage -> Epoch -> ImageEvent
  ImageDeleteStart : ImageEvent
  ImageDeleteDone : ImageEvent

||| Typed validation witness for a raw native image event.
public export
data ImageEventValidated : Epoch -> ImageEvent -> Type where
  ValidInitialize
    : {resetEpoch : Epoch}
   -> {pgid : PgId}
   -> {who : OsdId}
   -> {evtEpoch : Epoch}
   -> {acting : ActingSet}
   -> {upSet : ActingSet}
   -> {poolParams : PoolParams}
   -> {localInfo : PGImageInfo}
   -> {priorOsds : List OsdId}
   -> ImageEventValidated resetEpoch
        (ImageInitialize pgid who evtEpoch acting upSet poolParams localInfo priorOsds)
  ValidAdvanceMap
    : {resetEpoch : Epoch}
   -> {mapEpoch : Epoch}
   -> {acting : ActingSet}
   -> {upSet : ActingSet}
   -> {poolParams : PoolParams}
   -> {priorOsds : List OsdId}
   -> ImageEventValidated resetEpoch
        (ImageAdvanceMap mapEpoch acting upSet poolParams priorOsds)
  ValidPeerRecvZero
    : {resetEpoch : Epoch}
   -> {from : OsdId}
   -> {info : PeerImageInfo}
   -> ImageEventValidated resetEpoch (ImagePeerRecv from info 0)
  ValidPeerRecvFresh
    : {resetEpoch : Epoch}
   -> {from : OsdId}
   -> {info : PeerImageInfo}
   -> {queryEp : Epoch}
   -> (0 ok : isFresh resetEpoch queryEp = True)
   -> ImageEventValidated resetEpoch (ImagePeerRecv from info queryEp)
  ValidPeerTimeout
    : {resetEpoch : Epoch}
   -> {peer : OsdId}
   -> ImageEventValidated resetEpoch (ImagePeerTimeout peer)
  ValidUpThruOk
    : {resetEpoch : Epoch}
   -> {evtEpoch : Epoch}
   -> ImageEventValidated resetEpoch (ImageUpThruOk evtEpoch)
  ValidActivateCommitted
    : {resetEpoch : Epoch}
   -> ImageEventValidated resetEpoch ImageActivateCommitted
  ValidRecoveryDone
    : {resetEpoch : Epoch}
   -> {peer : OsdId}
   -> {recoveryEpoch : Epoch}
   -> (0 ok : isFresh resetEpoch recoveryEpoch = True)
   -> ImageEventValidated resetEpoch (ImageRecoveryDone peer recoveryEpoch)
  ValidAllRecovered
    : {resetEpoch : Epoch}
   -> {recoveryEpoch : Epoch}
   -> {peers : List OsdId}
   -> (0 ok : isFresh resetEpoch recoveryEpoch = True)
   -> ImageEventValidated resetEpoch (ImageAllRecovered recoveryEpoch peers)
  ValidReplicaActivate
    : {resetEpoch : Epoch}
   -> {from : OsdId}
   -> {info : PeerImageInfo}
   -> {activateEpoch : Epoch}
   -> (0 ok : isFresh resetEpoch activateEpoch = True)
   -> ImageEventValidated resetEpoch (ImageReplicaActivate from info activateEpoch)
  ValidReplicaRecovDone
    : {resetEpoch : Epoch}
   -> {recoveredImage : ObjectImage}
   -> {activateEpoch : Epoch}
   -> (0 ok : isFresh resetEpoch activateEpoch = True)
   -> ImageEventValidated resetEpoch (ImageReplicaRecovDone recoveredImage activateEpoch)
  ValidDeleteStart
    : {resetEpoch : Epoch}
   -> ImageEventValidated resetEpoch ImageDeleteStart
  ValidDeleteDone
    : {resetEpoch : Epoch}
   -> ImageEventValidated resetEpoch ImageDeleteDone

||| A validated image event is a checked raw event, not a second AST.
public export
data ImageValidatedEvent : Type where
  MkImageValidatedEvent
    : (checkedAgainst : Epoch)
   -> (rawEvent : ImageEvent)
   -> {0 valid : ImageEventValidated checkedAgainst rawEvent}
   -> ImageValidatedEvent

public export
validatedEventRaw : ImageValidatedEvent -> ImageEvent
validatedEventRaw (MkImageValidatedEvent _ rawEvent) = rawEvent

public export
validatedEventResetEpoch : ImageValidatedEvent -> Epoch
validatedEventResetEpoch (MkImageValidatedEvent checkedAgainst _) = checkedAgainst

||| Compatibility values for proof sites that reason about specific validated
||| no-op/control events.
public export
VActivateCommittedAt : Epoch -> ImageValidatedEvent
VActivateCommittedAt checkedAgainst =
  MkImageValidatedEvent checkedAgainst ImageActivateCommitted {valid = ValidActivateCommitted}

public export
VActivateCommitted : ImageValidatedEvent
VActivateCommitted = VActivateCommittedAt 0

public export
VDeleteStartAt : Epoch -> ImageValidatedEvent
VDeleteStartAt checkedAgainst =
  MkImageValidatedEvent checkedAgainst ImageDeleteStart {valid = ValidDeleteStart}

public export
VDeleteStart : ImageValidatedEvent
VDeleteStart = VDeleteStartAt 0

public export
VDeleteDoneAt : Epoch -> ImageValidatedEvent
VDeleteDoneAt checkedAgainst =
  MkImageValidatedEvent checkedAgainst ImageDeleteDone {valid = ValidDeleteDone}

public export
VDeleteDone : ImageValidatedEvent
VDeleteDone = VDeleteDoneAt 0

||| Replace the local image while preserving epoch metadata.
private
setLocalImagePreservingMeta : ObjectImage -> ImageContext -> ImageContext
setLocalImagePreservingMeta image ctx =
  let local = localImageInfo ctx
      newLocal : PGImageInfo
      newLocal = { image := image } local
      newCore : ImageCoreState
      newCore = { coreLocalImageInfo := newLocal } ctx.core
  in { core := newCore } ctx

||| Replace the local image and monotonically advance epoch metadata.
private
setLocalImageAtEpoch : ObjectImage -> Epoch -> ImageContext -> ImageContext
setLocalImageAtEpoch image evtEpoch ctx =
  let local = localImageInfo ctx
      updatedEpoch =
        if local.lastEpochStarted < evtEpoch
          then evtEpoch
          else local.lastEpochStarted
      updatedInterval =
        if local.lastIntervalStarted < evtEpoch
          then evtEpoch
          else local.lastIntervalStarted
      newLocal : PGImageInfo
      newLocal = { image := image
                 , lastEpochStarted := updatedEpoch
                 , lastIntervalStarted := updatedInterval
                 } local
      newCore : ImageCoreState
      newCore = { coreLocalImageInfo := newLocal } ctx.core
  in { core := newCore } ctx

private
activateCommittedCtx : ImageContext -> ImageContext
activateCommittedCtx ctx =
  let newCore : ImageCoreState
      newCore = { coreActivated := True } ctx.core
  in { core := newCore } ctx

||| Recompute authority and all recovery plans after updates.
private
refreshImageState : ImageContext -> ImageContext
refreshImageState = refreshImageDerived

private
recordPeerTimeout : OsdId -> ImageContext -> ImageContext
recordPeerTimeout peer ctx =
  let newBook : ImageBookkeeping
      newBook =
        { bookPeersResponded $= insertOsdSetLike peer
        , bookTimedOutProbes $= insertOsdSetLike peer
        } ctx.bookkeeping
  in { bookkeeping := newBook } ctx

private
inPeerInfoGathering : ImageContext -> Bool
inPeerInfoGathering imgCtx =
  isImagePrimary imgCtx &&
  (not (needUpThru imgCtx)) &&
  (pendingActChange imgCtx ||
   any (\osd => not (elem osd (peersResponded imgCtx))) (peersQueried imgCtx))

private
imageRecoveryTargets : ImageContext -> List OsdId
imageRecoveryTargets ctx =
  let remote = map (\plan => plan.target) (peerRecoveryPlans ctx)
  in if null (localRecoveryPlan ctx)
       then remote
       else nub (ctx.whoami :: remote)

private
isImageRecoveryTarget : OsdId -> ImageContext -> Bool
isImageRecoveryTarget peer ctx =
  peer == ctx.whoami
    || elem peer (imageRecoveryTargets ctx)
recordImageAuthorityFromPeer : OsdId -> PeerImageInfo -> ImageContext -> ImageContext
recordImageAuthorityFromPeer from info ctx =
  let safeInfo = { osd := from } info
      safeImage : ObjectImage
      safeImage =
        case safeInfo of
          MkPeerImageInfo _ image _ => image
      withPeer : ImageContext
      withPeer =
        let newCore : ImageCoreState
            newCore =
              { corePeerImages $= upsertPeerImageInfo safeInfo
              , coreAuthSources := authorityFromPeerImage safeInfo
              , coreAuthImage := safeImage
              } ctx.core
            newBook : ImageBookkeeping
            newBook = { bookPeersResponded $= insertOsdSetLike from } ctx.bookkeeping
        in { core := newCore, bookkeeping := newBook } ctx
  in refreshImageRecoveryPlans withPeer

private
adoptReplicaAuthorityImage : OsdId -> PeerImageInfo -> Epoch -> ImageContext -> ImageContext
adoptReplicaAuthorityImage from info actEp imgCtx =
  if actEp /= imgCtx.epoch
     || primary imgCtx.acting /= Just from
     || not (contains imgCtx.whoami imgCtx.acting)
    then imgCtx
    else
      let safeInfo = { osd := from } info
          auth = authorityFromPeerImage safeInfo
          authImage = authorityImageValues auth
          withAuth =
            let newCore : ImageCoreState
                newCore =
                  { coreAuthSources := auth
                  , coreAuthImage := authImage
                  } imgCtx.core
            in { core := newCore } imgCtx
          clampedLocal = clampImageTo authImage (localImageInfo withAuth).image
      in if prefixImage authImage (localImageInfo withAuth).image
           then refreshImageRecoveryPlans (setLocalImageAtEpoch clampedLocal actEp withAuth)
           else refreshImageRecoveryPlans (setLocalImagePreservingMeta clampedLocal withAuth)

private
recoverPeerToAuthority : OsdId -> ImageContext -> ImageContext
recoverPeerToAuthority peer imgCtx =
  let marked =
        let newBook : ImageBookkeeping
            newBook = { bookRecoveredPeers $= insertOsdSetLike peer } imgCtx.bookkeeping
        in { bookkeeping := newBook } imgCtx
      updated =
        if peer == imgCtx.whoami
          then refreshImageRecoveryPlans (setLocalImagePreservingMeta (authImage imgCtx) marked)
          else
            let oldLes =
                  case lookupPeerImageInfo peer marked of
                    Just info => info.lastEpochStarted
                    Nothing => 0
                recoveredInfo = MkPeerImageInfo peer (authImage imgCtx) oldLes
                newCore : ImageCoreState
                newCore =
                  { corePeerImages $= upsertPeerImageInfo recoveredInfo } marked.core
                newBook : ImageBookkeeping
                newBook =
                  { bookPeersResponded $= insertOsdSetLike peer } marked.bookkeeping
            in refreshImageRecoveryPlans
                 ({ core := newCore
                  , bookkeeping := newBook
                  } marked)
  in if null (peerRecoveryPlans updated) && null (localRecoveryPlan updated)
       then
         let newBook : ImageBookkeeping
             newBook = { bookRecoveredPeers := [] } updated.bookkeeping
         in { bookkeeping := newBook } updated
       else updated

private
applyReplicaRecoveryImage : ObjectImage -> Epoch -> ImageContext -> ImageContext
applyReplicaRecoveryImage recoveredImage actEp imgCtx =
  if actEp < lastPeeringReset imgCtx
     || actEp < (localImageInfo imgCtx).lastEpochStarted
    then imgCtx
    else
      let merged = joinImage (localImageInfo imgCtx).image recoveredImage
          clamped = clampImageTo (authImage imgCtx) merged
      in refreshImageRecoveryPlans (setLocalImageAtEpoch clamped actEp imgCtx)

private
localPeerImage : ImageContext -> PeerImageInfo
localPeerImage ctx = MkPeerImageInfo ctx.whoami
                                (localImageInfo ctx).image
                                (localImageInfo ctx).lastEpochStarted

private
lookupPeerImage : OsdId -> ImageContext -> Maybe PeerImageInfo
lookupPeerImage osd ctx =
  if osd == ctx.whoami
    then Just (localPeerImage ctx)
    else lookupPeerImageInfo osd ctx

private
peerIsCompleteForAuth : ObjectImage -> ImageContext -> OsdId -> Bool
peerIsCompleteForAuth auth ctx osd =
  case lookupPeerImage osd ctx of
    Nothing => False
    Just info => peerImageIsPrefixOf auth info

private
authorityPrimaryOsd : ImageContext -> OsdId
authorityPrimaryOsd ctx =
  case lookup 0 (authSources ctx) of
    Just authority => authorityOsd authority
    Nothing => ctx.whoami

private
buildDesiredActing : ImageContext -> ObjectImage -> List OsdId
buildDesiredActing ctx auth =
  let desiredPrimary =
        if lookupLength 0 (localImageInfo ctx).image < lookupLength 0 auth
           && authorityPrimaryOsd ctx /= ctx.whoami
           then authorityPrimaryOsd ctx
           else ctx.whoami
      allCandidates =
        nub (ctx.acting.osds ++ ctx.up.osds ++ priorOsds ctx)
      completePeers = filter (peerIsCompleteForAuth auth ctx) allCandidates
      withInfo = filter (\osd => isJust (lookupPeerImage osd ctx)) allCandidates
      pass1 = foldl (\acc, osd =>
               if elem osd acc
                 then acc
                 else if length acc >= ctx.pool.size
                      then acc
                      else acc ++ [osd]) [desiredPrimary] completePeers
      pass2 = foldl (\acc, osd =>
               if elem osd acc
                 then acc
                 else if length acc >= ctx.pool.size
                      then acc
                      else acc ++ [osd]) pass1 withInfo
  in pass2

private
needsActingChange : ImageContext -> List OsdId -> Bool
needsActingChange ctx want =
  let desiredPrimaryChange =
        case (want, primary ctx.acting) of
          (w :: _, Just old) => w /= old
          _ => True
      outsideCurrent = any (\osd => not (contains osd ctx.acting)) want
  in desiredPrimaryChange || outsideCurrent

private
haveEnoughForMinSize : ImageContext -> List OsdId -> Bool
haveEnoughForMinSize ctx want =
  length want >= ctx.pool.minSize

private
canActivateImage : ImageContext -> Bool
canActivateImage ctx =
  case isLTE ctx.pool.minSize (countAvailableImagePeers ctx) of
    Yes _ => True
    No _ => False

private
sameListMembers : Eq a => List a -> List a -> Bool
sameListMembers xs ys =
  let left = nub xs
      right = nub ys
  in all (\x => elem x right) left
     && all (\y => elem y left) right

||| Apply one acting/recovery decision step in the image model.
private
applyImageActingDecision : ImageContext -> ImageContext
applyImageActingDecision ctx =
  let auth = authImage ctx
  in if not (isImagePrimary ctx) then ctx
     else if not (haveEnoughImageInfo ctx)
            then
              let newBook : ImageBookkeeping
                  newBook =
                    { bookPendingActChange := pendingActChange ctx } ctx.bookkeeping
              in { bookkeeping := newBook } ctx
            else
              let want = buildDesiredActing ctx auth
                  actChange = needsActingChange ctx want
                  base : ImageContext
                  base =
                    let newBook : ImageBookkeeping
                        newBook =
                          { bookNeedUpThru := needUpThru ctx
                          , bookPendingActChange := False
                          } ctx.bookkeeping
                    in { bookkeeping := newBook } ctx
              in if actChange
                   then if haveEnoughForMinSize ctx want
                          then
                            let newBook : ImageBookkeeping
                                newBook =
                                  { bookPendingActChange := True } base.bookkeeping
                            in { bookkeeping := newBook } base
                          else base
                   else if (localImageInfo ctx).lastIntervalStarted < ctx.epoch &&
                           haveEnoughForMinSize ctx want
                          then
                            let newBook : ImageBookkeeping
                                newBook =
                                  { bookNeedUpThru := True
                                  , bookPendingActChange := False
                                  } base.bookkeeping
                            in { bookkeeping := newBook } base
                          else
                            let activationBase =
                                  let newBook : ImageBookkeeping
                                      newBook =
                                        { bookNeedUpThru := False
                                        , bookPendingActChange := False
                                        } ctx.bookkeeping
                                  in { bookkeeping := newBook } ctx
                                clampedLocal =
                                  if prefixImage auth (localImageInfo activationBase).image
                                     then clampImageTo auth (localImageInfo activationBase).image
                                     else (localImageInfo activationBase).image
                            in if canActivateImage activationBase
                                  then refreshImageRecoveryPlans
                                         (setLocalImageAtEpoch clampedLocal ctx.epoch activationBase)
                                  else activationBase

||| Check whether a peer timeout is sufficient to recompute acting decisions.
private
hasEnoughImageInfoAfterTimeout : OsdId -> ImageContext -> Bool
hasEnoughImageInfoAfterTimeout peer ctx =
  let allQueried =
        all (\osd => osd == peer || elem osd (peersResponded ctx)) (peersQueried ctx)
      allActing =
        all (\osd => osd == ctx.whoami || osd == peer || elem osd (peersResponded ctx))
            ctx.acting.osds
  in allQueried && allActing

private
initializeImageCtxFromInfo
  : PgId -> OsdId -> Epoch -> ActingSet -> ActingSet
 -> PoolParams -> PGImageInfo -> List OsdId -> ImageContext
initializeImageCtxFromInfo pgid whoami epoch acting up pool info priorOsds =
  let coreState =
        MkImageCoreState info [] emptyImage (fromList []) [] [] False
      bookState =
        MkImageBookkeeping [] [] [] [] [] False False epoch
      baseCtx = MkImageCtx pgid whoami epoch acting up pool coreState bookState
      filteredPrior = normalizeOsdSetLike (filter (\osd => osd /= whoami) priorOsds)
      probeSet =
        normalizeOsdSetLike $
          filter (\osd => osd /= whoami)
            (acting.osds ++ up.osds ++ filteredPrior)
      withPrior = if primary acting == Just whoami
                    then
                      let newBook : ImageBookkeeping
                          newBook =
                            { bookPriorOsds := filteredPrior
                            , bookPeersQueried := probeSet
                            } baseCtx.bookkeeping
                      in { bookkeeping := newBook } baseCtx
                    else
                      let newBook : ImageBookkeeping
                          newBook = { bookPriorOsds := filteredPrior } baseCtx.bookkeeping
                      in { bookkeeping := newBook } baseCtx
      initCtx =
        if primary acting == Just whoami
          then
            let selfImage = MkPeerImageInfo whoami info.image info.lastEpochStarted
                newCore : ImageCoreState
                newCore = { corePeerImages := upsertPeerImageInfo selfImage [] } withPrior.core
                newBook : ImageBookkeeping
                newBook = { bookPeersResponded := [whoami] } withPrior.bookkeeping
            in { core := newCore, bookkeeping := newBook } withPrior
          else withPrior
  in
    let initialized = refreshImageState initCtx
    in if isImagePrimary initialized
         then applyImageActingDecision initialized
         else initialized

||| Advance-map setup while preserving local image and clearing peering state.
private
setupAdvanceMapCtx : (newEpoch : Epoch) -> ActingSet -> ActingSet
                  -> PoolParams -> List OsdId -> ImageContext -> ImageContext
setupAdvanceMapCtx newEpoch newActing newUp newPool nextPriorOsds imgCtx =
  let
    newInterval = newActing.osds /= imgCtx.acting.osds || newUp.osds /= imgCtx.up.osds
    poolChanged = newPool /= imgCtx.pool
    nextIsPrimary = primary newActing == Just imgCtx.whoami
    updatedBook : ImageBookkeeping
    updatedBook =
      { bookLastPeeringReset := if newInterval then newEpoch else lastPeeringReset imgCtx
      , bookPriorOsds :=
          if newInterval
            then if nextIsPrimary
                   then normalizeOsdSetLike (filter (\osd => osd /= imgCtx.whoami) nextPriorOsds)
                   else []
            else normalizeOsdSetLike (priorOsds imgCtx)
      } imgCtx.bookkeeping
    baseCtx : ImageContext :=
      { epoch := newEpoch
      , acting := newActing
      , up := newUp
      , pool := newPool
      , bookkeeping := updatedBook
      } imgCtx
    resetCtx = if newInterval
      then resetImagePeeringState baseCtx
      else baseCtx
    probeSet = normalizeOsdSetLike (buildImageProbeSet resetCtx)
    withSelf =
      if isImagePrimary resetCtx && newInterval
        then
          let
            localPeer = MkPeerImageInfo resetCtx.whoami
                                       (localImageInfo resetCtx).image
                                       (localImageInfo resetCtx).lastEpochStarted
            newCore : ImageCoreState
            newCore = { corePeerImages := upsertPeerImageInfo localPeer (peerImages resetCtx) } resetCtx.core
            newBook : ImageBookkeeping
            newBook =
              { bookPeersQueried := probeSet
              , bookPeersResponded := [resetCtx.whoami]
              } resetCtx.bookkeeping
            updated : ImageContext
            updated = { core := newCore, bookkeeping := newBook } resetCtx
          in updated
        else resetCtx
    advanced =
      if not newInterval
        then if not (isImagePrimary withSelf)
               then withSelf
               else refreshImageState withSelf
        else refreshImageState withSelf
  in
  if isImagePrimary advanced && (newInterval || poolChanged || pendingActChange advanced)
    then applyImageActingDecision advanced
    else advanced

||| Validation for native image events.
export
%inline
validateNativeImageEvent : (resetEpoch : Epoch) -> ImageEvent -> Maybe ImageValidatedEvent
validateNativeImageEvent resetEpoch (ImageInitialize pgid who epoch act up pool info prior) =
  Just (MkImageValidatedEvent resetEpoch
          (ImageInitialize pgid who epoch act up pool info prior)
          {valid = ValidInitialize})
validateNativeImageEvent resetEpoch (ImageAdvanceMap ep act up pool prior) =
  Just (MkImageValidatedEvent resetEpoch
          (ImageAdvanceMap ep act up pool prior)
          {valid = ValidAdvanceMap})
validateNativeImageEvent resetEpoch (ImagePeerRecv from info 0) =
  Just (MkImageValidatedEvent resetEpoch
          (ImagePeerRecv from info 0)
          {valid = ValidPeerRecvZero})
validateNativeImageEvent resetEpoch (ImagePeerRecv from info (S queryEp))
  with (isFresh resetEpoch (S queryEp)) proof freshEq
  validateNativeImageEvent resetEpoch (ImagePeerRecv from info (S queryEp)) | False =
    Nothing
  validateNativeImageEvent resetEpoch (ImagePeerRecv from info (S queryEp)) | True =
    Just (MkImageValidatedEvent resetEpoch
            (ImagePeerRecv from info (S queryEp))
            {valid = ValidPeerRecvFresh freshEq})
validateNativeImageEvent resetEpoch (ImagePeerTimeout peer) =
  Just (MkImageValidatedEvent resetEpoch
          (ImagePeerTimeout peer)
          {valid = ValidPeerTimeout})
validateNativeImageEvent resetEpoch (ImageUpThruOk ep) =
  Just (MkImageValidatedEvent resetEpoch
          (ImageUpThruOk ep)
          {valid = ValidUpThruOk})
validateNativeImageEvent resetEpoch ImageActivateCommitted =
  Just (MkImageValidatedEvent resetEpoch
          ImageActivateCommitted
          {valid = ValidActivateCommitted})
validateNativeImageEvent resetEpoch (ImageRecoveryDone peer recEp)
  with (isFresh resetEpoch recEp) proof freshEq
  validateNativeImageEvent resetEpoch (ImageRecoveryDone peer recEp) | False =
    Nothing
  validateNativeImageEvent resetEpoch (ImageRecoveryDone peer recEp) | True =
    Just (MkImageValidatedEvent resetEpoch
            (ImageRecoveryDone peer recEp)
            {valid = ValidRecoveryDone freshEq})
validateNativeImageEvent resetEpoch (ImageAllRecovered recEp peers)
  with (isFresh resetEpoch recEp) proof freshEq
  validateNativeImageEvent resetEpoch (ImageAllRecovered recEp peers) | False =
    Nothing
  validateNativeImageEvent resetEpoch (ImageAllRecovered recEp peers) | True =
    Just (MkImageValidatedEvent resetEpoch
            (ImageAllRecovered recEp peers)
            {valid = ValidAllRecovered freshEq})
validateNativeImageEvent resetEpoch (ImageReplicaActivate from info actEp)
  with (isFresh resetEpoch actEp) proof freshEq
  validateNativeImageEvent resetEpoch (ImageReplicaActivate from info actEp) | False =
    Nothing
  validateNativeImageEvent resetEpoch (ImageReplicaActivate from info actEp) | True =
    Just (MkImageValidatedEvent resetEpoch
            (ImageReplicaActivate from info actEp)
            {valid = ValidReplicaActivate freshEq})
validateNativeImageEvent resetEpoch (ImageReplicaRecovDone image actEp)
  with (isFresh resetEpoch actEp) proof freshEq
  validateNativeImageEvent resetEpoch (ImageReplicaRecovDone image actEp) | False =
    Nothing
  validateNativeImageEvent resetEpoch (ImageReplicaRecovDone image actEp) | True =
    Just (MkImageValidatedEvent resetEpoch
            (ImageReplicaRecovDone image actEp)
            {valid = ValidReplicaRecovDone freshEq})
validateNativeImageEvent resetEpoch ImageDeleteStart =
  Just (MkImageValidatedEvent resetEpoch
          ImageDeleteStart
          {valid = ValidDeleteStart})
validateNativeImageEvent resetEpoch ImageDeleteDone =
  Just (MkImageValidatedEvent resetEpoch
          ImageDeleteDone
          {valid = ValidDeleteDone})

||| Execute one validated step through the image reducer.
private
runValidated : ImageContext -> ImageValidatedEvent -> ImageContext
runValidated imgCtx (MkImageValidatedEvent _ evt) = case evt of
  ImageInitialize pgid whoami epoch acting up pool info priorOsds =>
    initializeImageCtxFromInfo pgid whoami epoch acting up pool info priorOsds
  ImageAdvanceMap newEpoch newActing newUp newPool priorOsds =>
    setupAdvanceMapCtx newEpoch newActing newUp newPool priorOsds imgCtx
  ImagePeerRecv _ _ _ =>
    imgCtx
  ImagePeerTimeout peer =>
    imgCtx
  ImageUpThruOk ep =>
    if ep /= imgCtx.epoch
       || not (isImagePrimary imgCtx)
       || not (haveEnoughImageInfo imgCtx)
       || (localImageInfo imgCtx).lastIntervalStarted >= ep
       then imgCtx
       else
         let withUpThruNoMetadata =
               let newLocal : PGImageInfo
                   newLocal =
                     { lastIntervalStarted := if (localImageInfo imgCtx).lastIntervalStarted < ep
                                                then ep
                                                else (localImageInfo imgCtx).lastIntervalStarted
                     } (localImageInfo imgCtx)
                   newCore : ImageCoreState
                   newCore = { coreLocalImageInfo := newLocal } imgCtx.core
                   newBook : ImageBookkeeping
                   newBook = { bookNeedUpThru := False } imgCtx.bookkeeping
               in { core := newCore, bookkeeping := newBook } imgCtx
         in if not (isImagePrimary withUpThruNoMetadata)
              then withUpThruNoMetadata
              else
                let decided = applyImageActingDecision (refreshImageState withUpThruNoMetadata)
                in if pendingActChange decided || not (canActivateImage decided)
                     then decided
                     else setLocalImageAtEpoch (localImageInfo decided).image ep decided
  ImageActivateCommitted =>
    activateCommittedCtx imgCtx
  ImageRecoveryDone peer _ =>
    imgCtx
  ImageAllRecovered _ peers =>
    imgCtx
  ImageReplicaActivate from info actEp =>
    adoptReplicaAuthorityImage from info actEp imgCtx
  ImageReplicaRecovDone recoveredImage actEp =>
    applyReplicaRecoveryImage recoveredImage actEp imgCtx
  ImageDeleteStart =>
    imgCtx
  ImageDeleteDone =>
    imgCtx

||| Execute one validated step through the image reducer.
export
processImageValidated : (ctx : ImageContext) -> ImageValidatedEvent -> ImageStepResult
processImageValidated imgCtx (MkImageValidatedEvent _ ImageDeleteStart) =
  MkImageStepResult imgCtx
processImageValidated imgCtx (MkImageValidatedEvent _ ImageDeleteDone) =
  MkImageStepResult imgCtx
processImageValidated imgCtx (MkImageValidatedEvent _ ImageActivateCommitted) =
  MkImageStepResult (activateCommittedCtx imgCtx)
processImageValidated imgCtx validEvt@(MkImageValidatedEvent _ evt) =
  case evt of
    ImagePeerRecv from info _ =>
      if not (isKnownPeerImage from imgCtx)
        then MkImageStepResult imgCtx
        else MkImageStepResult (applyImageActingDecision (recordPeerImage ({ osd := from } info) imgCtx))
    ImagePeerTimeout peer =>
      if not (inPeerInfoGathering imgCtx)
        then MkImageStepResult imgCtx
        else
          let timedOutCtx = recordPeerTimeout peer imgCtx
          in if hasEnoughImageInfoAfterTimeout peer timedOutCtx
               then MkImageStepResult (applyImageActingDecision timedOutCtx)
               else MkImageStepResult timedOutCtx
    ImageRecoveryDone peer _ =>
      if not (isImageRecoveryTarget peer imgCtx)
        then MkImageStepResult imgCtx
        else MkImageStepResult (recoverPeerToAuthority peer imgCtx)
    ImageAllRecovered _ peers =>
      let completed = nub peers
          relevant = all (\peer => isImageRecoveryTarget peer imgCtx) completed
          exactCompletion =
            sameListMembers (completed ++ recoveredPeers imgCtx)
                            (imageRecoveryTargets imgCtx)
      in if not relevant || not exactCompletion
           then MkImageStepResult imgCtx
           else MkImageStepResult (foldl (flip recoverPeerToAuthority) imgCtx completed)
    _ =>
      MkImageStepResult (runValidated imgCtx validEvt)

||| Validated delete-start is currently a no-op.
public export
processImageValidatedDeleteStartCtx
  : (ctx : ImageContext)
 -> (processImageValidated ctx VDeleteStart).ctx = ctx
processImageValidatedDeleteStartCtx ctx = Refl

public export
processImageValidatedDeleteStartStep
  : (ctx : ImageContext)
 -> processImageValidated ctx VDeleteStart = MkImageStepResult ctx
processImageValidatedDeleteStartStep ctx = Refl

||| Validated delete-done is currently a no-op.
public export
processImageValidatedDeleteDoneCtx
  : (ctx : ImageContext)
 -> (processImageValidated ctx VDeleteDone).ctx = ctx
processImageValidatedDeleteDoneCtx ctx = Refl

public export
processImageValidatedDeleteDoneStep
  : (ctx : ImageContext)
 -> processImageValidated ctx VDeleteDone = MkImageStepResult ctx
processImageValidatedDeleteDoneStep ctx = Refl

||| Validated activate-committed only flips the activation bit.
public export
processImageValidatedActivateCommittedCtx
  : (ctx : ImageContext)
 -> (processImageValidated ctx VActivateCommitted).ctx
    = activateCommittedCtx ctx
processImageValidatedActivateCommittedCtx ctx = Refl

||| Execute one native image event through the objectwise reducer boundary.
export
processNativeImage : (ctx : ImageContext) -> ImageEvent -> ImageStepResult
processNativeImage imgCtx ImageDeleteStart =
  MkImageStepResult imgCtx
processNativeImage imgCtx ImageDeleteDone =
  MkImageStepResult imgCtx
processNativeImage imgCtx ImageActivateCommitted =
  MkImageStepResult (activateCommittedCtx imgCtx)
processNativeImage imgCtx evt =
  case validateNativeImageEvent (lastPeeringReset imgCtx) evt of
    Nothing => MkImageStepResult imgCtx
    Just validEvt => processImageValidated imgCtx validEvt

||| Native delete-start validates directly to the no-op validated step.
public export
processNativeImageDeleteStartCtx
  : (ctx : ImageContext)
 -> (processNativeImage ctx ImageDeleteStart).ctx = ctx
processNativeImageDeleteStartCtx ctx = Refl

public export
processNativeImageDeleteStartStep
  : (ctx : ImageContext)
 -> processNativeImage ctx ImageDeleteStart = MkImageStepResult ctx
processNativeImageDeleteStartStep ctx = Refl

||| Native delete-done validates directly to the no-op validated step.
public export
processNativeImageDeleteDoneCtx
  : (ctx : ImageContext)
 -> (processNativeImage ctx ImageDeleteDone).ctx = ctx
processNativeImageDeleteDoneCtx ctx = Refl

public export
processNativeImageDeleteDoneStep
  : (ctx : ImageContext)
 -> processNativeImage ctx ImageDeleteDone = MkImageStepResult ctx
processNativeImageDeleteDoneStep ctx = Refl

||| Native activate-committed validates directly to the validated activation
||| step.
public export
processNativeImageActivateCommittedCtx
  : (ctx : ImageContext)
 -> (processNativeImage ctx ImageActivateCommitted).ctx
    = activateCommittedCtx ctx
processNativeImageActivateCommittedCtx ctx = Refl

||| Execute a native image trace through the objectwise reducer boundary.
export
%inline
processNativeImageTrace : ImageContext -> List ImageEvent -> ImageContext
processNativeImageTrace ctx [] = ctx
processNativeImageTrace ctx (evt :: evts) =
  processNativeImageTrace (processNativeImage ctx evt).ctx evts

export
processNativeImageTraceNil : (ctx : ImageContext) -> processNativeImageTrace ctx [] = ctx
processNativeImageTraceNil ctx = Refl

export
processNativeImageTraceCons
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> (evts : List ImageEvent)
 -> processNativeImageTrace ctx (evt :: evts)
    = processNativeImageTrace (processNativeImage ctx evt).ctx evts
processNativeImageTraceCons ctx evt evts = Refl

||| Check whether image invariants are preserved by one native image step.
export
%inline
processNativeImagePreservesImageInvariant : (ctx : ImageContext) -> ImageEvent -> Bool
processNativeImagePreservesImageInvariant imgCtx evt =
  if imageContextInvariant imgCtx
    then imageContextInvariant (processNativeImage imgCtx evt).ctx
    else False

||| Execute a validated trace through the migration wrapper.
export
%inline
processImageValidatedTrace : ImageContext -> List ImageValidatedEvent -> ImageContext
processImageValidatedTrace ctx [] = ctx
processImageValidatedTrace ctx (evt :: evts) =
  processImageValidatedTrace (processImageValidated ctx evt).ctx evts

export
processImageValidatedTraceNil : (ctx : ImageContext) -> processImageValidatedTrace ctx [] = ctx
processImageValidatedTraceNil ctx = Refl

export
processImageValidatedTraceCons
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> (evts : List ImageValidatedEvent)
 -> processImageValidatedTrace ctx (evt :: evts)
    = processImageValidatedTrace (processImageValidated ctx evt).ctx evts
processImageValidatedTraceCons ctx evt evts = Refl

||| Check whether image invariants are preserved by one validated migration step.
export
%inline
processImageValidatedPreservesImageInvariant : (ctx : ImageContext) -> ImageValidatedEvent -> Bool
processImageValidatedPreservesImageInvariant imgCtx evt =
  if imageContextInvariant imgCtx
    then imageContextInvariant (processImageValidated imgCtx evt).ctx
    else False
