||| Image-aware machine scaffolding for the many-object peering roadmap.
|||
||| This is the active objectwise state layer for the Idris model.
module Peering.ImageMachine

import Data.List
import Data.Maybe
import Data.SortedMap
import Peering.Types

%default total

public export
record ImageCoreState where
  constructor MkImageCoreState
  coreLocalImageInfo    : PGImageInfo
  corePeerImages        : List PeerImageInfo
  coreAuthImage         : ObjectImage
  coreAuthSources       : AuthorityImage
  corePeerRecoveryPlans : List PeerRecoveryPlan
  coreLocalRecoveryPlan : List ObjRecovery
  coreActivated         : Bool

public export
record ImageBookkeeping where
  constructor MkImageBookkeeping
  bookPeersQueried     : List OsdId
  bookPeersResponded   : List OsdId
  bookPriorOsds        : List OsdId
  bookTimedOutProbes   : List OsdId
  bookRecoveredPeers   : List OsdId
  bookNeedUpThru       : Bool
  bookPendingActChange : Bool
  bookLastPeeringReset : Epoch

public export
record ImageContext where
  constructor MkImageCtx
  pgid        : PgId
  whoami      : OsdId
  epoch       : Epoch
  acting      : ActingSet
  up          : ActingSet
  pool        : PoolParams
  core        : ImageCoreState
  bookkeeping : ImageBookkeeping

export
emptyImageCtx : ImageContext
emptyImageCtx =
  let coreState =
        MkImageCoreState
          (MkPGImageInfo 0 emptyImage 0 0 0)
          []
          emptyImage
          (fromList [])
          []
          []
          False
      bookState =
        MkImageBookkeeping
          []
          []
          []
          []
          []
          False
          False
          0
  in MkImageCtx 0 0 0 (MkActingSet [] 0) (MkActingSet [] 0)
               (MkPoolParams 0 0) coreState bookState

export
localImageInfo : ImageContext -> PGImageInfo
localImageInfo (MkImageCtx _ _ _ _ _ _ coreState _) = coreLocalImageInfo coreState

export
peerImages : ImageContext -> List PeerImageInfo
peerImages (MkImageCtx _ _ _ _ _ _ coreState _) = corePeerImages coreState

export
authImage : ImageContext -> ObjectImage
authImage (MkImageCtx _ _ _ _ _ _ coreState _) = coreAuthImage coreState

export
authSources : ImageContext -> AuthorityImage
authSources (MkImageCtx _ _ _ _ _ _ coreState _) = coreAuthSources coreState

export
peerRecoveryPlans : ImageContext -> List PeerRecoveryPlan
peerRecoveryPlans (MkImageCtx _ _ _ _ _ _ coreState _) = corePeerRecoveryPlans coreState

export
localRecoveryPlan : ImageContext -> List ObjRecovery
localRecoveryPlan (MkImageCtx _ _ _ _ _ _ coreState _) = coreLocalRecoveryPlan coreState

export
activated : ImageContext -> Bool
activated (MkImageCtx _ _ _ _ _ _ coreState _) = coreActivated coreState

export
peersQueried : ImageContext -> List OsdId
peersQueried (MkImageCtx _ _ _ _ _ _ _ bookState) = bookPeersQueried bookState

export
peersResponded : ImageContext -> List OsdId
peersResponded (MkImageCtx _ _ _ _ _ _ _ bookState) = bookPeersResponded bookState

export
priorOsds : ImageContext -> List OsdId
priorOsds (MkImageCtx _ _ _ _ _ _ _ bookState) = bookPriorOsds bookState

export
timedOutProbes : ImageContext -> List OsdId
timedOutProbes (MkImageCtx _ _ _ _ _ _ _ bookState) = bookTimedOutProbes bookState

export
recoveredPeers : ImageContext -> List OsdId
recoveredPeers (MkImageCtx _ _ _ _ _ _ _ bookState) = bookRecoveredPeers bookState

export
needUpThru : ImageContext -> Bool
needUpThru (MkImageCtx _ _ _ _ _ _ _ bookState) = bookNeedUpThru bookState

export
pendingActChange : ImageContext -> Bool
pendingActChange (MkImageCtx _ _ _ _ _ _ _ bookState) = bookPendingActChange bookState

export
lastPeeringReset : ImageContext -> Epoch
lastPeeringReset (MkImageCtx _ _ _ _ _ _ _ bookState) = bookLastPeeringReset bookState

public export
localImageInfoOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> localImageInfo (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = coreLocalImageInfo coreState
localImageInfoOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

public export
peerImagesOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> peerImages (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = corePeerImages coreState
peerImagesOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

public export
authImageOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> authImage (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = coreAuthImage coreState
authImageOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

public export
peerRecoveryPlansOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> peerRecoveryPlans (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = corePeerRecoveryPlans coreState
peerRecoveryPlansOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

public export
localRecoveryPlanOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> localRecoveryPlan (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = coreLocalRecoveryPlan coreState
localRecoveryPlanOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

public export
activatedOnCtor
  : (pgid : PgId)
 -> (whoami : OsdId)
 -> (epoch : Epoch)
 -> (acting : ActingSet)
 -> (up : ActingSet)
 -> (pool : PoolParams)
 -> (coreState : ImageCoreState)
 -> (bookState : ImageBookkeeping)
 -> activated (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
    = coreActivated coreState
activatedOnCtor pgid whoami epoch acting up pool coreState bookState = Refl

export
localPeerImageInfoFrom : OsdId -> PGImageInfo -> PeerImageInfo
localPeerImageInfoFrom whoami localInfo =
  MkPeerImageInfo whoami localInfo.image localInfo.lastEpochStarted

||| Canonical insertion for OSD sets represented as ascending duplicate-free
||| lists, matching the C++ set-backed bookkeeping.
export
insertOsdSetLike : OsdId -> List OsdId -> List OsdId
insertOsdSetLike osd [] = [osd]
insertOsdSetLike osd (existing :: rest) =
  if osd == existing
     then existing :: rest
     else if osd < existing
             then osd :: existing :: rest
             else existing :: insertOsdSetLike osd rest

||| Normalize an OSD list to the canonical ascending duplicate-free form.
export
normalizeOsdSetLike : List OsdId -> List OsdId
normalizeOsdSetLike =
  foldl (\acc, osd => insertOsdSetLike osd acc) []

||| Local image re-expressed as peer metadata so authority selection can fold
||| local and remote knowledge uniformly.
export
localPeerImageInfo : ImageContext -> PeerImageInfo
localPeerImageInfo ctx =
  localPeerImageInfoFrom ctx.whoami (localImageInfo ctx)

||| Replace or insert peer image info by OSD.
export
upsertPeerImageInfo : PeerImageInfo -> List PeerImageInfo -> List PeerImageInfo
upsertPeerImageInfo info [] = [info]
upsertPeerImageInfo info (existing :: rest) =
  if info.osd == existing.osd
     then info :: rest
     else if info.osd < existing.osd
             then info :: existing :: rest
             else existing :: upsertPeerImageInfo info rest

||| Lookup one replica image. The local replica is synthesized from local state.
export
lookupPeerImageInfo : OsdId -> ImageContext -> Maybe PeerImageInfo
lookupPeerImageInfo osd ctx =
  if osd == ctx.whoami
    then Just (localPeerImageInfo ctx)
    else find (\info => info.osd == osd) (peerImages ctx)

export
knownPeerImagesFrom : OsdId -> PGImageInfo -> List PeerImageInfo -> List PeerImageInfo
knownPeerImagesFrom whoami localInfo knownPeers =
  filter (\existing => existing.osd /= whoami) knownPeers
    ++ [localPeerImageInfoFrom whoami localInfo]

||| All known images, with local state inserted canonically.
export
knownPeerImages : ImageContext -> List PeerImageInfo
knownPeerImages ctx =
  knownPeerImagesFrom ctx.whoami (localImageInfo ctx) (peerImages ctx)

public export
knownPeerImagesUnfold
  : (ctx : ImageContext)
 -> knownPeerImages ctx
    = knownPeerImagesFrom (whoami ctx) (localImageInfo ctx) (peerImages ctx)
knownPeerImagesUnfold
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookkeeping) = Refl

||| Image info for an acting-set peer, defaulting to an empty image when the
||| peer has not responded yet.
export
actingPeerImageOrEmptyFrom : OsdId -> PGImageInfo -> List PeerImageInfo -> OsdId -> PeerImageInfo
actingPeerImageOrEmptyFrom whoami localInfo knownPeers osd =
  if osd == whoami
     then MkPeerImageInfo osd localInfo.image localInfo.lastEpochStarted
     else fromMaybe (MkPeerImageInfo osd emptyImage 0)
                    (find (\info => info.osd == osd) knownPeers)

||| Image info for an acting-set peer, defaulting to an empty image when the
||| peer has not responded yet.
export
%inline
actingPeerImageOrEmpty : ImageContext -> OsdId -> PeerImageInfo
actingPeerImageOrEmpty ctx osd =
  actingPeerImageOrEmptyFrom ctx.whoami (localImageInfo ctx) (peerImages ctx) osd

export
actingReplicaImagesFrom : OsdId -> ActingSet -> PGImageInfo -> List PeerImageInfo -> List PeerImageInfo
actingReplicaImagesFrom whoami acting localInfo knownPeers =
  map (actingPeerImageOrEmptyFrom whoami localInfo knownPeers)
      (filter (\osd => osd /= whoami) acting.osds)

||| Acting replicas excluding the local primary.
export
%inline
actingReplicaImages : ImageContext -> List PeerImageInfo
actingReplicaImages ctx =
  actingReplicaImagesFrom ctx.whoami ctx.acting (localImageInfo ctx) (peerImages ctx)

public export
actingReplicaImagesUnfold
  : (ctx : ImageContext)
 -> actingReplicaImages ctx
    = actingReplicaImagesFrom (whoami ctx) (acting ctx) (localImageInfo ctx) (peerImages ctx)
actingReplicaImagesUnfold
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookkeeping) = Refl

export
actingImagesFrom : OsdId -> ActingSet -> PGImageInfo -> List PeerImageInfo -> List PeerImageInfo
actingImagesFrom whoami acting localInfo knownPeers =
  map (actingPeerImageOrEmptyFrom whoami localInfo knownPeers) acting.osds

||| All acting-set images, including the local replica.
export
%inline
actingImages : ImageContext -> List PeerImageInfo
actingImages ctx =
  actingImagesFrom ctx.whoami ctx.acting (localImageInfo ctx) (peerImages ctx)

||| Check whether this OSD is the primary of the acting set.
export
isImagePrimary : ImageContext -> Bool
isImagePrimary ctx = primary ctx.acting == Just ctx.whoami

||| Unknown-peer guard for the image-native reducer.
export
isKnownPeerImage : OsdId -> ImageContext -> Bool
isKnownPeerImage osd ctx =
  elem osd (peersQueried ctx)
  || contains osd ctx.acting
  || contains osd ctx.up
  || elem osd (priorOsds ctx)

||| Build the probe set: acting + up + prior, excluding self.
export
buildImageProbeSet : ImageContext -> List OsdId
buildImageProbeSet ctx =
  let all' = ctx.acting.osds ++ ctx.up.osds ++ priorOsds ctx
  in nub $ filter (\osd => osd /= ctx.whoami) all'

||| Peers still needing a query under the current bookkeeping.
export
queryNeededPeers : ImageContext -> List OsdId
queryNeededPeers ctx =
  filter (\osd => not (elem osd (peersResponded ctx))
               && not (elem osd (peersQueried ctx)))
         (buildImageProbeSet ctx)

||| Count acting replicas for which we currently have image information.
export
countAvailableImagePeers : ImageContext -> Nat
countAvailableImagePeers ctx =
  length $ filter (\osd => isJust (lookupPeerImageInfo osd ctx)) ctx.acting.osds

||| Check whether all queried peers and all acting replicas have responded.
export
haveEnoughImageInfo : ImageContext -> Bool
haveEnoughImageInfo ctx =
  let allQueried = all (\osd => elem osd (peersResponded ctx)) (peersQueried ctx)
      allActing  = all (\osd => elem osd (peersResponded ctx))
                       (filter (\osd => osd /= ctx.whoami) ctx.acting.osds)
  in allQueried && allActing

||| Recompute the pointwise authoritative image and source map from all known
||| local/remote images.
export
refreshImageAuthority : ImageContext -> ImageContext
refreshImageAuthority
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) =
    let ctx =
          MkImageCtx pgid whoami epoch acting up pool
                     (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                       corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
                     bookState
        newSources = authoritativeSources (knownPeerImages ctx)
        newImage = authorityImageValues newSources
        newCore : ImageCoreState
        newCore =
          MkImageCoreState coreLocalImageInfo corePeerImages newImage newSources
                           corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated
    in MkImageCtx pgid whoami epoch acting up pool newCore bookState

||| Recompute per-peer and local recovery plans from the current authority.
export
refreshImageRecoveryPlans : ImageContext -> ImageContext
refreshImageRecoveryPlans
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) =
    let ctx =
          MkImageCtx pgid whoami epoch acting up pool
                     (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                       corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
                     bookState
        peerPlans = buildPeerRecoveryPlans (authImage ctx) (actingReplicaImages ctx)
        localPlan = pgImageRecoveryPlan (authImage ctx) (localImageInfo ctx)
        newCore : ImageCoreState
        newCore =
          MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                           peerPlans localPlan coreActivated
    in MkImageCtx pgid whoami epoch acting up pool newCore bookState

||| Recompute all derived objectwise fields after peer/local image changes.
export
refreshImageDerived : ImageContext -> ImageContext
refreshImageDerived ctx = refreshImageRecoveryPlans (refreshImageAuthority ctx)

public export
refreshImageDerivedUnfold
  : (ctx : ImageContext)
 -> refreshImageDerived ctx = refreshImageRecoveryPlans (refreshImageAuthority ctx)
refreshImageDerivedUnfold ctx = Refl

||| Exact constructive account of what authority refresh recomputes and what it
||| leaves unchanged.
public export
record ImageAuthorityRefresh (ctx : ImageContext) where
  constructor MkImageAuthorityRefresh
  localInfoPreserved         : localImageInfo (refreshImageAuthority ctx) = localImageInfo ctx
  peerImagesPreserved        : peerImages (refreshImageAuthority ctx) = peerImages ctx
  authSourcesRecomputed      : authSources (refreshImageAuthority ctx) = authoritativeSources (knownPeerImages ctx)
  authImageRecomputed        : authImage (refreshImageAuthority ctx) = authorityImageValues (authoritativeSources (knownPeerImages ctx))
  peerRecoveryPlansPreserved : peerRecoveryPlans (refreshImageAuthority ctx) = peerRecoveryPlans ctx
  localRecoveryPlanPreserved : localRecoveryPlan (refreshImageAuthority ctx) = localRecoveryPlan ctx
  activatedPreserved         : activated (refreshImageAuthority ctx) = activated ctx
  bookkeepingPreserved       : bookkeeping (refreshImageAuthority ctx) = bookkeeping ctx

public export
refreshImageAuthorityLocalInfoPreserved
  : (ctx : ImageContext) -> localImageInfo (refreshImageAuthority ctx) = localImageInfo ctx
refreshImageAuthorityLocalInfoPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityPeerImagesPreserved
  : (ctx : ImageContext) -> peerImages (refreshImageAuthority ctx) = peerImages ctx
refreshImageAuthorityPeerImagesPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityAuthSourcesRecomputed
  : (ctx : ImageContext)
 -> authSources (refreshImageAuthority ctx) = authoritativeSources (knownPeerImages ctx)
refreshImageAuthorityAuthSourcesRecomputed
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityAuthImageRecomputed
  : (ctx : ImageContext)
 -> authImage (refreshImageAuthority ctx) = authorityImageValues (authoritativeSources (knownPeerImages ctx))
refreshImageAuthorityAuthImageRecomputed
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityPeerRecoveryPlansPreserved
  : (ctx : ImageContext)
 -> peerRecoveryPlans (refreshImageAuthority ctx) = peerRecoveryPlans ctx
refreshImageAuthorityPeerRecoveryPlansPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityLocalRecoveryPlanPreserved
  : (ctx : ImageContext)
 -> localRecoveryPlan (refreshImageAuthority ctx) = localRecoveryPlan ctx
refreshImageAuthorityLocalRecoveryPlanPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityActivatedPreserved
  : (ctx : ImageContext) -> activated (refreshImageAuthority ctx) = activated ctx
refreshImageAuthorityActivatedPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityBookkeepingPreserved
  : (ctx : ImageContext) -> bookkeeping (refreshImageAuthority ctx) = bookkeeping ctx
refreshImageAuthorityBookkeepingPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageAuthorityWhoamiPreserved
  : (ctx : ImageContext) -> whoami (refreshImageAuthority ctx) = whoami ctx
refreshImageAuthorityWhoamiPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

export
refreshImageAuthorityWitness : (ctx : ImageContext) -> ImageAuthorityRefresh ctx
refreshImageAuthorityWitness ctx =
  MkImageAuthorityRefresh
    (refreshImageAuthorityLocalInfoPreserved ctx)
    (refreshImageAuthorityPeerImagesPreserved ctx)
    (refreshImageAuthorityAuthSourcesRecomputed ctx)
    (refreshImageAuthorityAuthImageRecomputed ctx)
    (refreshImageAuthorityPeerRecoveryPlansPreserved ctx)
    (refreshImageAuthorityLocalRecoveryPlanPreserved ctx)
    (refreshImageAuthorityActivatedPreserved ctx)
    (refreshImageAuthorityBookkeepingPreserved ctx)

||| Exact constructive account of what recovery-plan refresh recomputes and
||| what it leaves unchanged.
public export
record ImageRecoveryPlanRefresh (ctx : ImageContext) where
  constructor MkImageRecoveryPlanRefresh
  localInfoPreserved         : localImageInfo (refreshImageRecoveryPlans ctx) = localImageInfo ctx
  peerImagesPreserved        : peerImages (refreshImageRecoveryPlans ctx) = peerImages ctx
  authSourcesPreserved       : authSources (refreshImageRecoveryPlans ctx) = authSources ctx
  authImagePreserved         : authImage (refreshImageRecoveryPlans ctx) = authImage ctx
  peerRecoveryPlansRecomputed
    : peerRecoveryPlans (refreshImageRecoveryPlans ctx)
      = buildPeerRecoveryPlans (authImage ctx) (actingReplicaImages ctx)
  localRecoveryPlanRecomputed
    : localRecoveryPlan (refreshImageRecoveryPlans ctx)
      = pgImageRecoveryPlan (authImage ctx) (localImageInfo ctx)
  activatedPreserved         : activated (refreshImageRecoveryPlans ctx) = activated ctx
  bookkeepingPreserved       : bookkeeping (refreshImageRecoveryPlans ctx) = bookkeeping ctx

public export
refreshImageRecoveryPlansLocalInfoPreserved
  : (ctx : ImageContext) -> localImageInfo (refreshImageRecoveryPlans ctx) = localImageInfo ctx
refreshImageRecoveryPlansLocalInfoPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansPeerImagesPreserved
  : (ctx : ImageContext) -> peerImages (refreshImageRecoveryPlans ctx) = peerImages ctx
refreshImageRecoveryPlansPeerImagesPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansAuthSourcesPreserved
  : (ctx : ImageContext) -> authSources (refreshImageRecoveryPlans ctx) = authSources ctx
refreshImageRecoveryPlansAuthSourcesPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansAuthImagePreserved
  : (ctx : ImageContext) -> authImage (refreshImageRecoveryPlans ctx) = authImage ctx
refreshImageRecoveryPlansAuthImagePreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansWhoamiPreserved
  : (ctx : ImageContext) -> whoami (refreshImageRecoveryPlans ctx) = whoami ctx
refreshImageRecoveryPlansWhoamiPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansActingPreserved
  : (ctx : ImageContext) -> acting (refreshImageRecoveryPlans ctx) = acting ctx
refreshImageRecoveryPlansActingPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansPeerRecoveryPlansRecomputed
  : (ctx : ImageContext)
 -> peerRecoveryPlans (refreshImageRecoveryPlans ctx)
    = buildPeerRecoveryPlans (authImage ctx) (actingReplicaImages ctx)
refreshImageRecoveryPlansPeerRecoveryPlansRecomputed
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansLocalRecoveryPlanRecomputed
  : (ctx : ImageContext)
 -> localRecoveryPlan (refreshImageRecoveryPlans ctx)
    = pgImageRecoveryPlan (authImage ctx) (localImageInfo ctx)
refreshImageRecoveryPlansLocalRecoveryPlanRecomputed
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansActivatedPreserved
  : (ctx : ImageContext) -> activated (refreshImageRecoveryPlans ctx) = activated ctx
refreshImageRecoveryPlansActivatedPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

public export
refreshImageRecoveryPlansBookkeepingPreserved
  : (ctx : ImageContext) -> bookkeeping (refreshImageRecoveryPlans ctx) = bookkeeping ctx
refreshImageRecoveryPlansBookkeepingPreserved
  (MkImageCtx pgid whoami epoch acting up pool
              (MkImageCoreState coreLocalImageInfo corePeerImages coreAuthImage coreAuthSources
                                corePeerRecoveryPlans coreLocalRecoveryPlan coreActivated)
              bookState) = Refl

export
refreshImageRecoveryPlansWitness : (ctx : ImageContext) -> ImageRecoveryPlanRefresh ctx
refreshImageRecoveryPlansWitness ctx =
  MkImageRecoveryPlanRefresh
    (refreshImageRecoveryPlansLocalInfoPreserved ctx)
    (refreshImageRecoveryPlansPeerImagesPreserved ctx)
    (refreshImageRecoveryPlansAuthSourcesPreserved ctx)
    (refreshImageRecoveryPlansAuthImagePreserved ctx)
    (refreshImageRecoveryPlansPeerRecoveryPlansRecomputed ctx)
    (refreshImageRecoveryPlansLocalRecoveryPlanRecomputed ctx)
    (refreshImageRecoveryPlansActivatedPreserved ctx)
    (refreshImageRecoveryPlansBookkeepingPreserved ctx)

||| Mark one peer image as received and refresh derived state.
export
recordPeerImage : PeerImageInfo -> ImageContext -> ImageContext
recordPeerImage info ctx =
  let newCore : ImageCoreState
      newCore = { corePeerImages $= upsertPeerImageInfo info } ctx.core
      newBook : ImageBookkeeping
      newBook = { bookPeersResponded $= insertOsdSetLike info.osd } ctx.bookkeeping
  in refreshImageDerived
       ({ core := newCore
        , bookkeeping := newBook
        } ctx)

||| Reset peering-specific image bookkeeping when entering a new interval.
export
resetImagePeeringState : ImageContext -> ImageContext
resetImagePeeringState ctx =
  let newCore : ImageCoreState
      newCore =
        { corePeerImages := []
        , coreAuthImage := emptyImage
        , coreAuthSources := fromList []
        , corePeerRecoveryPlans := []
        , coreLocalRecoveryPlan := []
        , coreActivated := False
        } ctx.core
      newBook : ImageBookkeeping
      newBook =
        { bookPeersQueried := []
        , bookPeersResponded := []
        , bookTimedOutProbes := []
        , bookRecoveredPeers := []
        , bookNeedUpThru := False
        , bookPendingActChange := False
        } ctx.bookkeeping
  in { core := newCore, bookkeeping := newBook } ctx
