||| Core types for the append-only peering protocol.
module Peering.Types

import Data.Nat
import Data.Maybe
import Data.SortedMap
import Decidable.Equality
import public Peering.Common
import public Peering.ObjectImage

%default total

-- ── Image-native peer and PG summaries ────────────────────────────

||| Image-aware peer metadata for the active objectwise model.
public export
record PeerImageInfo where
  constructor MkPeerImageInfo
  osd              : OsdId
  image            : ObjectImage
  lastEpochStarted : Epoch

||| Structural equality for peer summaries. Semantic comparison helpers live
||| in the refinement layer under explicit `...Equivalent` names.
export
peerImageInfoStructuralEqual : PeerImageInfo -> PeerImageInfo -> Bool
peerImageInfoStructuralEqual a b =
  a.osd == b.osd
  && a.image == b.image
  && a.lastEpochStarted == b.lastEpochStarted

public export
Eq PeerImageInfo where
  (==) = peerImageInfoStructuralEqual

public export
Show PeerImageInfo where
  show p = "PeerImageInfo(osd=" ++ show p.osd
        ++ ", image=" ++ show p.image
        ++ ", les=" ++ show p.lastEpochStarted ++ ")"

||| Image-aware local PG summary for the active objectwise model.
public export
record PGImageInfo where
  constructor MkPGImageInfo
  pgid                : PgId
  image               : ObjectImage
  lastEpochStarted    : Epoch
  lastIntervalStarted : Epoch
  lastEpochClean      : Epoch

||| Structural equality for local PG summaries. Monotone/semantic comparison
||| helpers are named explicitly in the refinement layer.
export
pgImageInfoStructuralEqual : PGImageInfo -> PGImageInfo -> Bool
pgImageInfoStructuralEqual a b =
  a.pgid == b.pgid
  && a.image == b.image
  && a.lastEpochStarted == b.lastEpochStarted
  && a.lastIntervalStarted == b.lastIntervalStarted
  && a.lastEpochClean == b.lastEpochClean

public export
Eq PGImageInfo where
  (==) = pgImageInfoStructuralEqual

public export
Show PGImageInfo where
  show p = "PGImageInfo(pg=" ++ show p.pgid
        ++ ", image=" ++ show p.image
        ++ ", les=" ++ show p.lastEpochStarted ++ ")"

||| The authoritative source for one object's visible prefix.
public export
record ObjectAuthority where
  constructor MkObjectAuthority
  authorityOsd    : OsdId
  authorityLength : Length

export
objectAuthorityStructuralEqual : ObjectAuthority -> ObjectAuthority -> Bool
objectAuthorityStructuralEqual a b =
  a.authorityOsd == b.authorityOsd
  && a.authorityLength == b.authorityLength

public export
Eq ObjectAuthority where
  (==) = objectAuthorityStructuralEqual

public export
DecEq ObjectAuthority where
  decEq (MkObjectAuthority osdA lenA)
        (MkObjectAuthority osdB lenB) =
    let Yes Refl = decEq osdA osdB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq lenA lenB
          | No contra => No (\Refl => contra Refl)
    in Yes Refl

public export
Show ObjectAuthority where
  show item =
    "ObjectAuthority(osd=" ++ show item.authorityOsd
      ++ ", len=" ++ show item.authorityLength ++ ")"

public export
AuthorityImage : Type
AuthorityImage = SortedMap ObjectId ObjectAuthority

||| Recovery work targeted at one replica in the objectwise model.
public export
record PeerRecoveryPlan where
  constructor MkPeerRecoveryPlan
  target     : OsdId
  recoveries : List ObjRecovery

export
peerRecoveryPlanStructuralEqual : PeerRecoveryPlan -> PeerRecoveryPlan -> Bool
peerRecoveryPlanStructuralEqual a b =
  a.target == b.target
  && a.recoveries == b.recoveries

public export
Eq PeerRecoveryPlan where
  (==) = peerRecoveryPlanStructuralEqual

public export
DecEq PeerRecoveryPlan where
  decEq (MkPeerRecoveryPlan targetA recoveriesA)
        (MkPeerRecoveryPlan targetB recoveriesB) =
    let Yes Refl = decEq targetA targetB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq recoveriesA recoveriesB
          | No contra => No (\Refl => contra Refl)
    in Yes Refl

public export
Show PeerRecoveryPlan where
  show plan =
    "PeerRecoveryPlan(target=" ++ show plan.target
      ++ ", recoveries=" ++ show plan.recoveries ++ ")"

||| Choose the stronger authority for one object. Longer visible prefix wins;
||| ties keep the existing source so folding remains stable.
export
joinAuthority : ObjectAuthority -> ObjectAuthority -> ObjectAuthority
joinAuthority left right =
  if left.authorityLength < right.authorityLength then right else left

||| Collapse peer images to a pointwise authoritative image.
export
authoritativeImage : List PeerImageInfo -> ObjectImage
authoritativeImage infos = joinImages (map (\info => info.image) infos)

||| Track both authority source and authority length objectwise.
export
authoritativeSources : List PeerImageInfo -> AuthorityImage
authoritativeSources = foldl addPeer empty
  where
    addObject : OsdId -> AuthorityImage -> (ObjectId, Length) -> AuthorityImage
    addObject source acc (obj, len) =
      insertWith joinAuthority obj (MkObjectAuthority source len) acc

    addPeer : AuthorityImage -> PeerImageInfo -> AuthorityImage
    addPeer acc info =
      foldl (\acc', entry => addObject info.osd acc' entry) acc (imageToList info.image)

||| Use a single peer image as the chosen objectwise authority.
export
authorityFromPeerImage : PeerImageInfo -> AuthorityImage
authorityFromPeerImage info =
  fromList (map (\(obj, len) => (obj, MkObjectAuthority info.osd len)) (imageToList info.image))

||| Extract just the authoritative image from an authority map.
export
authorityImageValues : AuthorityImage -> ObjectImage
authorityImageValues auth = map authorityLength auth

||| Canonical equality for authority maps via their sorted key/value lists.
export
sameAuthorityImage : AuthorityImage -> AuthorityImage -> Bool
sameAuthorityImage left right =
  Data.SortedMap.toList left == Data.SortedMap.toList right

export
objectAuthorityStructuralEqualSelf : (auth : ObjectAuthority) -> auth == auth = True
objectAuthorityStructuralEqualSelf (MkObjectAuthority osd len) =
  rewrite natEqSelf osd in
  rewrite natEqSelf len in
    Refl

export
sameAuthorityImageSelf : (auth : AuthorityImage) -> sameAuthorityImage auth auth = True
sameAuthorityImageSelf auth =
  listEqSelf
    (pairEqSelf natEqSelf objectAuthorityStructuralEqualSelf)
    (Data.SortedMap.toList auth)

||| Derive the objectwise recovery work needed for one peer image.
export
peerImageRecoveryPlanFromImage : ObjectImage -> ObjectImage -> List ObjRecovery
peerImageRecoveryPlanFromImage auth image =
  map (\(obj, fromLen, toLen) => MkObjRecovery obj fromLen toLen)
      (imageRecoveryGaps image auth)

||| Derive the objectwise recovery work needed for one peer image.
export
peerImageRecoveryPlan : ObjectImage -> PeerImageInfo -> List ObjRecovery
peerImageRecoveryPlan auth peer =
  peerImageRecoveryPlanFromImage auth peer.image

||| Peer recovery work depends only on the peer's visible image, not on
||| unrelated metadata such as `lastEpochStarted`.
export
peerImageRecoveryPlanDependsOnlyOnImage
  : (auth : ObjectImage)
 -> {peerA : PeerImageInfo}
 -> {peerB : PeerImageInfo}
 -> peerA.image = peerB.image
 -> peerImageRecoveryPlan auth peerA = peerImageRecoveryPlan auth peerB
peerImageRecoveryPlanDependsOnlyOnImage auth {peerA} {peerB} imageEq =
  rewrite imageEq in Refl

||| Derive the objectwise recovery work needed for the local PG image.
export
pgImageRecoveryPlanFromImage : ObjectImage -> ObjectImage -> List ObjRecovery
pgImageRecoveryPlanFromImage = peerImageRecoveryPlanFromImage

||| Derive the objectwise recovery work needed for the local PG image.
export
pgImageRecoveryPlan : ObjectImage -> PGImageInfo -> List ObjRecovery
pgImageRecoveryPlan auth pg =
  pgImageRecoveryPlanFromImage auth pg.image

||| Local recovery work depends only on the local visible image, not on the
||| epoch-tracking metadata carried alongside it.
export
pgImageRecoveryPlanDependsOnlyOnImage
  : (auth : ObjectImage)
 -> {pgA : PGImageInfo}
 -> {pgB : PGImageInfo}
 -> pgA.image = pgB.image
 -> pgImageRecoveryPlan auth pgA = pgImageRecoveryPlan auth pgB
pgImageRecoveryPlanDependsOnlyOnImage auth {pgA} {pgB} imageEq =
  rewrite imageEq in Refl

||| Check the objectwise safety condition for one peer image.
export
peerImageIsPrefixOf : ObjectImage -> PeerImageInfo -> Bool
peerImageIsPrefixOf auth peer = prefixImage peer.image auth

||| Check whether one peer is fully caught up objectwise.
export
peerImageIsRecovered : ObjectImage -> PeerImageInfo -> Bool
peerImageIsRecovered auth peer = sameImage peer.image auth

||| Check the objectwise safety condition for the local PG image.
export
pgImageIsPrefixOf : ObjectImage -> PGImageInfo -> Bool
pgImageIsPrefixOf auth pg = prefixImage pg.image auth

||| Check whether the local PG image is fully caught up objectwise.
export
pgImageIsRecovered : ObjectImage -> PGImageInfo -> Bool
pgImageIsRecovered auth pg = sameImage pg.image auth

||| Derive recovery work for a peer only when it is actually behind.
export
mkPeerRecoveryPlanFromInputs : ObjectImage -> OsdId -> ObjectImage -> Maybe PeerRecoveryPlan
mkPeerRecoveryPlanFromInputs auth target image =
  let gaps = peerImageRecoveryPlanFromImage auth image
  in if null gaps
       then Nothing
       else Just (MkPeerRecoveryPlan target gaps)

||| Derive recovery work for a peer only when it is actually behind.
export
mkPeerRecoveryPlan : ObjectImage -> PeerImageInfo -> Maybe PeerRecoveryPlan
mkPeerRecoveryPlan auth peer =
  mkPeerRecoveryPlanFromInputs auth peer.osd peer.image

||| One peer plan depends only on the target OSD and visible image.
export
mkPeerRecoveryPlanDependsOnlyOnPlanInputs
  : (auth : ObjectImage)
 -> {peerA : PeerImageInfo}
 -> {peerB : PeerImageInfo}
 -> peerA.osd = peerB.osd
 -> peerA.image = peerB.image
 -> mkPeerRecoveryPlan auth peerA = mkPeerRecoveryPlan auth peerB
mkPeerRecoveryPlanDependsOnlyOnPlanInputs auth {peerA} {peerB} osdEq imageEq =
  rewrite osdEq in
  rewrite imageEq in
    Refl

||| Derive objectwise recovery plans for every peer that is behind the
||| authoritative image.
export
buildPeerRecoveryPlans : ObjectImage -> List PeerImageInfo -> List PeerRecoveryPlan
buildPeerRecoveryPlans auth peers = mapMaybe (mkPeerRecoveryPlan auth) peers

||| Small-step expansion of peer-plan recomputation.
export
buildPeerRecoveryPlansNil : (auth : ObjectImage) -> buildPeerRecoveryPlans auth [] = []
buildPeerRecoveryPlansNil auth = Refl

||| Constructor-level view of one peer-plan recomputation step.
export
buildPeerRecoveryPlansCons
  : (auth : ObjectImage)
 -> (peer : PeerImageInfo)
 -> (peers : List PeerImageInfo)
 -> buildPeerRecoveryPlans auth (peer :: peers)
    = case mkPeerRecoveryPlan auth peer of
        Nothing => mapMaybe (mkPeerRecoveryPlan auth) peers
        Just plan => plan :: mapMaybe (mkPeerRecoveryPlan auth) peers
buildPeerRecoveryPlansCons auth peer peers with (mkPeerRecoveryPlan auth peer)
  buildPeerRecoveryPlansCons auth peer peers | Nothing = Refl
  buildPeerRecoveryPlansCons auth peer peers | Just plan = Refl

||| Executable objectwise invariant check for a whole peer set.
export
allPeerImagesPrefixOf : ObjectImage -> List PeerImageInfo -> Bool
allPeerImagesPrefixOf auth peers = all (peerImageIsPrefixOf auth) peers

||| Executable objectwise clean check for a whole peer set.
export
allPeerImagesRecovered : ObjectImage -> List PeerImageInfo -> Bool
allPeerImagesRecovered auth peers = all (peerImageIsRecovered auth) peers

-- ── ActingSet ─────────────────────────────────────────────────────

||| An acting set with roles. Head is primary.
public export
record ActingSet where
  constructor MkActingSet
  osds  : List OsdId
  epoch : Epoch

export
actingSetStructuralEqual : ActingSet -> ActingSet -> Bool
actingSetStructuralEqual a b = a.osds == b.osds && a.epoch == b.epoch

public export
Eq ActingSet where
  (==) = actingSetStructuralEqual

public export
DecEq ActingSet where
  decEq (MkActingSet osdsA epochA) (MkActingSet osdsB epochB) =
    let Yes Refl = decEq osdsA osdsB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq epochA epochB
          | No contra => No (\Refl => contra Refl)
    in Yes Refl

public export
primary : ActingSet -> Maybe OsdId
primary as = case as.osds of
  (p :: _) => Just p
  []       => Nothing

public export
contains : OsdId -> ActingSet -> Bool
contains osd as = elem osd as.osds

public export
actingSize : ActingSet -> Nat
actingSize as = length as.osds

-- ── Pool parameters ───────────────────────────────────────────────

public export
record PoolParams where
  constructor MkPoolParams
  size    : Nat  -- desired replication factor
  minSize : Nat  -- minimum to serve IO

export
poolParamsStructuralEqual : PoolParams -> PoolParams -> Bool
poolParamsStructuralEqual a b = a.size == b.size && a.minSize == b.minSize

public export
Eq PoolParams where
  (==) = poolParamsStructuralEqual

public export
DecEq PoolParams where
  decEq (MkPoolParams sizeA minA) (MkPoolParams sizeB minB) =
    let Yes Refl = decEq sizeA sizeB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq minA minB
          | No contra => No (\Refl => contra Refl)
    in Yes Refl
