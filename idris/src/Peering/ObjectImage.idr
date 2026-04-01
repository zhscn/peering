||| Objectwise append-only summaries for many-object peering.
|||
||| This module defines the finite-map image used by the active Idris model.
module Peering.ObjectImage

import Data.List
import Data.Maybe
import Data.Nat
import Data.SortedMap
import Decidable.Equality
import Peering.Common

%default total

||| An objectwise visible-prefix summary for one PG replica.
public export
ObjectImage : Type
ObjectImage = SortedMap ObjectId Length

||| Missing objects denote visible length 0, so zero entries are omitted.
export
normalizeImageEntry : (ObjectId, Length) -> Maybe (ObjectId, Length)
normalizeImageEntry (obj, Z) = Nothing
normalizeImageEntry (obj, S len) = Just (obj, S len)

||| Build a canonical image from a list of object lengths.
||| Duplicate object IDs keep the greatest visible prefix.
export
imageFromList : List (ObjectId, Length) -> ObjectImage
imageFromList entries =
  fromListWith max (mapMaybe normalizeImageEntry entries)

||| Convert an image back to a canonical key-sorted list.
export
imageToList : ObjectImage -> List (ObjectId, Length)
imageToList = toList

||| Empty image: every object is absent and therefore has length 0.
export
emptyImage : ObjectImage
emptyImage = empty

||| Lookup the visible length of one object. Missing means 0.
export
lookupLength : ObjectId -> ObjectImage -> Length
lookupLength obj image = fromMaybe 0 (lookup obj image)

||| Set the visible length for an object. Length 0 removes the object.
export
setLength : ObjectId -> Length -> ObjectImage -> ObjectImage
setLength obj Z image = delete obj image
setLength obj (S len) image = insert obj (S len) image

||| Monotone append update for one object.
export
appendLength : ObjectId -> Length -> ObjectImage -> ObjectImage
appendLength obj delta image =
  setLength obj (lookupLength obj image + delta) image

||| A singleton image for one object prefix.
export
singletonImage : ObjectId -> Length -> ObjectImage
singletonImage obj len = setLength obj len emptyImage

||| Pointwise authoritative join for two peer images.
export
joinImage : ObjectImage -> ObjectImage -> ObjectImage
joinImage = mergeWith max

||| Clamp a candidate image to an authoritative image, dropping any object
||| content beyond the chosen authority and removing objects absent from it.
export
clampImageTo : ObjectImage -> ObjectImage -> ObjectImage
clampImageTo auth image =
  imageFromList $
    map (\(obj, len) => (obj, min len (lookupLength obj auth))) (imageToList image)

||| Pointwise authoritative join for a whole peer set.
export
joinImages : List ObjectImage -> ObjectImage
joinImages = foldl (\acc, image => joinImage acc image) emptyImage

||| Pointwise prefix check. Missing objects mean visible length 0.
export
prefixImageEntry : ObjectImage -> (ObjectId, Length) -> Bool
prefixImageEntry rhs (obj, lhsLen) = lhsLen <= lookupLength obj rhs

||| Pointwise prefix check over a canonical image-entry list.
export
prefixImageEntries : ObjectImage -> List (ObjectId, Length) -> Bool
prefixImageEntries rhs [] = True
prefixImageEntries rhs (entry :: entries) =
  prefixImageEntry rhs entry && prefixImageEntries rhs entries

||| Pointwise prefix check. Missing objects mean visible length 0.
export
prefixImage : ObjectImage -> ObjectImage -> Bool
prefixImage lhs rhs =
  prefixImageEntries rhs (imageToList lhs)

||| Objectwise equality under the canonical missing-means-zero encoding.
export
sameImage : ObjectImage -> ObjectImage -> Bool
sameImage lhs rhs = prefixImage lhs rhs && prefixImage rhs lhs

||| A typed witness that one image is a pointwise prefix of another.
public export
record ImagePrefixWitness (lhs : ObjectImage) (rhs : ObjectImage) where
  constructor MkImagePrefixWitness
  prefixHolds : prefixImage lhs rhs = True

||| A typed witness that two images describe the same visible prefixes.
public export
record SameImageWitness (lhs : ObjectImage) (rhs : ObjectImage) where
  constructor MkSameImageWitness
  sameHolds : sameImage lhs rhs = True

falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

boolFalseNotTrue : {b : Bool} -> b = False -> b = True -> Void
boolFalseNotTrue Refl Refl impossible

export
natEqSelf : (n : Nat) -> n == n = True
natEqSelf Z = Refl
natEqSelf (S n) = natEqSelf n

export
pairEqSelf
  : {a : Type}
 -> {b : Type}
 -> Eq a => Eq b
 => ((x : a) -> x == x = True)
 -> ((y : b) -> y == y = True)
 -> (pair : (a, b))
 -> pair == pair = True
pairEqSelf eqLeft eqRight (left, right) =
  rewrite eqLeft left in
  rewrite eqRight right in
    Refl

export
listEqSelf
  : {a : Type}
 -> Eq a
 => ((x : a) -> x == x = True)
 -> (xs : List a)
 -> xs == xs = True
listEqSelf eqSelf [] = Refl
listEqSelf eqSelf (x :: xs) =
  rewrite eqSelf x in
  rewrite listEqSelf eqSelf xs in
    Refl

consNotNil : {a : Type} -> {x : a} -> {xs : List a} -> x :: xs = [] -> Void
consNotNil Refl impossible

justNotNothing : {a : Type} -> {x : a} -> Just x = Nothing -> Void
justNotNothing Refl impossible

export
andTrueLeft : {a : Bool} -> {b : Bool} -> a && b = True -> a = True
andTrueLeft {a = False} _ impossible
andTrueLeft {a = True} {b = False} _ impossible
andTrueLeft {a = True} {b = True} Refl = Refl

export
andTrueRight : {a : Bool} -> {b : Bool} -> a && b = True -> b = True
andTrueRight {a = False} _ impossible
andTrueRight {a = True} {b = False} _ impossible
andTrueRight {a = True} {b = True} Refl = Refl

export
andCommutes : (a : Bool) -> (b : Bool) -> a && b = b && a
andCommutes False False = Refl
andCommutes False True = Refl
andCommutes True False = Refl
andCommutes True True = Refl

||| If `x` is not less than `y`, then `y` is at most `x`.
export
ltFalseImpliesLte : (x : Nat) -> (y : Nat) -> x < y = False -> y <= x = True
ltFalseImpliesLte Z Z Refl = Refl
ltFalseImpliesLte Z (S y) prf impossible
ltFalseImpliesLte (S x) Z Refl = Refl
ltFalseImpliesLte (S x) (S y) prf = ltFalseImpliesLte x y prf

||| If `y` is at most `x`, then `x` is not less than `y`.
export
lteTrueImpliesLtFalse : (x : Nat) -> (y : Nat) -> y <= x = True -> x < y = False
lteTrueImpliesLtFalse Z Z Refl = Refl
lteTrueImpliesLtFalse Z (S y) prf impossible
lteTrueImpliesLtFalse (S x) Z Refl = Refl
lteTrueImpliesLtFalse (S x) (S y) prf = lteTrueImpliesLtFalse x y prf

export
decImagePrefixWitness : (lhs : ObjectImage) -> (rhs : ObjectImage) -> Dec (ImagePrefixWitness lhs rhs)
decImagePrefixWitness lhs rhs with (prefixImage lhs rhs) proof prefixEq
  _ | True = Yes (MkImagePrefixWitness prefixEq)
  _ | False = No (\(MkImagePrefixWitness holds) => boolFalseNotTrue prefixEq holds)

export
decSameImageWitness : (lhs : ObjectImage) -> (rhs : ObjectImage) -> Dec (SameImageWitness lhs rhs)
decSameImageWitness lhs rhs with (sameImage lhs rhs) proof sameEq
  _ | True = Yes (MkSameImageWitness sameEq)
  _ | False = No (\(MkSameImageWitness holds) => boolFalseNotTrue sameEq holds)

export
objectImageStructuralEqualSelf : (image : ObjectImage) -> image == image = True
objectImageStructuralEqualSelf image =
  listEqSelf (pairEqSelf natEqSelf natEqSelf) (imageToList image)

export
sameImageLeftPrefix :
  {lhs : ObjectImage} ->
  {rhs : ObjectImage} ->
  SameImageWitness lhs rhs ->
  ImagePrefixWitness lhs rhs
sameImageLeftPrefix {lhs} {rhs} (MkSameImageWitness sameEq) =
  MkImagePrefixWitness (andTrueLeft {a = prefixImage lhs rhs} {b = prefixImage rhs lhs} sameEq)

export
sameImageRightPrefix :
  {lhs : ObjectImage} ->
  {rhs : ObjectImage} ->
  SameImageWitness lhs rhs ->
  ImagePrefixWitness rhs lhs
sameImageRightPrefix {lhs} {rhs} (MkSameImageWitness sameEq) =
  MkImagePrefixWitness (andTrueRight {a = prefixImage lhs rhs} {b = prefixImage rhs lhs} sameEq)

export
prefixWitnessesGiveSameImage :
  {lhs : ObjectImage} ->
  {rhs : ObjectImage} ->
  ImagePrefixWitness lhs rhs ->
  ImagePrefixWitness rhs lhs ->
  SameImageWitness lhs rhs
prefixWitnessesGiveSameImage (MkImagePrefixWitness leftEq) (MkImagePrefixWitness rightEq) =
  MkSameImageWitness (rewrite leftEq in rewrite rightEq in Refl)

export
sameImageSymmetric :
  {lhs : ObjectImage} ->
  {rhs : ObjectImage} ->
  SameImageWitness lhs rhs ->
  SameImageWitness rhs lhs
sameImageSymmetric {lhs} {rhs} sameEq =
  prefixWitnessesGiveSameImage {lhs = rhs} {rhs = lhs}
    (sameImageRightPrefix sameEq)
    (sameImageLeftPrefix sameEq)

||| Centralize the executable "join extends the left image" check.
export
joinImageExtendsLeft : ObjectImage -> ObjectImage -> Bool
joinImageExtendsLeft lhs rhs = prefixImage lhs (joinImage lhs rhs)

||| Centralize the executable "join extends the right image" check.
export
joinImageExtendsRight : ObjectImage -> ObjectImage -> Bool
joinImageExtendsRight lhs rhs = prefixImage rhs (joinImage lhs rhs)

||| Centralize the executable "clamp stays within authority" check.
export
clampImageWithinAuthority : ObjectImage -> ObjectImage -> Bool
clampImageWithinAuthority auth image = prefixImage (clampImageTo auth image) auth

||| One recovery item if the local image is behind the authoritative image.
export
recoveryGapFor : ObjectImage -> (ObjectId, Length) -> Maybe (ObjectId, Length, Length)
recoveryGapFor local (obj, authLen) =
  if lookupLength obj local < authLen
        then Just (obj, lookupLength obj local, authLen)
        else Nothing

||| Recovery gaps over a canonical authoritative entry list.
export
imageRecoveryGapEntries : ObjectImage -> List (ObjectId, Length) -> List (ObjectId, Length, Length)
imageRecoveryGapEntries local [] = []
imageRecoveryGapEntries local (entry :: entries) =
  case recoveryGapFor local entry of
    Nothing => imageRecoveryGapEntries local entries
    Just gap => gap :: imageRecoveryGapEntries local entries

||| Objects that are behind the authoritative image, with local and target lengths.
export
imageRecoveryGaps : ObjectImage -> ObjectImage -> List (ObjectId, Length, Length)
imageRecoveryGaps local auth =
  imageRecoveryGapEntries local (imageToList auth)

||| A typed witness that all authoritative recovery gaps have been closed.
public export
record NoImageRecoveryGaps (local : ObjectImage) (auth : ObjectImage) where
  constructor MkNoImageRecoveryGaps
  noRecoveryGaps : imageRecoveryGaps local auth = []

||| Centralize the executable "there are no authoritative recovery gaps" check.
export
recoveryGapFree : ObjectImage -> ObjectImage -> Bool
recoveryGapFree local auth = null (imageRecoveryGaps local auth)

export
decNoImageRecoveryGaps : (local : ObjectImage) -> (auth : ObjectImage) -> Dec (NoImageRecoveryGaps local auth)
decNoImageRecoveryGaps local auth with (imageRecoveryGaps local auth) proof noGaps
  _ | [] = Yes (MkNoImageRecoveryGaps noGaps)
  _ | gap :: gaps = No (\(MkNoImageRecoveryGaps emptyEq) => consNotNil (trans (sym noGaps) emptyEq))

export
decJoinImageExtendsLeft : (lhs : ObjectImage) -> (rhs : ObjectImage) -> Dec (ImagePrefixWitness lhs (joinImage lhs rhs))
decJoinImageExtendsLeft lhs rhs = decImagePrefixWitness lhs (joinImage lhs rhs)

export
decJoinImageExtendsRight : (lhs : ObjectImage) -> (rhs : ObjectImage) -> Dec (ImagePrefixWitness rhs (joinImage lhs rhs))
decJoinImageExtendsRight lhs rhs = decImagePrefixWitness rhs (joinImage lhs rhs)

export
decClampImageWithinAuthority : (auth : ObjectImage) -> (image : ObjectImage) -> Dec (ImagePrefixWitness (clampImageTo auth image) auth)
decClampImageWithinAuthority auth image = decImagePrefixWitness (clampImageTo auth image) auth

export
prefixEntryImpliesNoRecoveryGap :
  (local : ObjectImage) ->
  (entry : (ObjectId, Length)) ->
  prefixImageEntry local entry = True ->
  recoveryGapFor local entry = Nothing
prefixEntryImpliesNoRecoveryGap local (obj, authLen) prefixEq =
  let noGap = lteTrueImpliesLtFalse (lookupLength obj local) authLen prefixEq
  in rewrite noGap in Refl

export
noRecoveryGapImpliesPrefixEntry :
  (local : ObjectImage) ->
  (entry : (ObjectId, Length)) ->
  recoveryGapFor local entry = Nothing ->
  prefixImageEntry local entry = True
noRecoveryGapImpliesPrefixEntry local (obj, authLen) gapEq
    with (lookupLength obj local < authLen) proof gapLt
  _ | True = absurd (justNotNothing gapEq)
  _ | False = ltFalseImpliesLte (lookupLength obj local) authLen gapLt

prefixEntriesImpliesNoRecoveryGaps :
  (local : ObjectImage) ->
  (entries : List (ObjectId, Length)) ->
  prefixImageEntries local entries = True ->
  imageRecoveryGapEntries local entries = []
prefixEntriesImpliesNoRecoveryGaps local [] Refl = Refl
prefixEntriesImpliesNoRecoveryGaps local ((obj, authLen) :: rest) prefixEq =
  let headGapFree = prefixEntryImpliesNoRecoveryGap local (obj, authLen) (andTrueLeft prefixEq)
      tailNoGaps = prefixEntriesImpliesNoRecoveryGaps local rest (andTrueRight prefixEq)
  in rewrite headGapFree in tailNoGaps

noRecoveryGapsEntriesImpliesPrefix :
  (local : ObjectImage) ->
  (entries : List (ObjectId, Length)) ->
  imageRecoveryGapEntries local entries = [] ->
  prefixImageEntries local entries = True
noRecoveryGapsEntriesImpliesPrefix local [] Refl = Refl
noRecoveryGapsEntriesImpliesPrefix local ((obj, authLen) :: rest) noGaps
    with (recoveryGapFor local (obj, authLen)) proof headGap
  _ | Just gap = absurd (consNotNil noGaps)
  _ | Nothing =
    let headPrefix = noRecoveryGapImpliesPrefixEntry local (obj, authLen) headGap
        tailNoGaps = noGaps
        tailPrefix = noRecoveryGapsEntriesImpliesPrefix local rest tailNoGaps
    in rewrite headPrefix in rewrite tailPrefix in Refl

export
prefixImageImpliesNoRecoveryGaps :
  {local : ObjectImage} ->
  {auth : ObjectImage} ->
  ImagePrefixWitness auth local ->
  NoImageRecoveryGaps local auth
prefixImageImpliesNoRecoveryGaps {local} {auth} (MkImagePrefixWitness prefixEq) =
  MkNoImageRecoveryGaps (prefixEntriesImpliesNoRecoveryGaps local (imageToList auth) prefixEq)

export
noRecoveryGapsImpliesPrefixImage :
  {local : ObjectImage} ->
  {auth : ObjectImage} ->
  NoImageRecoveryGaps local auth ->
  ImagePrefixWitness auth local
noRecoveryGapsImpliesPrefixImage {local} {auth} (MkNoImageRecoveryGaps noGaps) =
  MkImagePrefixWitness (noRecoveryGapsEntriesImpliesPrefix local (imageToList auth) noGaps)

export
sameImageImpliesNoRecoveryGaps :
  {local : ObjectImage} ->
  {auth : ObjectImage} ->
  SameImageWitness local auth ->
  NoImageRecoveryGaps local auth
sameImageImpliesNoRecoveryGaps sameEq =
  prefixImageImpliesNoRecoveryGaps (sameImageRightPrefix sameEq)

export
noRecoveryGapsAndPrefixGiveSameImage :
  {local : ObjectImage} ->
  {auth : ObjectImage} ->
  NoImageRecoveryGaps local auth ->
  ImagePrefixWitness local auth ->
  SameImageWitness local auth
noRecoveryGapsAndPrefixGiveSameImage noGaps localPrefix =
  prefixWitnessesGiveSameImage localPrefix (noRecoveryGapsImpliesPrefixImage noGaps)

||| One recovery item for one object on one target peer.
public export
record ObjRecovery where
  constructor MkObjRecovery
  obj     : ObjectId
  fromLen : Length
  toLen   : Length

export
objRecoveryStructuralEqual : ObjRecovery -> ObjRecovery -> Bool
objRecoveryStructuralEqual a b =
  a.obj == b.obj
  && a.fromLen == b.fromLen
  && a.toLen == b.toLen

public export
Eq ObjRecovery where
  (==) = objRecoveryStructuralEqual

public export
DecEq ObjRecovery where
  decEq (MkObjRecovery objA fromA toA) (MkObjRecovery objB fromB toB) =
    let Yes Refl = decEq objA objB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq fromA fromB
          | No contra => No (\Refl => contra Refl)
        Yes Refl = decEq toA toB
          | No contra => No (\Refl => contra Refl)
    in Yes Refl

public export
Show ObjRecovery where
  show item =
    "ObjRecovery(obj=" ++ show item.obj
      ++ ", from=" ++ show item.fromLen
      ++ ", to=" ++ show item.toLen ++ ")"
