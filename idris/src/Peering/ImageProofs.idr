||| Typed proof shell for the native image-aware reducer.
|||
||| This keeps the preservation premise in an explicit normal form so Idris
||| can reduce it without getting stuck on cross-module unfolding.
module Peering.ImageProofs

import Data.List
import Data.SortedMap
import Peering.ImageInvariants
import Peering.ImageProcess
import Peering.ImageMachine
import Peering.ImageRefinement
import Peering.Types

%default total

public export
record ImageInvariant (ctx : ImageContext) where
  constructor MkImageInvariant
  holds : imageContextInvariant ctx = True

public export
record ImageSemanticBoundary (ctx : ImageContext) where
  constructor MkImageSemanticBoundary
  holds : imageSemanticBoundarySafe ctx = True

public export
record ImageObservableBoundary (ctx : ImageContext) where
  constructor MkImageObservableBoundary
  holds : contextObservableStateSafe ctx = True

||| Fine-grained witness for just the peer-plan-derived component of the image
||| invariant.
public export
record ImagePeerRecoveryPlansDerived (ctx : ImageContext) where
  constructor MkImagePeerRecoveryPlansDerived
  holds : peerRecoveryPlans ctx = buildPeerRecoveryPlans (authImage ctx) (actingReplicaImages ctx)

||| Fine-grained witness for just the local-plan-derived component of the image
||| invariant.
public export
record ImageLocalRecoveryPlanDerived (ctx : ImageContext) where
  constructor MkImageLocalRecoveryPlanDerived
  holds : localRecoveryPlan ctx = pgImageRecoveryPlan (authImage ctx) (localImageInfo ctx)

||| Bundle the two recovery-plan-derived invariant fragments together.
public export
record ImageRecoveryPlansDerived (ctx : ImageContext) where
  constructor MkImageRecoveryPlansDerived
  peerPlans  : ImagePeerRecoveryPlansDerived ctx
  localPlans : ImageLocalRecoveryPlanDerived ctx

||| Fine-grained constructive witness for authority-source recomputation.
public export
record ImageAuthoritySourcesDerived (ctx : ImageContext) where
  constructor MkImageAuthoritySourcesDerived
  holds : authSources ctx = authoritativeSources (knownPeerImages ctx)

||| Fine-grained constructive witness for authoritative-image recomputation
||| from known peers.
public export
record ImageAuthorityImageDerived (ctx : ImageContext) where
  constructor MkImageAuthorityImageDerived
  holds : authImage ctx = authorityImageValues (authoritativeSources (knownPeerImages ctx))

||| Proof-facing canonical authority alignment. The executable semantic check
||| uses `sameImage`; the proof layer carries the stronger equality that makes
||| that check straightforward to discharge later.
public export
record ImageAuthoritySemanticAlignment (ctx : ImageContext) where
  constructor MkImageAuthoritySemanticAlignment
  holds : authImage ctx = authorityImageValues (authSources ctx)

||| Bundle the constructive authority recomputation facts together.
public export
record ImageAuthorityDerived (ctx : ImageContext) where
  constructor MkImageAuthorityDerived
  sources   : ImageAuthoritySourcesDerived ctx
  image     : ImageAuthorityImageDerived ctx
  alignment : ImageAuthoritySemanticAlignment ctx

||| Exact authority-map equality discharges the executable source-map check.
public export
sameAuthorityImageOnEqual
  : {lhs : AuthorityImage}
 -> {rhs : AuthorityImage}
 -> lhs = rhs
 -> sameAuthorityImage lhs rhs = True
sameAuthorityImageOnEqual {rhs} Refl = sameAuthorityImageSelf rhs

||| Canonical image equality is enough to discharge the executable
||| authority-image semantic check; the `sameImage` branch becomes redundant
||| once the exact equality short-circuit fires.
public export
authorityImageSemanticallyMatchesOnEqual
  : {image : ObjectImage}
 -> {auth : AuthorityImage}
 -> image = authorityImageValues auth
 -> authorityImageSemanticallyMatches image auth = True
authorityImageSemanticallyMatchesOnEqual {image} {auth} imageEq =
  rewrite authorityImageSemanticallyMatchesUnfold image auth in
  replace
    {p = \lhs =>
       (lhs == authorityImageValues auth
        || sameImage lhs (authorityImageValues auth)) = True}
    (sym imageEq)
    (rewrite objectImageStructuralEqualSelf (authorityImageValues auth) in Refl)

||| The stored authority-source image semantically matches recomputation from
||| known peers whenever authority sources are constructively recomputed.
public export
authorityStoredSourcesMatchKnownPeersFromDerived
  : {ctx : ImageContext}
 -> ImageAuthoritySourcesDerived ctx
 -> authorityImageSemanticallyMatches
      (authorityImageValues (authSources ctx))
      (authoritativeSources (knownPeerImages ctx))
    = True
authorityStoredSourcesMatchKnownPeersFromDerived
  {ctx = MkImageCtx pgid whoami epoch acting up pool coreState bookState}
  (MkImageAuthoritySourcesDerived sourcesEq) =
    authorityImageSemanticallyMatchesOnEqual (cong authorityImageValues sourcesEq)

||| The current authoritative image semantically matches recomputation from
||| known peers whenever the image itself is constructively recomputed.
public export
authorityCurrentImageMatchesKnownPeersFromDerived
  : {ctx : ImageContext}
 -> ImageAuthorityImageDerived ctx
 -> authorityImageSemanticallyMatches
      (authImage ctx)
      (authoritativeSources (knownPeerImages ctx))
    = True
authorityCurrentImageMatchesKnownPeersFromDerived
  {ctx = MkImageCtx pgid whoami epoch acting up pool coreState bookState}
  (MkImageAuthorityImageDerived imageEq) =
    authorityImageSemanticallyMatchesOnEqual imageEq

||| Exact authority-source recomputation discharges the executable structural
||| source-map agreement check.
public export
authorityEntriesBackedByKnownPeersFromDerived
  : {ctx : ImageContext}
 -> ImageAuthoritySourcesDerived ctx
 -> sameAuthorityImage
      (authSources ctx)
      (authoritativeSources (knownPeerImages ctx))
    = True
authorityEntriesBackedByKnownPeersFromDerived
  {ctx = MkImageCtx pgid whoami epoch acting up pool coreState bookState}
  (MkImageAuthoritySourcesDerived sourcesEq) =
    sameAuthorityImageOnEqual sourcesEq

||| The constructive authority bundle is enough to prove that authority is
||| derived from known peers in the executable checker.
public export
authorityDerivedFromKnownPeersFromDerived
  : {ctx : ImageContext}
 -> ImageAuthorityDerived ctx
 -> authorityDerivedFromKnownPeers ctx = True
authorityDerivedFromKnownPeersFromDerived
  {ctx = MkImageCtx pgid whoami epoch acting up pool coreState bookState}
  derived =
  let storedOk = authorityStoredSourcesMatchKnownPeersFromDerived derived.sources
      currentOk = authorityCurrentImageMatchesKnownPeersFromDerived derived.image
      entriesOk = authorityEntriesBackedByKnownPeersFromDerived derived.sources
  in rewrite authorityDerivedFromKnownPeersUnfold
               (MkImageCtx pgid whoami epoch acting up pool coreState bookState) in
     rewrite authorityStoredSourcesMatchKnownPeersUnfold
               (MkImageCtx pgid whoami epoch acting up pool coreState bookState) in
     rewrite authorityCurrentImageMatchesKnownPeersUnfold
               (MkImageCtx pgid whoami epoch acting up pool coreState bookState) in
     rewrite authorityEntriesBackedByKnownPeersUnfold
               (MkImageCtx pgid whoami epoch acting up pool coreState bookState) in
     rewrite storedOk in
     rewrite currentOk in
     rewrite entriesOk in
       Refl

||| The constructive authority bundle also discharges the top-level executable
||| authority check.
public export
authorityDerivedCorrectlyFromDerived
  : {ctx : ImageContext}
 -> ImageAuthorityDerived ctx
 -> authorityDerivedCorrectly ctx = True
authorityDerivedCorrectlyFromDerived
  {ctx = MkImageCtx pgid whoami epoch acting up pool coreState bookState}
  derived =
  rewrite authorityDerivedCorrectlyUnfold
            (MkImageCtx pgid whoami epoch acting up pool coreState bookState) in
  rewrite authorityDerivedFromKnownPeersFromDerived derived in Refl

||| `actingReplicaImagesFrom` depends only on its explicit input tuple, so it
||| provides the constructive congruence principle needed by the refresh
||| proofs without reopening whole contexts.
public export
actingReplicaImagesFromCongruent
  : {whoamiA : OsdId}
 -> {whoamiB : OsdId}
 -> {actingA : ActingSet}
 -> {actingB : ActingSet}
 -> {localA : PGImageInfo}
 -> {localB : PGImageInfo}
 -> {peersA : List PeerImageInfo}
 -> {peersB : List PeerImageInfo}
 -> whoamiA = whoamiB
 -> actingA = actingB
 -> localA = localB
 -> peersA = peersB
 -> actingReplicaImagesFrom whoamiA actingA localA peersA
    = actingReplicaImagesFrom whoamiB actingB localB peersB
actingReplicaImagesFromCongruent Refl Refl Refl Refl = Refl

||| `knownPeerImagesFrom` depends only on its explicit input tuple.
public export
knownPeerImagesFromCongruent
  : {whoamiA : OsdId}
 -> {whoamiB : OsdId}
 -> {localA : PGImageInfo}
 -> {localB : PGImageInfo}
 -> {peersA : List PeerImageInfo}
 -> {peersB : List PeerImageInfo}
 -> whoamiA = whoamiB
 -> localA = localB
 -> peersA = peersB
 -> knownPeerImagesFrom whoamiA localA peersA
    = knownPeerImagesFrom whoamiB localB peersB
knownPeerImagesFromCongruent Refl Refl Refl = Refl

public export
record ObservedImageBoundary (snap : ImageObservedSnapshot) where
  constructor MkObservedImageBoundary
  holds : observableImageStateSafe (snapshotObservableState snap) = True

public export
record ObservedObservableSnapshotBoundary (snap : ObservableImageSnapshot) where
  constructor MkObservedObservableSnapshotBoundary
  holds : observableImageStateSafe (observableSnapshotState snap) = True

||| Semantic proof-facing boundary alias. The proof layer works on this
||| reduced snapshot surface; the replay snapshot remains an external wrapper.
public export
ObservedSemanticSnapshotBoundary : ImageSemanticSnapshot -> Type
ObservedSemanticSnapshotBoundary = ObservedObservableSnapshotBoundary

falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

boolFalseNotTrue : {b : Bool} -> b = False -> b = True -> Void
boolFalseNotTrue Refl Refl impossible

||| Native reducer step on the underlying image state.
public export
NativeImageStep : ImageContext -> ImageEvent -> ImageContext
NativeImageStep ctx evt = (processNativeImage ctx evt).ctx

||| Validated reducer step on the underlying image state.
public export
ValidatedImageStep : ImageContext -> ImageValidatedEvent -> ImageContext
ValidatedImageStep ctx evt = (processImageValidated ctx evt).ctx

||| Generic normalized one-step preservation premise for a Bool predicate over
||| an executable transition.
public export
StepPreserves
  : {state : Type}
 -> {event : Type}
 -> (step : state -> event -> state)
 -> (pred : state -> Bool)
 -> state
 -> event
 -> Type
StepPreserves step pred st evt =
  (if pred st then pred (step st evt) else False) = True

||| Generic trace-level preservation witness built from a one-step witness
||| family and an executable transition.
public export
data TracePreserves
  : {state : Type}
 -> {event : Type}
 -> (step : state -> event -> state)
 -> (stepWitness : state -> event -> Type)
 -> state
 -> List event
 -> Type where
  TracePreservesNil
    : {state : Type}
   -> {event : Type}
   -> {step : state -> event -> state}
   -> {stepWitness : state -> event -> Type}
   -> {st : state}
   -> TracePreserves step stepWitness st []
  TracePreservesCons
    : {state : Type}
   -> {event : Type}
   -> {step : state -> event -> state}
   -> {stepWitness : state -> event -> Type}
   -> {st : state}
   -> {evt : event}
   -> {evts : List event}
   -> stepWitness st evt
   -> TracePreserves step stepWitness (step st evt) evts
   -> TracePreserves step stepWitness st (evt :: evts)

||| Generic decision procedure for one-step Bool-preservation witnesses.
public export
decStepPreserves
  : {state : Type}
 -> {event : Type}
 -> (step : state -> event -> state)
 -> (pred : state -> Bool)
 -> (st : state)
 -> (evt : event)
 -> Dec (StepPreserves step pred st evt)
decStepPreserves step pred st evt
  with (pred st) proof predEq
  decStepPreserves step pred st evt | False =
    No falseNotTrue
  decStepPreserves step pred st evt | True
    with (pred (step st evt)) proof nextEq
    decStepPreserves step pred st evt | True | False =
      No falseNotTrue
    decStepPreserves step pred st evt | True | True =
      Yes Refl

||| Generic decision procedure for trace-level preservation witnesses.
public export
decTracePreserves
  : {state : Type}
 -> {event : Type}
 -> {stepWitness : state -> event -> Type}
 -> (step : state -> event -> state)
 -> ((st : state) -> (evt : event) -> Dec (stepWitness st evt))
 -> (st : state)
 -> (evts : List event)
 -> Dec (TracePreserves step stepWitness st evts)
decTracePreserves step decStep st [] =
  Yes TracePreservesNil
decTracePreserves step decStep st (evt :: evts) =
  case decStep st evt of
    No contra =>
      No (\preserve =>
            case preserve of
              TracePreservesCons hstep _ => contra hstep)
    Yes hstep =>
      case decTracePreserves step decStep (step st evt) evts of
        No contra =>
          No (\preserve =>
                case preserve of
                  TracePreservesCons _ htail => contra htail)
        Yes htail =>
          Yes (TracePreservesCons hstep htail)

||| Normalized one-step preservation premise for image events.
public export
ImageStepPreservesInvariant : ImageContext -> ImageEvent -> Type
ImageStepPreservesInvariant ctx evt =
  StepPreserves NativeImageStep imageContextInvariant ctx evt

||| Normalized one-step preservation premise for the validated image reducer.
public export
ImageValidatedStepPreservesInvariant : ImageContext -> ImageValidatedEvent -> Type
ImageValidatedStepPreservesInvariant ctx evt =
  StepPreserves ValidatedImageStep imageContextInvariant ctx evt

||| Normalized one-step semantic-boundary preservation premise for image events.
public export
ImageStepPreservesSemanticBoundary : ImageContext -> ImageEvent -> Type
ImageStepPreservesSemanticBoundary ctx evt =
  StepPreserves NativeImageStep imageSemanticBoundarySafe ctx evt

||| Normalized one-step semantic-boundary preservation premise for validated
||| image events.
public export
ImageValidatedStepPreservesSemanticBoundary : ImageContext -> ImageValidatedEvent -> Type
ImageValidatedStepPreservesSemanticBoundary ctx evt =
  StepPreserves ValidatedImageStep imageSemanticBoundarySafe ctx evt

||| Normalized one-step preservation premise for the reduced observable
||| boundary alone.
public export
ImageStepPreservesObservableBoundary : ImageContext -> ImageEvent -> Type
ImageStepPreservesObservableBoundary ctx evt =
  StepPreserves NativeImageStep contextObservableStateSafe ctx evt

||| Validated-path version of the reduced observable boundary premise.
public export
ImageValidatedStepPreservesObservableBoundary : ImageContext -> ImageValidatedEvent -> Type
ImageValidatedStepPreservesObservableBoundary ctx evt =
  StepPreserves ValidatedImageStep contextObservableStateSafe ctx evt

||| Recover a typed image-invariant witness from the executable check.
public export
decImageInvariant
  : (ctx : ImageContext) -> Dec (ImageInvariant ctx)
decImageInvariant ctx with (imageContextInvariant ctx) proof invEq
  decImageInvariant ctx | True = Yes (MkImageInvariant invEq)
  decImageInvariant ctx | False =
    No (\(MkImageInvariant holds) => boolFalseNotTrue invEq holds)

||| Recover a typed semantic-boundary witness from the executable check.
public export
decImageSemanticBoundary
  : (ctx : ImageContext) -> Dec (ImageSemanticBoundary ctx)
decImageSemanticBoundary ctx with (imageSemanticBoundarySafe ctx) proof invEq
  decImageSemanticBoundary ctx | True = Yes (MkImageSemanticBoundary invEq)
  decImageSemanticBoundary ctx | False =
    No (\(MkImageSemanticBoundary holds) => boolFalseNotTrue invEq holds)

||| Recover a typed one-step invariant-preservation witness from the
||| executable native reducer check.
public export
decImageStepPreservesInvariant
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> Dec (ImageStepPreservesInvariant ctx evt)
decImageStepPreservesInvariant ctx evt =
  decStepPreserves NativeImageStep imageContextInvariant ctx evt

||| Recover a typed one-step invariant-preservation witness from the
||| executable validated reducer check.
public export
decImageValidatedStepPreservesInvariant
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> Dec (ImageValidatedStepPreservesInvariant ctx evt)
decImageValidatedStepPreservesInvariant ctx evt =
  decStepPreserves ValidatedImageStep imageContextInvariant ctx evt

||| Recover a typed one-step semantic-boundary-preservation witness from the
||| executable native reducer check.
public export
decImageStepPreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> Dec (ImageStepPreservesSemanticBoundary ctx evt)
decImageStepPreservesSemanticBoundary ctx evt =
  decStepPreserves NativeImageStep imageSemanticBoundarySafe ctx evt

||| Recover a typed one-step semantic-boundary-preservation witness from the
||| executable validated reducer check.
public export
decImageValidatedStepPreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> Dec (ImageValidatedStepPreservesSemanticBoundary ctx evt)
decImageValidatedStepPreservesSemanticBoundary ctx evt =
  decStepPreserves ValidatedImageStep imageSemanticBoundarySafe ctx evt

||| Recover a typed observable-boundary witness from the executable check.
public export
decImageObservableBoundary
  : (ctx : ImageContext) -> Dec (ImageObservableBoundary ctx)
decImageObservableBoundary ctx with (contextObservableStateSafe ctx) proof obsEq
  decImageObservableBoundary ctx | True = Yes (MkImageObservableBoundary obsEq)
  decImageObservableBoundary ctx | False =
    No (\(MkImageObservableBoundary holds) => boolFalseNotTrue obsEq holds)

||| Constructive proof that refreshing just the recovery-plan layer rebuilds
||| the stored peer recovery plans from the current authority view.
public export
refreshImageRecoveryPlansDerivesPeerRecoveryPlans
  : (ctx : ImageContext)
 -> ImagePeerRecoveryPlansDerived (refreshImageRecoveryPlans ctx)
refreshImageRecoveryPlansDerivesPeerRecoveryPlans ctx =
  let refresh = refreshImageRecoveryPlansWitness ctx
      actingSame =
        actingReplicaImagesFromCongruent
          {whoamiA = whoami (refreshImageRecoveryPlans ctx)}
          {whoamiB = whoami ctx}
          {actingA = acting (refreshImageRecoveryPlans ctx)}
          {actingB = acting ctx}
          {localA = localImageInfo (refreshImageRecoveryPlans ctx)}
          {localB = localImageInfo ctx}
          {peersA = peerImages (refreshImageRecoveryPlans ctx)}
          {peersB = peerImages ctx}
          (refreshImageRecoveryPlansWhoamiPreserved ctx)
          (refreshImageRecoveryPlansActingPreserved ctx)
          refresh.localInfoPreserved
          refresh.peerImagesPreserved
      refreshedPlanEq =
        replace
          {p = \rhs =>
             peerRecoveryPlans (refreshImageRecoveryPlans ctx)
               = buildPeerRecoveryPlans (authImage ctx) rhs}
          (actingReplicaImagesUnfold ctx)
          refresh.peerRecoveryPlansRecomputed
  in MkImagePeerRecoveryPlansDerived $
       rewrite refresh.authImagePreserved in
       rewrite actingReplicaImagesUnfold (refreshImageRecoveryPlans ctx) in
       rewrite actingSame in
         refreshedPlanEq

||| Constructive proof that refreshing just the recovery-plan layer rebuilds
||| the stored local recovery plan from the current authority view.
public export
refreshImageRecoveryPlansDerivesLocalRecoveryPlan
  : (ctx : ImageContext)
 -> ImageLocalRecoveryPlanDerived (refreshImageRecoveryPlans ctx)
refreshImageRecoveryPlansDerivesLocalRecoveryPlan ctx =
  let refresh = refreshImageRecoveryPlansWitness ctx
  in MkImageLocalRecoveryPlanDerived $
       rewrite refresh.authImagePreserved in
       rewrite refresh.localInfoPreserved in
         refresh.localRecoveryPlanRecomputed

||| Bundle the two constructive recovery-plan lemmas for the recovery-plan
||| refresh helper.
public export
refreshImageRecoveryPlansDerivesRecoveryPlans
  : (ctx : ImageContext)
 -> ImageRecoveryPlansDerived (refreshImageRecoveryPlans ctx)
refreshImageRecoveryPlansDerivesRecoveryPlans ctx =
  MkImageRecoveryPlansDerived
    (refreshImageRecoveryPlansDerivesPeerRecoveryPlans ctx)
    (refreshImageRecoveryPlansDerivesLocalRecoveryPlan ctx)

||| Constructive proof that the full derived refresh ends with peer recovery
||| plans matching the refreshed authority image.
public export
refreshImageDerivedDerivesPeerRecoveryPlans
  : (ctx : ImageContext)
 -> ImagePeerRecoveryPlansDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesPeerRecoveryPlans ctx =
  let planRefresh = refreshImageRecoveryPlansWitness (refreshImageAuthority ctx)
      actingSame =
        actingReplicaImagesFromCongruent
          {whoamiA = whoami (refreshImageRecoveryPlans (refreshImageAuthority ctx))}
          {whoamiB = whoami (refreshImageAuthority ctx)}
          {actingA = acting (refreshImageRecoveryPlans (refreshImageAuthority ctx))}
          {actingB = acting (refreshImageAuthority ctx)}
          {localA = localImageInfo (refreshImageRecoveryPlans (refreshImageAuthority ctx))}
          {localB = localImageInfo (refreshImageAuthority ctx)}
          {peersA = peerImages (refreshImageRecoveryPlans (refreshImageAuthority ctx))}
          {peersB = peerImages (refreshImageAuthority ctx)}
          (refreshImageRecoveryPlansWhoamiPreserved (refreshImageAuthority ctx))
          (refreshImageRecoveryPlansActingPreserved (refreshImageAuthority ctx))
          planRefresh.localInfoPreserved
          planRefresh.peerImagesPreserved
      refreshedPlanEq =
        replace
          {p = \rhs =>
             peerRecoveryPlans (refreshImageRecoveryPlans (refreshImageAuthority ctx))
               = buildPeerRecoveryPlans (authImage (refreshImageAuthority ctx)) rhs}
          (actingReplicaImagesUnfold (refreshImageAuthority ctx))
          planRefresh.peerRecoveryPlansRecomputed
  in MkImagePeerRecoveryPlansDerived $
       rewrite refreshImageDerivedUnfold ctx in
       rewrite planRefresh.authImagePreserved in
       rewrite actingReplicaImagesUnfold (refreshImageRecoveryPlans (refreshImageAuthority ctx)) in
       rewrite actingSame in
         refreshedPlanEq

||| Constructive proof that the full derived refresh ends with the local
||| recovery plan matching the refreshed authority image.
public export
refreshImageDerivedDerivesLocalRecoveryPlan
  : (ctx : ImageContext)
 -> ImageLocalRecoveryPlanDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesLocalRecoveryPlan ctx =
  let planRefresh = refreshImageRecoveryPlansWitness (refreshImageAuthority ctx)
  in MkImageLocalRecoveryPlanDerived $
       rewrite refreshImageDerivedUnfold ctx in
       rewrite planRefresh.authImagePreserved in
       rewrite planRefresh.localInfoPreserved in
         planRefresh.localRecoveryPlanRecomputed

||| Bundle the two constructive recovery-plan lemmas for the full derived
||| refresh helper.
public export
refreshImageDerivedDerivesRecoveryPlans
  : (ctx : ImageContext)
 -> ImageRecoveryPlansDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesRecoveryPlans ctx =
  MkImageRecoveryPlansDerived
    (refreshImageDerivedDerivesPeerRecoveryPlans ctx)
    (refreshImageDerivedDerivesLocalRecoveryPlan ctx)

||| Constructive authority-source recomputation proof for the authority refresh
||| helper.
public export
refreshImageAuthorityDerivesAuthoritySources
  : (ctx : ImageContext)
 -> ImageAuthoritySourcesDerived (refreshImageAuthority ctx)
refreshImageAuthorityDerivesAuthoritySources ctx =
  let refresh = refreshImageAuthorityWitness ctx
      knownCurrent =
        knownPeerImagesFromCongruent
          {whoamiA = whoami (refreshImageAuthority ctx)}
          {whoamiB = whoami ctx}
          {localA = localImageInfo (refreshImageAuthority ctx)}
          {localB = localImageInfo ctx}
          {peersA = peerImages (refreshImageAuthority ctx)}
          {peersB = peerImages ctx}
          (refreshImageAuthorityWhoamiPreserved ctx)
          refresh.localInfoPreserved
          refresh.peerImagesPreserved
      knownSame : (knownPeerImages (refreshImageAuthority ctx) = knownPeerImages ctx)
      knownSame =
        trans
          (knownPeerImagesUnfold (refreshImageAuthority ctx))
          (trans knownCurrent (sym (knownPeerImagesUnfold ctx)))
  in MkImageAuthoritySourcesDerived $
       replace
         {p = \rhs =>
            authSources (refreshImageAuthority ctx) = authoritativeSources rhs}
         (sym knownSame)
         refresh.authSourcesRecomputed

||| Constructive authoritative-image recomputation proof for the authority
||| refresh helper.
public export
refreshImageAuthorityDerivesAuthorityImage
  : (ctx : ImageContext)
 -> ImageAuthorityImageDerived (refreshImageAuthority ctx)
refreshImageAuthorityDerivesAuthorityImage ctx =
  let refresh = refreshImageAuthorityWitness ctx
      knownCurrent =
        knownPeerImagesFromCongruent
          {whoamiA = whoami (refreshImageAuthority ctx)}
          {whoamiB = whoami ctx}
          {localA = localImageInfo (refreshImageAuthority ctx)}
          {localB = localImageInfo ctx}
          {peersA = peerImages (refreshImageAuthority ctx)}
          {peersB = peerImages ctx}
          (refreshImageAuthorityWhoamiPreserved ctx)
          refresh.localInfoPreserved
          refresh.peerImagesPreserved
      knownSame : (knownPeerImages (refreshImageAuthority ctx) = knownPeerImages ctx)
      knownSame =
        trans
          (knownPeerImagesUnfold (refreshImageAuthority ctx))
          (trans knownCurrent (sym (knownPeerImagesUnfold ctx)))
  in MkImageAuthorityImageDerived $
       replace
         {p = \rhs =>
            authImage (refreshImageAuthority ctx)
              = authorityImageValues (authoritativeSources rhs)}
         (sym knownSame)
         refresh.authImageRecomputed

||| Canonical authority-image/auth-sources alignment for the authority refresh
||| helper. This is the proof-facing companion to the executable same-image
||| semantic check.
public export
refreshImageAuthoritySemanticAlignment
  : (ctx : ImageContext)
 -> ImageAuthoritySemanticAlignment (refreshImageAuthority ctx)
refreshImageAuthoritySemanticAlignment ctx =
  let sourcesDerived = refreshImageAuthorityDerivesAuthoritySources ctx
      imageDerived = refreshImageAuthorityDerivesAuthorityImage ctx
      alignedRhs
        : (authorityImageValues (authoritativeSources (knownPeerImages (refreshImageAuthority ctx)))
            = authorityImageValues (authSources (refreshImageAuthority ctx)))
      alignedRhs =
        replace
          {p = \rhs =>
             authorityImageValues (authoritativeSources (knownPeerImages (refreshImageAuthority ctx)))
               = authorityImageValues rhs}
          (sym sourcesDerived.holds)
          Refl
  in MkImageAuthoritySemanticAlignment $
       trans imageDerived.holds alignedRhs

||| Bundle the constructive authority refresh facts.
public export
refreshImageAuthorityDerivesAuthority
  : (ctx : ImageContext)
 -> ImageAuthorityDerived (refreshImageAuthority ctx)
refreshImageAuthorityDerivesAuthority ctx =
  MkImageAuthorityDerived
    (refreshImageAuthorityDerivesAuthoritySources ctx)
    (refreshImageAuthorityDerivesAuthorityImage ctx)
    (refreshImageAuthoritySemanticAlignment ctx)

||| The full derived refresh preserves the authority-source recomputation fact.
public export
refreshImageDerivedDerivesAuthoritySources
  : (ctx : ImageContext)
 -> ImageAuthoritySourcesDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesAuthoritySources ctx =
  let authRefresh = refreshImageAuthorityWitness ctx
      planRefresh = refreshImageRecoveryPlansWitness (refreshImageAuthority ctx)
      whoamiSame : (whoami (refreshImageDerived ctx) = whoami ctx)
      whoamiSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans (refreshImageRecoveryPlansWhoamiPreserved (refreshImageAuthority ctx))
                (refreshImageAuthorityWhoamiPreserved ctx)
      localSame : (localImageInfo (refreshImageDerived ctx) = localImageInfo ctx)
      localSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.localInfoPreserved authRefresh.localInfoPreserved
      peerSame : (peerImages (refreshImageDerived ctx) = peerImages ctx)
      peerSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.peerImagesPreserved authRefresh.peerImagesPreserved
      knownCurrent =
        knownPeerImagesFromCongruent
          {whoamiA = whoami (refreshImageDerived ctx)}
          {whoamiB = whoami ctx}
          {localA = localImageInfo (refreshImageDerived ctx)}
          {localB = localImageInfo ctx}
          {peersA = peerImages (refreshImageDerived ctx)}
          {peersB = peerImages ctx}
          whoamiSame
          localSame
          peerSame
      knownSame : (knownPeerImages (refreshImageDerived ctx) = knownPeerImages ctx)
      knownSame =
        trans
          (knownPeerImagesUnfold (refreshImageDerived ctx))
          (trans knownCurrent (sym (knownPeerImagesUnfold ctx)))
      sourcesEq : (authSources (refreshImageDerived ctx) = authoritativeSources (knownPeerImages ctx))
      sourcesEq =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.authSourcesPreserved authRefresh.authSourcesRecomputed
  in MkImageAuthoritySourcesDerived $
       replace
         {p = \rhs =>
            authSources (refreshImageDerived ctx) = authoritativeSources rhs}
         (sym knownSame)
         sourcesEq

||| The full derived refresh preserves the authoritative-image recomputation
||| fact.
public export
refreshImageDerivedDerivesAuthorityImage
  : (ctx : ImageContext)
 -> ImageAuthorityImageDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesAuthorityImage ctx =
  let authRefresh = refreshImageAuthorityWitness ctx
      planRefresh = refreshImageRecoveryPlansWitness (refreshImageAuthority ctx)
      whoamiSame : (whoami (refreshImageDerived ctx) = whoami ctx)
      whoamiSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans (refreshImageRecoveryPlansWhoamiPreserved (refreshImageAuthority ctx))
                (refreshImageAuthorityWhoamiPreserved ctx)
      localSame : (localImageInfo (refreshImageDerived ctx) = localImageInfo ctx)
      localSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.localInfoPreserved authRefresh.localInfoPreserved
      peerSame : (peerImages (refreshImageDerived ctx) = peerImages ctx)
      peerSame =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.peerImagesPreserved authRefresh.peerImagesPreserved
      knownCurrent =
        knownPeerImagesFromCongruent
          {whoamiA = whoami (refreshImageDerived ctx)}
          {whoamiB = whoami ctx}
          {localA = localImageInfo (refreshImageDerived ctx)}
          {localB = localImageInfo ctx}
          {peersA = peerImages (refreshImageDerived ctx)}
          {peersB = peerImages ctx}
          whoamiSame
          localSame
          peerSame
      knownSame : (knownPeerImages (refreshImageDerived ctx) = knownPeerImages ctx)
      knownSame =
        trans
          (knownPeerImagesUnfold (refreshImageDerived ctx))
          (trans knownCurrent (sym (knownPeerImagesUnfold ctx)))
      imageEq
        : (authImage (refreshImageDerived ctx)
            = authorityImageValues (authoritativeSources (knownPeerImages ctx)))
      imageEq =
        rewrite refreshImageDerivedUnfold ctx in
          trans planRefresh.authImagePreserved authRefresh.authImageRecomputed
  in MkImageAuthorityImageDerived $
       replace
         {p = \rhs =>
            authImage (refreshImageDerived ctx)
              = authorityImageValues (authoritativeSources rhs)}
         (sym knownSame)
         imageEq

||| Canonical authority-image/auth-sources alignment for the full derived
||| refresh.
public export
refreshImageDerivedSemanticAlignment
  : (ctx : ImageContext)
 -> ImageAuthoritySemanticAlignment (refreshImageDerived ctx)
refreshImageDerivedSemanticAlignment ctx =
  let sourcesDerived = refreshImageDerivedDerivesAuthoritySources ctx
      imageDerived = refreshImageDerivedDerivesAuthorityImage ctx
      alignedRhs
        : (authorityImageValues (authoritativeSources (knownPeerImages (refreshImageDerived ctx)))
            = authorityImageValues (authSources (refreshImageDerived ctx)))
      alignedRhs =
        replace
          {p = \rhs =>
             authorityImageValues (authoritativeSources (knownPeerImages (refreshImageDerived ctx)))
               = authorityImageValues rhs}
          (sym sourcesDerived.holds)
          Refl
  in MkImageAuthoritySemanticAlignment $
       trans imageDerived.holds alignedRhs

||| Bundle the constructive authority facts for the full derived refresh.
public export
refreshImageDerivedDerivesAuthority
  : (ctx : ImageContext)
 -> ImageAuthorityDerived (refreshImageDerived ctx)
refreshImageDerivedDerivesAuthority ctx =
  MkImageAuthorityDerived
    (refreshImageDerivedDerivesAuthoritySources ctx)
    (refreshImageDerivedDerivesAuthorityImage ctx)
    (refreshImageDerivedSemanticAlignment ctx)

||| Recover a typed one-step observable-boundary-preservation witness from the
||| executable native reducer check.
public export
decImageStepPreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> Dec (ImageStepPreservesObservableBoundary ctx evt)
decImageStepPreservesObservableBoundary ctx evt =
  decStepPreserves NativeImageStep contextObservableStateSafe ctx evt

||| Recover a typed one-step observable-boundary-preservation witness from the
||| executable validated reducer check.
public export
decImageValidatedStepPreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> Dec (ImageValidatedStepPreservesObservableBoundary ctx evt)
decImageValidatedStepPreservesObservableBoundary ctx evt =
  decStepPreserves ValidatedImageStep contextObservableStateSafe ctx evt

||| Trace-level preservation witness for image events.
public export
ImageTracePreservesInvariant : ImageContext -> List ImageEvent -> Type
ImageTracePreservesInvariant ctx evts =
  TracePreserves NativeImageStep ImageStepPreservesInvariant ctx evts

||| Trace-level preservation witness for validated image events.
public export
ImageValidatedTracePreservesInvariant : ImageContext -> List ImageValidatedEvent -> Type
ImageValidatedTracePreservesInvariant ctx evts =
  TracePreserves ValidatedImageStep ImageValidatedStepPreservesInvariant ctx evts

||| Trace-level preservation witness for the reduced semantic boundary.
public export
ImageTracePreservesSemanticBoundary : ImageContext -> List ImageEvent -> Type
ImageTracePreservesSemanticBoundary ctx evts =
  TracePreserves NativeImageStep ImageStepPreservesSemanticBoundary ctx evts

||| Trace-level preservation witness for the reduced semantic boundary on the
||| validated reducer path.
public export
ImageValidatedTracePreservesSemanticBoundary : ImageContext -> List ImageValidatedEvent -> Type
ImageValidatedTracePreservesSemanticBoundary ctx evts =
  TracePreserves ValidatedImageStep ImageValidatedStepPreservesSemanticBoundary ctx evts

||| Decide trace-level preservation of the core image invariant.
public export
decImageTracePreservesInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> Dec (ImageTracePreservesInvariant ctx evts)
decImageTracePreservesInvariant ctx evts =
  decTracePreserves NativeImageStep decImageStepPreservesInvariant ctx evts

||| Decide trace-level preservation of the core image invariant on the
||| validated reducer path.
public export
decImageValidatedTracePreservesInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> Dec (ImageValidatedTracePreservesInvariant ctx evts)
decImageValidatedTracePreservesInvariant ctx evts =
  decTracePreserves ValidatedImageStep
                    decImageValidatedStepPreservesInvariant
                    ctx
                    evts

||| Decide trace-level preservation of the reduced semantic boundary.
public export
decImageTracePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> Dec (ImageTracePreservesSemanticBoundary ctx evts)
decImageTracePreservesSemanticBoundary ctx evts =
  decTracePreserves NativeImageStep
                    decImageStepPreservesSemanticBoundary
                    ctx
                    evts

||| Decide trace-level preservation of the reduced semantic boundary on the
||| validated reducer path.
public export
decImageValidatedTracePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> Dec (ImageValidatedTracePreservesSemanticBoundary ctx evts)
decImageValidatedTracePreservesSemanticBoundary ctx evts =
  decTracePreserves ValidatedImageStep
                    decImageValidatedStepPreservesSemanticBoundary
                    ctx
                    evts

||| Trace-level preservation witness for the reduced observable boundary alone.
public export
ImageTracePreservesObservableBoundary : ImageContext -> List ImageEvent -> Type
ImageTracePreservesObservableBoundary ctx evts =
  TracePreserves NativeImageStep ImageStepPreservesObservableBoundary ctx evts

||| Trace-level preservation witness for the reduced observable boundary on the
||| validated reducer path.
public export
ImageValidatedTracePreservesObservableBoundary
  : ImageContext -> List ImageValidatedEvent -> Type
ImageValidatedTracePreservesObservableBoundary ctx evts =
  TracePreserves ValidatedImageStep
                 ImageValidatedStepPreservesObservableBoundary
                 ctx
                 evts

||| Decide trace-level preservation over the reduced observable boundary.
public export
decImageTracePreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> Dec (ImageTracePreservesObservableBoundary ctx evts)
decImageTracePreservesObservableBoundary ctx evts =
  decTracePreserves NativeImageStep
                    decImageStepPreservesObservableBoundary
                    ctx
                    evts

||| Decide trace-level preservation over the reduced observable boundary on the
||| validated reducer path.
public export
decImageValidatedTracePreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> Dec (ImageValidatedTracePreservesObservableBoundary ctx evts)
decImageValidatedTracePreservesObservableBoundary ctx evts =
  decTracePreserves ValidatedImageStep
                    decImageValidatedStepPreservesObservableBoundary
                    ctx
                    evts

||| Trace-level witness over the smaller proof-facing snapshots.
public export
data ObservedObservableSnapshotTraceRefinesSemanticBoundary
  : ImageContext -> List (ImageEvent, ObservableImageSnapshot) -> Type where
  ObservedObservableSnapshotTraceNil
    : {ctx : ImageContext}
   -> ObservedObservableSnapshotTraceRefinesSemanticBoundary ctx []
  ObservedObservableSnapshotTraceCons
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ObservableImageSnapshot}
   -> {rest : List (ImageEvent, ObservableImageSnapshot)}
   -> ObservableProofSnapshotCppStepSimulates ctx evt snap
   -> ObservedObservableSnapshotTraceRefinesSemanticBoundary (processNativeImage ctx evt).ctx rest
   -> ObservedObservableSnapshotTraceRefinesSemanticBoundary ctx ((evt, snap) :: rest)

||| Validated-path trace-level witness over the smaller proof-facing
||| snapshots.
public export
data ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary
  : ImageContext -> List (ImageValidatedEvent, ObservableImageSnapshot) -> Type where
  ObservedValidatedObservableSnapshotTraceNil
    : {ctx : ImageContext}
   -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx []
  ObservedValidatedObservableSnapshotTraceCons
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ObservableImageSnapshot}
   -> {rest : List (ImageValidatedEvent, ObservableImageSnapshot)}
   -> ObservableValidatedProofSnapshotCppStepSimulates ctx evt snap
   -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary (processImageValidated ctx evt).ctx rest
   -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx ((evt, snap) :: rest)

||| Event projection for traces over the smaller proof-facing snapshots.
public export
proofSnapshotTraceEvents
  : List (ImageEvent, ObservableImageSnapshot) -> List ImageEvent
proofSnapshotTraceEvents [] = []
proofSnapshotTraceEvents ((evt, _) :: rest) =
  evt :: proofSnapshotTraceEvents rest

||| Semantic proof-trace event projection.
public export
semanticSnapshotTraceEvents
  : List (ImageEvent, ImageSemanticSnapshot) -> List ImageEvent
semanticSnapshotTraceEvents = proofSnapshotTraceEvents

||| Event projection for validated traces over the smaller proof-facing
||| snapshots.
public export
validatedProofSnapshotTraceEvents
  : List (ImageValidatedEvent, ObservableImageSnapshot)
 -> List ImageValidatedEvent
validatedProofSnapshotTraceEvents [] = []
validatedProofSnapshotTraceEvents ((evt, _) :: rest) =
  evt :: validatedProofSnapshotTraceEvents rest

||| Semantic proof-trace event projection on the validated path.
public export
validatedSemanticSnapshotTraceEvents
  : List (ImageValidatedEvent, ImageSemanticSnapshot)
 -> List ImageValidatedEvent
validatedSemanticSnapshotTraceEvents = validatedProofSnapshotTraceEvents

||| Event projection for traces over the full replay snapshot surface.
public export
observedImageTraceEvents
  : List (ImageEvent, ImageObservedSnapshot) -> List ImageEvent
observedImageTraceEvents [] = []
observedImageTraceEvents ((evt, _) :: rest) =
  evt :: observedImageTraceEvents rest

||| Event projection for validated traces over the full replay snapshot
||| surface.
public export
validatedObservedImageTraceEvents
  : List (ImageValidatedEvent, ImageObservedSnapshot)
 -> List ImageValidatedEvent
validatedObservedImageTraceEvents [] = []
validatedObservedImageTraceEvents ((evt, _) :: rest) =
  evt :: validatedObservedImageTraceEvents rest

||| Canonical proof-facing trace generated by the native reducer itself.
public export
proofSnapshotTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> List (ImageEvent, ObservableImageSnapshot)
proofSnapshotTraceOf ctx [] = []
proofSnapshotTraceOf ctx (evt :: evts) =
  let nextCtx = (processNativeImage ctx evt).ctx
  in (evt, observableSnapshotOfContext nextCtx)
      :: proofSnapshotTraceOf nextCtx evts

||| Canonical semantic proof trace generated by the native reducer itself.
public export
semanticSnapshotTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> List (ImageEvent, ImageSemanticSnapshot)
semanticSnapshotTraceOf = proofSnapshotTraceOf

||| Canonical proof-facing trace generated by the validated reducer itself.
public export
validatedProofSnapshotTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> List (ImageValidatedEvent, ObservableImageSnapshot)
validatedProofSnapshotTraceOf ctx [] = []
validatedProofSnapshotTraceOf ctx (evt :: evts) =
  let nextCtx = (processImageValidated ctx evt).ctx
  in (evt, observableSnapshotOfContext nextCtx)
      :: validatedProofSnapshotTraceOf nextCtx evts

||| Canonical semantic proof trace generated by the validated reducer itself.
public export
validatedSemanticSnapshotTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> List (ImageValidatedEvent, ImageSemanticSnapshot)
validatedSemanticSnapshotTraceOf = validatedProofSnapshotTraceOf

||| Canonical full replay-snapshot trace generated by the native reducer
||| itself.
public export
observedImageTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> List (ImageEvent, ImageObservedSnapshot)
observedImageTraceOf ctx [] = []
observedImageTraceOf ctx (evt :: evts) =
  let nextCtx = (processNativeImage ctx evt).ctx
  in (evt, imageObservedSnapshot nextCtx)
      :: observedImageTraceOf nextCtx evts

||| Projection from a replay/debug trace to the semantic proof trace.
public export
semanticSnapshotTraceOfReplayTrace
  : List (ImageEvent, ImageReplaySnapshot)
 -> List (ImageEvent, ImageSemanticSnapshot)
semanticSnapshotTraceOfReplayTrace [] = []
semanticSnapshotTraceOfReplayTrace ((evt, snap) :: rest) =
  (evt, observableSnapshotOfObserved snap)
    :: semanticSnapshotTraceOfReplayTrace rest

||| Canonical full replay-snapshot trace generated by the validated reducer
||| itself.
public export
validatedObservedImageTraceOf
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> List (ImageValidatedEvent, ImageObservedSnapshot)
validatedObservedImageTraceOf ctx [] = []
validatedObservedImageTraceOf ctx (evt :: evts) =
  let nextCtx = (processImageValidated ctx evt).ctx
  in (evt, imageObservedSnapshot nextCtx)
      :: validatedObservedImageTraceOf nextCtx evts

||| Projection from a validated replay/debug trace to the semantic proof
||| trace.
public export
validatedSemanticSnapshotTraceOfReplayTrace
  : List (ImageValidatedEvent, ImageReplaySnapshot)
 -> List (ImageValidatedEvent, ImageSemanticSnapshot)
validatedSemanticSnapshotTraceOfReplayTrace [] = []
validatedSemanticSnapshotTraceOfReplayTrace ((evt, snap) :: rest) =
  (evt, observableSnapshotOfObserved snap)
    :: validatedSemanticSnapshotTraceOfReplayTrace rest

||| Typed trace-level simulation witness for the full replay snapshot surface.
||| This is the trace analogue of `ObservableImageCppStepSimulates`.
public export
data ObservedImageTraceSimulates
  : ImageContext -> List (ImageEvent, ImageObservedSnapshot) -> Type where
  ObservedImageSimulationTraceNil
    : {ctx : ImageContext}
   -> ObservedImageTraceSimulates ctx []
  ObservedImageSimulationTraceCons
    : {ctx : ImageContext}
   -> {evt : ImageEvent}
   -> {snap : ImageObservedSnapshot}
   -> {rest : List (ImageEvent, ImageObservedSnapshot)}
   -> ObservableImageCppStepSimulates ctx evt snap
   -> ObservedImageTraceSimulates (processNativeImage ctx evt).ctx rest
   -> ObservedImageTraceSimulates ctx ((evt, snap) :: rest)

||| Validated-path typed trace-level simulation witness for the full replay
||| snapshot surface.
public export
data ObservedValidatedImageTraceSimulates
  : ImageContext -> List (ImageValidatedEvent, ImageObservedSnapshot) -> Type where
  ObservedValidatedImageSimulationTraceNil
    : {ctx : ImageContext}
   -> ObservedValidatedImageTraceSimulates ctx []
  ObservedValidatedImageSimulationTraceCons
    : {ctx : ImageContext}
   -> {evt : ImageValidatedEvent}
   -> {snap : ImageObservedSnapshot}
   -> {rest : List (ImageValidatedEvent, ImageObservedSnapshot)}
   -> ObservableValidatedImageCppStepSimulates ctx evt snap
   -> ObservedValidatedImageTraceSimulates (processImageValidated ctx evt).ctx rest
   -> ObservedValidatedImageTraceSimulates ctx ((evt, snap) :: rest)

||| The native reducer's own proof-facing emitted trace simulates itself
||| by construction.
public export
selfObservedObservableSnapshotTraceRefinesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ObservedObservableSnapshotTraceRefinesSemanticBoundary
      ctx
      (proofSnapshotTraceOf ctx evts)
selfObservedObservableSnapshotTraceRefinesSemanticBoundary ctx [] =
  ObservedObservableSnapshotTraceNil
selfObservedObservableSnapshotTraceRefinesSemanticBoundary ctx (evt :: evts) =
  let headSim = observableProofSnapshotCppStepSelfSimulates ctx evt
      tailSim =
        selfObservedObservableSnapshotTraceRefinesSemanticBoundary
          ((processNativeImage ctx evt).ctx)
          evts
  in ObservedObservableSnapshotTraceCons headSim tailSim

||| The validated reducer's own proof-facing emitted trace simulates itself
||| by construction.
public export
selfObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary
      ctx
      (validatedProofSnapshotTraceOf ctx evts)
selfObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx [] =
  ObservedValidatedObservableSnapshotTraceNil
selfObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx (evt :: evts) =
  let headSim = observableValidatedProofSnapshotCppStepSelfSimulates ctx evt
      tailSim =
        selfObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary
          ((processImageValidated ctx evt).ctx)
          evts
  in ObservedValidatedObservableSnapshotTraceCons headSim tailSim

||| The native reducer's own full replay-snapshot trace simulates itself by
||| construction.
public export
selfObservedImageTraceSimulates
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ObservedImageTraceSimulates ctx (observedImageTraceOf ctx evts)
selfObservedImageTraceSimulates ctx [] =
  ObservedImageSimulationTraceNil
selfObservedImageTraceSimulates ctx (evt :: evts) =
  let headSim = observableImageCppStepSelfSimulates ctx evt
      tailSim =
        selfObservedImageTraceSimulates
          ((processNativeImage ctx evt).ctx)
          evts
  in ObservedImageSimulationTraceCons headSim tailSim

||| The validated reducer's own full replay-snapshot trace simulates itself
||| by construction.
public export
selfObservedValidatedImageTraceSimulates
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ObservedValidatedImageTraceSimulates ctx (validatedObservedImageTraceOf ctx evts)
selfObservedValidatedImageTraceSimulates ctx [] =
  ObservedValidatedImageSimulationTraceNil
selfObservedValidatedImageTraceSimulates ctx (evt :: evts) =
  let headSim = observableValidatedImageCppStepSelfSimulates ctx evt
      tailSim =
        selfObservedValidatedImageTraceSimulates
          ((processImageValidated ctx evt).ctx)
          evts
  in ObservedValidatedImageSimulationTraceCons headSim tailSim

||| Replay/debug trace projection preserves the emitted event stream.
public export
semanticSnapshotReplayTraceEvents
  : (trace : List (ImageEvent, ImageReplaySnapshot))
 -> proofSnapshotTraceEvents (semanticSnapshotTraceOfReplayTrace trace)
    = observedImageTraceEvents trace
semanticSnapshotReplayTraceEvents [] = Refl
semanticSnapshotReplayTraceEvents ((evt, _) :: rest) =
  rewrite semanticSnapshotReplayTraceEvents rest in Refl

||| Validated replay/debug trace projection preserves the emitted event
||| stream.
public export
validatedSemanticSnapshotReplayTraceEvents
  : (trace : List (ImageValidatedEvent, ImageReplaySnapshot))
 -> validatedProofSnapshotTraceEvents
      (validatedSemanticSnapshotTraceOfReplayTrace trace)
    = validatedObservedImageTraceEvents trace
validatedSemanticSnapshotReplayTraceEvents [] = Refl
validatedSemanticSnapshotReplayTraceEvents ((evt, _) :: rest) =
  rewrite validatedSemanticSnapshotReplayTraceEvents rest in Refl

||| Project a replay/debug native trace simulation witness onto the semantic
||| proof-trace surface.
public export
observedImageTraceSimulatesProjectsToSemanticTrace
  : {ctx : ImageContext}
 -> {trace : List (ImageEvent, ImageReplaySnapshot)}
 -> ObservedImageTraceSimulates ctx trace
 -> ObservedObservableSnapshotTraceRefinesSemanticBoundary
      ctx
      (semanticSnapshotTraceOfReplayTrace trace)
observedImageTraceSimulatesProjectsToSemanticTrace
  ObservedImageSimulationTraceNil =
    ObservedObservableSnapshotTraceNil
observedImageTraceSimulatesProjectsToSemanticTrace
  (ObservedImageSimulationTraceCons hhead htail) =
    ObservedObservableSnapshotTraceCons
      (observableImageSimulationProjectsToProofSnapshot hhead)
      (observedImageTraceSimulatesProjectsToSemanticTrace htail)

||| Project a replay/debug validated trace simulation witness onto the
||| semantic proof-trace surface.
public export
observedValidatedImageTraceSimulatesProjectsToSemanticTrace
  : {ctx : ImageContext}
 -> {trace : List (ImageValidatedEvent, ImageReplaySnapshot)}
 -> ObservedValidatedImageTraceSimulates ctx trace
 -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary
      ctx
      (validatedSemanticSnapshotTraceOfReplayTrace trace)
observedValidatedImageTraceSimulatesProjectsToSemanticTrace
  ObservedValidatedImageSimulationTraceNil =
    ObservedValidatedObservableSnapshotTraceNil
observedValidatedImageTraceSimulatesProjectsToSemanticTrace
  (ObservedValidatedImageSimulationTraceCons hhead htail) =
    ObservedValidatedObservableSnapshotTraceCons
      (observableValidatedImageSimulationProjectsToProofSnapshot hhead)
      (observedValidatedImageTraceSimulatesProjectsToSemanticTrace htail)

||| Trace-level safety witness for the smaller proof-facing snapshot surface.
public export
data ObservedObservableSnapshotTraceSafe
  : List (ImageEvent, ObservableImageSnapshot) -> Type where
  ObservedObservableSnapshotTraceSafeNil
    : ObservedObservableSnapshotTraceSafe []
  ObservedObservableSnapshotTraceSafeCons
    : {evt : ImageEvent}
   -> {snap : ObservableImageSnapshot}
   -> {rest : List (ImageEvent, ObservableImageSnapshot)}
   -> ObservedObservableSnapshotBoundary snap
   -> ObservedObservableSnapshotTraceSafe rest
   -> ObservedObservableSnapshotTraceSafe ((evt, snap) :: rest)

||| Validated-path trace-level safety witness for the smaller proof-facing
||| snapshot surface.
public export
data ObservedValidatedObservableSnapshotTraceSafe
  : List (ImageValidatedEvent, ObservableImageSnapshot) -> Type where
  ObservedValidatedObservableSnapshotTraceSafeNil
    : ObservedValidatedObservableSnapshotTraceSafe []
  ObservedValidatedObservableSnapshotTraceSafeCons
    : {evt : ImageValidatedEvent}
   -> {snap : ObservableImageSnapshot}
   -> {rest : List (ImageValidatedEvent, ObservableImageSnapshot)}
   -> ObservedObservableSnapshotBoundary snap
   -> ObservedValidatedObservableSnapshotTraceSafe rest
   -> ObservedValidatedObservableSnapshotTraceSafe ((evt, snap) :: rest)

||| Trace-level safety witness for the full replay snapshot surface.
public export
data ObservedImageTraceSafe
  : List (ImageEvent, ImageObservedSnapshot) -> Type where
  ObservedImageTraceSafeNil
    : ObservedImageTraceSafe []
  ObservedImageTraceSafeCons
    : {evt : ImageEvent}
   -> {snap : ImageObservedSnapshot}
   -> {rest : List (ImageEvent, ImageObservedSnapshot)}
   -> ObservedImageBoundary snap
   -> ObservedImageTraceSafe rest
   -> ObservedImageTraceSafe ((evt, snap) :: rest)

||| Validated-path trace-level safety witness for the full replay snapshot
||| surface.
public export
data ObservedValidatedImageTraceSafe
  : List (ImageValidatedEvent, ImageObservedSnapshot) -> Type where
  ObservedValidatedImageTraceSafeNil
    : ObservedValidatedImageTraceSafe []
  ObservedValidatedImageTraceSafeCons
    : {evt : ImageValidatedEvent}
   -> {snap : ImageObservedSnapshot}
   -> {rest : List (ImageValidatedEvent, ImageObservedSnapshot)}
   -> ObservedImageBoundary snap
   -> ObservedValidatedImageTraceSafe rest
   -> ObservedValidatedImageTraceSafe ((evt, snap) :: rest)

||| Final typed trace-refinement result on the smaller proof-facing snapshot
||| surface.
public export
record ObservedObservableSnapshotTraceRefinement
    (ctx : ImageContext)
    (trace : List (ImageEvent, ObservableImageSnapshot)) where
  constructor MkObservedObservableSnapshotTraceRefinement
  finalBoundary
    : ImageObservableBoundary
        (processNativeImageTrace ctx (proofSnapshotTraceEvents trace))
  emittedSnapshotsSafe
    : ObservedObservableSnapshotTraceSafe trace

||| Validated-path final typed trace-refinement result on the smaller
||| proof-facing snapshot surface.
public export
record ObservedValidatedObservableSnapshotTraceRefinement
    (ctx : ImageContext)
    (trace : List (ImageValidatedEvent, ObservableImageSnapshot)) where
  constructor MkObservedValidatedObservableSnapshotTraceRefinement
  validatedFinalBoundary
    : ImageObservableBoundary
        (processImageValidatedTrace ctx (validatedProofSnapshotTraceEvents trace))
  validatedEmittedSnapshotsSafe
    : ObservedValidatedObservableSnapshotTraceSafe trace

||| Final typed trace-refinement result on the full replay snapshot surface.
public export
record ObservedImageTraceRefinement
    (ctx : ImageContext)
    (trace : List (ImageEvent, ImageObservedSnapshot)) where
  constructor MkObservedImageTraceRefinement
  finalReplayBoundary
    : ImageObservableBoundary
        (processNativeImageTrace ctx (observedImageTraceEvents trace))
  emittedReplaySnapshotsSafe
    : ObservedImageTraceSafe trace

||| Validated-path final typed trace-refinement result on the full replay
||| snapshot surface.
public export
record ObservedValidatedImageTraceRefinement
    (ctx : ImageContext)
    (trace : List (ImageValidatedEvent, ImageObservedSnapshot)) where
  constructor MkObservedValidatedImageTraceRefinement
  validatedFinalReplayBoundary
    : ImageObservableBoundary
        (processImageValidatedTrace ctx (validatedObservedImageTraceEvents trace))
  validatedEmittedReplaySnapshotsSafe
    : ObservedValidatedImageTraceSafe trace

||| Semantic proof-trace refinement aliases. These are the canonical typed
||| proof results; full replay-snapshot refinement remains a replay/debug
||| wrapper around them.
public export
ObservedSemanticSnapshotTraceRefinement
  : ImageContext -> List (ImageEvent, ImageSemanticSnapshot) -> Type
ObservedSemanticSnapshotTraceRefinement =
  ObservedObservableSnapshotTraceRefinement

public export
ObservedValidatedSemanticSnapshotTraceRefinement
  : ImageContext -> List (ImageValidatedEvent, ImageSemanticSnapshot) -> Type
ObservedValidatedSemanticSnapshotTraceRefinement =
  ObservedValidatedObservableSnapshotTraceRefinement

||| Preservation theorem for one image step.
public export
imageProofStepPreservesInvariant
  : (ctx : ImageContext) -> (evt : ImageEvent) -> ImageInvariant ctx
  -> ImageStepPreservesInvariant ctx evt
  -> ImageInvariant (processNativeImage ctx evt).ctx
imageProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve
  with (imageContextInvariant ctx) proof invEq
  imageProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve | False impossible
  imageProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve | True =
    MkImageInvariant hpreserve

||| Preservation theorem for one validated image step.
public export
imageValidatedProofStepPreservesInvariant
  : (ctx : ImageContext) -> (evt : ImageValidatedEvent) -> ImageInvariant ctx
  -> ImageValidatedStepPreservesInvariant ctx evt
  -> ImageInvariant (processImageValidated ctx evt).ctx
imageValidatedProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve
  with (imageContextInvariant ctx) proof invEq
  imageValidatedProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve | False impossible
  imageValidatedProofStepPreservesInvariant ctx evt (MkImageInvariant invCtx) hpreserve | True =
    MkImageInvariant hpreserve

||| Preservation theorem for one image step over the reduced semantic boundary.
public export
imageProofStepPreservesSemanticBoundary
  : (ctx : ImageContext) -> (evt : ImageEvent) -> ImageSemanticBoundary ctx
  -> ImageStepPreservesSemanticBoundary ctx evt
  -> ImageSemanticBoundary (processNativeImage ctx evt).ctx
imageProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve
  with (imageSemanticBoundarySafe ctx) proof invEq
  imageProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve | False impossible
  imageProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve | True =
    MkImageSemanticBoundary hpreserve

||| Preservation theorem for one validated image step over the reduced
||| semantic boundary.
public export
imageValidatedProofStepPreservesSemanticBoundary
  : (ctx : ImageContext) -> (evt : ImageValidatedEvent) -> ImageSemanticBoundary ctx
  -> ImageValidatedStepPreservesSemanticBoundary ctx evt
  -> ImageSemanticBoundary (processImageValidated ctx evt).ctx
imageValidatedProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve
  with (imageSemanticBoundarySafe ctx) proof invEq
  imageValidatedProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve | False impossible
  imageValidatedProofStepPreservesSemanticBoundary ctx evt (MkImageSemanticBoundary invCtx) hpreserve | True =
    MkImageSemanticBoundary hpreserve

||| Preservation theorem for one image step over the reduced observable
||| boundary alone.
public export
imageProofStepPreservesObservableBoundary
  : (ctx : ImageContext) -> (evt : ImageEvent) -> ImageObservableBoundary ctx
  -> ImageStepPreservesObservableBoundary ctx evt
  -> ImageObservableBoundary (processNativeImage ctx evt).ctx
imageProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve
  with (contextObservableStateSafe ctx) proof invEq
  imageProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve | False impossible
  imageProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve | True =
    MkImageObservableBoundary hpreserve

||| Preservation theorem for one validated image step over the reduced
||| observable boundary alone.
public export
imageValidatedProofStepPreservesObservableBoundary
  : (ctx : ImageContext) -> (evt : ImageValidatedEvent) -> ImageObservableBoundary ctx
  -> ImageValidatedStepPreservesObservableBoundary ctx evt
  -> ImageObservableBoundary (processImageValidated ctx evt).ctx
imageValidatedProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve
  with (contextObservableStateSafe ctx) proof invEq
  imageValidatedProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve | False impossible
  imageValidatedProofStepPreservesObservableBoundary ctx evt (MkImageObservableBoundary invCtx) hpreserve | True =
    MkImageObservableBoundary hpreserve

||| Build the native one-step invariant-preservation theorem directly from the
||| executable step check.
public export
buildImageStepInvariant
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ImageInvariant ctx
 -> Maybe (ImageInvariant (processNativeImage ctx evt).ctx)
buildImageStepInvariant ctx evt inv =
  case decImageStepPreservesInvariant ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageProofStepPreservesInvariant ctx evt inv hpreserve)

||| Build the validated one-step invariant-preservation theorem directly from
||| the executable step check.
public export
buildValidatedImageStepInvariant
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ImageInvariant ctx
 -> Maybe (ImageInvariant (processImageValidated ctx evt).ctx)
buildValidatedImageStepInvariant ctx evt inv =
  case decImageValidatedStepPreservesInvariant ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageValidatedProofStepPreservesInvariant ctx evt inv hpreserve)

||| Build the native one-step semantic-boundary-preservation theorem directly
||| from the executable step check.
public export
buildImageStepSemanticBoundary
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ImageSemanticBoundary ctx
 -> Maybe (ImageSemanticBoundary (processNativeImage ctx evt).ctx)
buildImageStepSemanticBoundary ctx evt inv =
  case decImageStepPreservesSemanticBoundary ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageProofStepPreservesSemanticBoundary ctx evt inv hpreserve)

||| Build the validated one-step semantic-boundary-preservation theorem
||| directly from the executable step check.
public export
buildValidatedImageStepSemanticBoundary
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ImageSemanticBoundary ctx
 -> Maybe (ImageSemanticBoundary (processImageValidated ctx evt).ctx)
buildValidatedImageStepSemanticBoundary ctx evt inv =
  case decImageValidatedStepPreservesSemanticBoundary ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageValidatedProofStepPreservesSemanticBoundary ctx evt inv hpreserve)

||| Build the native one-step observable-boundary-preservation theorem
||| directly from the executable step check.
public export
buildImageStepObservableBoundary
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ImageObservableBoundary (processNativeImage ctx evt).ctx)
buildImageStepObservableBoundary ctx evt inv =
  case decImageStepPreservesObservableBoundary ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageProofStepPreservesObservableBoundary ctx evt inv hpreserve)

||| Build the validated one-step observable-boundary-preservation theorem
||| directly from the executable step check.
public export
buildValidatedImageStepObservableBoundary
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ImageObservableBoundary (processImageValidated ctx evt).ctx)
buildValidatedImageStepObservableBoundary ctx evt inv =
  case decImageValidatedStepPreservesObservableBoundary ctx evt of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageValidatedProofStepPreservesObservableBoundary ctx evt inv hpreserve)

||| Native delete-start preserves the image invariant because the native
||| reducer leaves the image context unchanged.
public export
nativeImageDeleteStartPreservesInvariant
  : (ctx : ImageContext)
 -> ImageInvariant ctx
 -> ImageInvariant (processNativeImage ctx ImageDeleteStart).ctx
nativeImageDeleteStartPreservesInvariant ctx inv =
  rewrite processNativeImageDeleteStartCtx ctx in inv

||| Native delete-done preserves the image invariant because the native
||| reducer leaves the image context unchanged.
public export
nativeImageDeleteDonePreservesInvariant
  : (ctx : ImageContext)
 -> ImageInvariant ctx
 -> ImageInvariant (processNativeImage ctx ImageDeleteDone).ctx
nativeImageDeleteDonePreservesInvariant ctx inv =
  rewrite processNativeImageDeleteDoneCtx ctx in inv

||| Validated delete-start preserves the image invariant because the validated
||| reducer leaves the image context unchanged.
public export
validatedImageDeleteStartPreservesInvariant
  : (ctx : ImageContext)
 -> ImageInvariant ctx
 -> ImageInvariant (processImageValidated ctx VDeleteStart).ctx
validatedImageDeleteStartPreservesInvariant ctx inv =
  rewrite processImageValidatedDeleteStartCtx ctx in inv

||| Validated delete-done preserves the image invariant because the validated
||| reducer leaves the image context unchanged.
public export
validatedImageDeleteDonePreservesInvariant
  : (ctx : ImageContext)
 -> ImageInvariant ctx
 -> ImageInvariant (processImageValidated ctx VDeleteDone).ctx
validatedImageDeleteDonePreservesInvariant ctx inv =
  rewrite processImageValidatedDeleteDoneCtx ctx in inv

||| Native delete-start preserves the semantic boundary because the native
||| reducer leaves the image context unchanged.
public export
nativeImageDeleteStartPreservesSemanticBoundary
  : (ctx : ImageContext)
 -> ImageSemanticBoundary ctx
 -> ImageSemanticBoundary (processNativeImage ctx ImageDeleteStart).ctx
nativeImageDeleteStartPreservesSemanticBoundary ctx inv =
  rewrite processNativeImageDeleteStartCtx ctx in inv

||| Native delete-done preserves the semantic boundary because the native
||| reducer leaves the image context unchanged.
public export
nativeImageDeleteDonePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> ImageSemanticBoundary ctx
 -> ImageSemanticBoundary (processNativeImage ctx ImageDeleteDone).ctx
nativeImageDeleteDonePreservesSemanticBoundary ctx inv =
  rewrite processNativeImageDeleteDoneCtx ctx in inv

||| Validated delete-start preserves the semantic boundary because the
||| validated reducer leaves the image context unchanged.
public export
validatedImageDeleteStartPreservesSemanticBoundary
  : (ctx : ImageContext)
 -> ImageSemanticBoundary ctx
 -> ImageSemanticBoundary (processImageValidated ctx VDeleteStart).ctx
validatedImageDeleteStartPreservesSemanticBoundary ctx inv =
  rewrite processImageValidatedDeleteStartCtx ctx in inv

||| Validated delete-done preserves the semantic boundary because the
||| validated reducer leaves the image context unchanged.
public export
validatedImageDeleteDonePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> ImageSemanticBoundary ctx
 -> ImageSemanticBoundary (processImageValidated ctx VDeleteDone).ctx
validatedImageDeleteDonePreservesSemanticBoundary ctx inv =
  rewrite processImageValidatedDeleteDoneCtx ctx in inv

||| Native delete-start preserves the reduced observable boundary because the
||| native reducer leaves the image context unchanged.
public export
nativeImageDeleteStartPreservesObservableBoundary
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ImageObservableBoundary (processNativeImage ctx ImageDeleteStart).ctx
nativeImageDeleteStartPreservesObservableBoundary ctx obs =
  rewrite processNativeImageDeleteStartCtx ctx in obs

||| Native delete-done preserves the reduced observable boundary because the
||| native reducer leaves the image context unchanged.
public export
nativeImageDeleteDonePreservesObservableBoundary
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ImageObservableBoundary (processNativeImage ctx ImageDeleteDone).ctx
nativeImageDeleteDonePreservesObservableBoundary ctx obs =
  rewrite processNativeImageDeleteDoneCtx ctx in obs

||| Validated delete-start preserves the reduced observable boundary because
||| the validated reducer leaves the image context unchanged.
public export
validatedImageDeleteStartPreservesObservableBoundary
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ImageObservableBoundary (processImageValidated ctx VDeleteStart).ctx
validatedImageDeleteStartPreservesObservableBoundary ctx obs =
  rewrite processImageValidatedDeleteStartCtx ctx in obs

||| Validated delete-done preserves the reduced observable boundary because
||| the validated reducer leaves the image context unchanged.
public export
validatedImageDeleteDonePreservesObservableBoundary
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ImageObservableBoundary (processImageValidated ctx VDeleteDone).ctx
validatedImageDeleteDonePreservesObservableBoundary ctx obs =
  rewrite processImageValidatedDeleteDoneCtx ctx in obs

||| A context satisfying the reduced observable boundary yields a direct safety
||| proof for its reduced observable state.
public export
imageObservableBoundaryStateSafe
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> observableImageStateSafe (observeImageState ctx) = True
imageObservableBoundaryStateSafe
  (MkImageCtx pgid whoami epoch acting up pool coreState bookState)
  (MkImageObservableBoundary obsSafe) =
  let expandedSafe =
        replace {p = \rhs => rhs = True}
                (contextObservableStateSafeOnCtor pgid whoami epoch acting up
                                                  pool coreState bookState)
                obsSafe
  in replace {p = \rhs => observableImageStateSafe rhs = True}
             (sym (observeImageStateOnCtor pgid whoami epoch acting up pool
                                           coreState bookState))
             expandedSafe

||| Any smaller proof-facing snapshot that refines a context on the reduced
||| observable boundary inherits the same observable safety.
public export
observedObservableSnapshotBoundaryFromRefines
  : (snap : ObservableImageSnapshot)
 -> (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ObservableSnapshotRefines snap ctx
 -> ObservedObservableSnapshotBoundary snap
observedObservableSnapshotBoundaryFromRefines
    (MkObservableImageSnapshot proofPgid proofWhoami proofEpoch proofActing proofUp proofPool
                               proofLocalInfo proofPeerImages proofAuthImage
                               proofPeerRecoveryPlans proofLocalRecoveryPlan
                               proofActivated)
    (MkImageCtx ctxPgid ctxWhoami ctxEpoch ctxActing ctxUp ctxPool
                ctxCore ctxBook)
    (MkImageObservableBoundary obsSafe)
    (MkObservableSnapshotRefines pgidOk whoamiOk epochOk actingOk upOk poolOk localOk peerOk
                                 authOk peerPlanOk localPlanOk activatedOk) =
  MkObservedObservableSnapshotBoundary $
       rewrite observableSnapshotStateOnCtor proofPgid proofWhoami proofEpoch proofActing proofUp
                                             proofPool proofLocalInfo
                                             proofPeerImages proofAuthImage
                                             proofPeerRecoveryPlans
                                             proofLocalRecoveryPlan
                                             proofActivated in
       rewrite pgidOk in
       rewrite whoamiOk in
       rewrite epochOk in
       rewrite actingOk in
       rewrite upOk in
       rewrite poolOk in
       rewrite localOk in
       rewrite peerOk in
       rewrite authOk in
       rewrite peerPlanOk in
       rewrite localPlanOk in
       rewrite activatedOk in
         replace {p = \rhs => rhs = True}
                 (contextObservableStateSafeOnCtor ctxPgid ctxWhoami ctxEpoch
                                                  ctxActing ctxUp ctxPool
                                                  ctxCore ctxBook)
                 obsSafe

||| A self-generated smaller proof-facing snapshot from a context satisfying
||| the reduced observable boundary is itself observably safe.
public export
observedObservableSnapshotBoundary
  : (ctx : ImageContext)
 -> ImageObservableBoundary ctx
 -> ObservedObservableSnapshotBoundary (observableSnapshotOfContext ctx)
observedObservableSnapshotBoundary ctx obs =
  observedObservableSnapshotBoundaryFromRefines (observableSnapshotOfContext ctx)
                                               ctx
                                               obs
                                               (observableSnapshotOfContextRefines ctx)

||| One native image step produces an observably safe smaller proof-facing
||| snapshot provided the reduced observable boundary is preserved.
public export
observedObservableStepProducesSafeSelfSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> ImageObservableBoundary ctx
 -> ImageStepPreservesObservableBoundary ctx evt
 -> ObservedObservableSnapshotBoundary
      (observableSnapshotOfContext (processNativeImage ctx evt).ctx)
observedObservableStepProducesSafeSelfSnapshot ctx evt obs hpreserve =
  let nextObs = imageProofStepPreservesObservableBoundary ctx evt obs hpreserve
  in observedObservableSnapshotBoundary ((processNativeImage ctx evt).ctx) nextObs

||| One validated image step produces an observably safe smaller proof-facing
||| snapshot provided the reduced observable boundary is preserved.
public export
observedValidatedObservableStepProducesSafeSelfSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> ImageValidatedStepPreservesObservableBoundary ctx evt
 -> ObservedObservableSnapshotBoundary
      (observableSnapshotOfContext (processImageValidated ctx evt).ctx)
observedValidatedObservableStepProducesSafeSelfSnapshot ctx evt obs hpreserve =
  let nextObs = imageValidatedProofStepPreservesObservableBoundary ctx evt obs hpreserve
  in observedObservableSnapshotBoundary ((processImageValidated ctx evt).ctx) nextObs

||| Once the reduced observable boundary is preserved, any smaller proof-facing
||| snapshot that simulates the native step is observably safe.
public export
observedObservableSimulationProducesSafeSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> (snap : ObservableImageSnapshot)
 -> ImageObservableBoundary ctx
 -> ImageStepPreservesObservableBoundary ctx evt
 -> ObservableProofSnapshotCppStepSimulates ctx evt snap
 -> ObservedObservableSnapshotBoundary snap
observedObservableSimulationProducesSafeSnapshot ctx evt snap obs hpreserve sim =
  case sim of
    ObservableProofSnapshotAdvances hrefines =>
      let nextObs = imageProofStepPreservesObservableBoundary ctx evt obs hpreserve
      in observedObservableSnapshotBoundaryFromRefines snap
                                                     ((processNativeImage ctx evt).ctx)
                                                     nextObs
                                                     hrefines
    ObservableProofSnapshotStutters hstutter =>
      let currentSafe = imageObservableBoundaryStateSafe ctx obs
      in MkObservedObservableSnapshotBoundary $
           replace {p = \rhs => observableImageStateSafe rhs = True}
                   (sym hstutter)
                   currentSafe

||| Validated-path version of the smaller simulated-snapshot safety theorem.
public export
observedValidatedObservableSimulationProducesSafeSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> (snap : ObservableImageSnapshot)
 -> ImageObservableBoundary ctx
 -> ImageValidatedStepPreservesObservableBoundary ctx evt
 -> ObservableValidatedProofSnapshotCppStepSimulates ctx evt snap
 -> ObservedObservableSnapshotBoundary snap
observedValidatedObservableSimulationProducesSafeSnapshot ctx evt snap obs hpreserve sim =
  case sim of
    ObservableValidatedProofSnapshotAdvances hrefines =>
      let nextObs = imageValidatedProofStepPreservesObservableBoundary ctx evt obs hpreserve
      in observedObservableSnapshotBoundaryFromRefines snap
                                                     ((processImageValidated ctx evt).ctx)
                                                     nextObs
                                                     hrefines
    ObservableValidatedProofSnapshotStutters hstutter =>
      let currentSafe = imageObservableBoundaryStateSafe ctx obs
      in MkObservedObservableSnapshotBoundary $
           replace {p = \rhs => observableImageStateSafe rhs = True}
                   (sym hstutter)
                   currentSafe

||| Safe-snapshot production remains the next proof obligation after observable
||| boundary preservation and step simulation are established for full replay
||| snapshots; the smaller proof-facing snapshot path now has the corresponding
||| theorem.

||| A full replay-snapshot safety witness projects to the smaller proof-facing
||| snapshot safety witness.
public export
observedImageBoundaryProjectsToObservableSnapshotBoundary
  : {snap : ImageObservedSnapshot}
 -> ObservedImageBoundary snap
 -> ObservedObservableSnapshotBoundary (observableSnapshotOfObserved snap)
observedImageBoundaryProjectsToObservableSnapshotBoundary
  {snap} (MkObservedImageBoundary hsafe) =
  MkObservedObservableSnapshotBoundary $
    replace {p = \rhs => observableImageStateSafe rhs = True}
            (observedSnapshotProjectsToProofSnapshot snap)
            hsafe

||| The smaller proof-facing snapshot safety witness lifts back to the full
||| replay snapshot surface because both project to the same observable state.
public export
observedObservableSnapshotBoundaryProjectsToImageBoundary
  : {snap : ImageObservedSnapshot}
 -> ObservedObservableSnapshotBoundary (observableSnapshotOfObserved snap)
 -> ObservedImageBoundary snap
observedObservableSnapshotBoundaryProjectsToImageBoundary
  {snap} (MkObservedObservableSnapshotBoundary hsafe) =
  MkObservedImageBoundary $
    replace {p = \rhs => observableImageStateSafe rhs = True}
            (sym (observedSnapshotProjectsToProofSnapshot snap))
            hsafe

||| Finished one-step refinement theorem for the full replay snapshot surface.
||| If the current context satisfies the reduced observable boundary, that
||| boundary is preserved by the Idris step, and the emitted replay snapshot
||| simulates the step, then the emitted replay snapshot is observably safe.
public export
observedImageSimulationProducesSafeSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageEvent)
 -> (snap : ImageObservedSnapshot)
 -> ImageObservableBoundary ctx
 -> ImageStepPreservesObservableBoundary ctx evt
 -> ObservableImageCppStepSimulates ctx evt snap
 -> ObservedImageBoundary snap
observedImageSimulationProducesSafeSnapshot ctx evt snap obs hpreserve sim =
  let projectedSim =
        observableImageSimulationProjectsToProofSnapshot sim
      projectedSafe =
        observedObservableSimulationProducesSafeSnapshot ctx
                                                        evt
                                                        (observableSnapshotOfObserved snap)
                                                        obs
                                                        hpreserve
                                                        projectedSim
  in observedObservableSnapshotBoundaryProjectsToImageBoundary projectedSafe

||| Validated-path finished one-step refinement theorem for the full replay
||| snapshot surface.
public export
observedValidatedImageSimulationProducesSafeSnapshot
  : (ctx : ImageContext)
 -> (evt : ImageValidatedEvent)
 -> (snap : ImageObservedSnapshot)
 -> ImageObservableBoundary ctx
 -> ImageValidatedStepPreservesObservableBoundary ctx evt
 -> ObservableValidatedImageCppStepSimulates ctx evt snap
 -> ObservedImageBoundary snap
observedValidatedImageSimulationProducesSafeSnapshot ctx evt snap obs hpreserve sim =
  let projectedSim =
        observableValidatedImageSimulationProjectsToProofSnapshot sim
      projectedSafe =
        observedValidatedObservableSimulationProducesSafeSnapshot
          ctx
          evt
          (observableSnapshotOfObserved snap)
          obs
          hpreserve
          projectedSim
  in observedObservableSnapshotBoundaryProjectsToImageBoundary projectedSafe

||| Typed trace refinement theorem for the smaller proof-facing snapshot
||| surface. If the observable boundary is preserved along the Idris trace and
||| each emitted snapshot simulates the corresponding step, then every emitted
||| proof-facing snapshot is observably safe.
public export
observedObservableTraceSimulationProducesSafeSnapshots
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageTracePreservesObservableBoundary ctx (proofSnapshotTraceEvents trace)
 -> ObservedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> ObservedObservableSnapshotTraceSafe trace
observedObservableTraceSimulationProducesSafeSnapshots ctx trace obs hpreserve hsim =
  case trace of
    [] =>
      case hpreserve of
        TracePreservesNil =>
          case hsim of
            ObservedObservableSnapshotTraceNil =>
              ObservedObservableSnapshotTraceSafeNil
    ((evt, snap) :: rest) =>
      case hpreserve of
        TracePreservesCons hstep htail =>
          case hsim of
            ObservedObservableSnapshotTraceCons hsimHead hsimTail =>
              let headSafe =
                    observedObservableSimulationProducesSafeSnapshot ctx
                                                                    evt
                                                                    snap
                                                                    obs
                                                                    hstep
                                                                    hsimHead
                  nextObs =
                    imageProofStepPreservesObservableBoundary ctx evt obs hstep
                  tailSafe =
                    observedObservableTraceSimulationProducesSafeSnapshots
                      ((processNativeImage ctx evt).ctx)
                      rest
                      nextObs
                      htail
                      hsimTail
              in ObservedObservableSnapshotTraceSafeCons headSafe tailSafe

||| Validated-path typed trace refinement theorem for the smaller proof-facing
||| snapshot surface.
public export
observedValidatedObservableTraceSimulationProducesSafeSnapshots
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageValidatedTracePreservesObservableBoundary ctx (validatedProofSnapshotTraceEvents trace)
 -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> ObservedValidatedObservableSnapshotTraceSafe trace
observedValidatedObservableTraceSimulationProducesSafeSnapshots
  ctx
  trace
  obs
  hpreserve
  hsim =
    case trace of
      [] =>
        case hpreserve of
          TracePreservesNil =>
            case hsim of
              ObservedValidatedObservableSnapshotTraceNil =>
                ObservedValidatedObservableSnapshotTraceSafeNil
      ((evt, snap) :: rest) =>
        case hpreserve of
          TracePreservesCons hstep htail =>
            case hsim of
              ObservedValidatedObservableSnapshotTraceCons hsimHead hsimTail =>
                let headSafe =
                      observedValidatedObservableSimulationProducesSafeSnapshot
                        ctx
                        evt
                        snap
                        obs
                        hstep
                        hsimHead
                    nextObs =
                      imageValidatedProofStepPreservesObservableBoundary ctx evt obs hstep
                    tailSafe =
                      observedValidatedObservableTraceSimulationProducesSafeSnapshots
                        ((processImageValidated ctx evt).ctx)
                        rest
                        nextObs
                        htail
                        hsimTail
                in ObservedValidatedObservableSnapshotTraceSafeCons headSafe tailSafe

||| Lift semantic proof-trace safety back to the corresponding replay/debug
||| trace once replay snapshots have been projected onto the proof surface.
public export
observedSemanticTraceSafeProjectsToReplayTraceSafe
  : {trace : List (ImageEvent, ImageReplaySnapshot)}
 -> ObservedObservableSnapshotTraceSafe (semanticSnapshotTraceOfReplayTrace trace)
 -> ObservedImageTraceSafe trace
observedSemanticTraceSafeProjectsToReplayTraceSafe
  {trace = []}
  ObservedObservableSnapshotTraceSafeNil =
    ObservedImageTraceSafeNil
observedSemanticTraceSafeProjectsToReplayTraceSafe
  {trace = (evt, snap) :: rest}
  (ObservedObservableSnapshotTraceSafeCons headSafe tailSafe) =
    ObservedImageTraceSafeCons
      (observedObservableSnapshotBoundaryProjectsToImageBoundary {snap} headSafe)
      (observedSemanticTraceSafeProjectsToReplayTraceSafe {trace = rest} tailSafe)

||| Validated-path lift from semantic proof-trace safety back to the replay
||| snapshot surface.
public export
observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
  : {trace : List (ImageValidatedEvent, ImageReplaySnapshot)}
 -> ObservedValidatedObservableSnapshotTraceSafe
      (validatedSemanticSnapshotTraceOfReplayTrace trace)
 -> ObservedValidatedImageTraceSafe trace
observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
  {trace = []}
  ObservedValidatedObservableSnapshotTraceSafeNil =
    ObservedValidatedImageTraceSafeNil
observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
  {trace = (evt, snap) :: rest}
  (ObservedValidatedObservableSnapshotTraceSafeCons headSafe tailSafe) =
    ObservedValidatedImageTraceSafeCons
      (observedObservableSnapshotBoundaryProjectsToImageBoundary {snap} headSafe)
      (observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
         {trace = rest}
         tailSafe)

||| Typed trace refinement theorem on the full replay snapshot surface.
||| This is the external replay-facing analogue of the smaller proof-facing
||| theorem above.
public export
observedImageTraceSimulationProducesSafeSnapshots
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageTracePreservesObservableBoundary ctx (observedImageTraceEvents trace)
 -> ObservedImageTraceSimulates ctx trace
 -> ObservedImageTraceSafe trace
observedImageTraceSimulationProducesSafeSnapshots ctx trace obs hpreserve hsim =
  let semanticPreserve =
        replace
          {p = \evts => ImageTracePreservesObservableBoundary ctx evts}
          (sym (semanticSnapshotReplayTraceEvents trace))
          hpreserve
      semanticSim =
        observedImageTraceSimulatesProjectsToSemanticTrace hsim
      semanticSafe =
        observedObservableTraceSimulationProducesSafeSnapshots
          ctx
          (semanticSnapshotTraceOfReplayTrace trace)
          obs
          semanticPreserve
          semanticSim
  in observedSemanticTraceSafeProjectsToReplayTraceSafe
       {trace}
       semanticSafe

||| Validated-path typed trace refinement theorem on the full replay snapshot
||| surface.
public export
observedValidatedImageTraceSimulationProducesSafeSnapshots
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageValidatedTracePreservesObservableBoundary ctx (validatedObservedImageTraceEvents trace)
 -> ObservedValidatedImageTraceSimulates ctx trace
 -> ObservedValidatedImageTraceSafe trace
observedValidatedImageTraceSimulationProducesSafeSnapshots
  ctx
  trace
  obs
  hpreserve
  hsim =
    let semanticPreserve =
          replace
            {p = \evts => ImageValidatedTracePreservesObservableBoundary ctx evts}
            (sym (validatedSemanticSnapshotReplayTraceEvents trace))
            hpreserve
        semanticSim =
          observedValidatedImageTraceSimulatesProjectsToSemanticTrace hsim
        semanticSafe =
          observedValidatedObservableTraceSimulationProducesSafeSnapshots
            ctx
            (validatedSemanticSnapshotTraceOfReplayTrace trace)
            obs
            semanticPreserve
            semanticSim
    in observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
         {trace}
         semanticSafe

||| Inductive preservation theorem for image traces.
public export
imageProofTracePreservesInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageInvariant ctx
 -> ImageTracePreservesInvariant ctx evts
 -> ImageInvariant (processNativeImageTrace ctx evts)
imageProofTracePreservesInvariant ctx [] inv TracePreservesNil =
  rewrite processNativeImageTraceNil ctx in inv
imageProofTracePreservesInvariant ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageProofStepPreservesInvariant ctx evt inv hstep
  in rewrite processNativeImageTraceCons ctx evt evts in
       imageProofTracePreservesInvariant (processNativeImage ctx evt).ctx evts nextInv htail

||| Inductive preservation theorem for validated image traces.
public export
imageValidatedProofTracePreservesInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageInvariant ctx
 -> ImageValidatedTracePreservesInvariant ctx evts
 -> ImageInvariant (processImageValidatedTrace ctx evts)
imageValidatedProofTracePreservesInvariant ctx [] inv TracePreservesNil =
  rewrite processImageValidatedTraceNil ctx in inv
imageValidatedProofTracePreservesInvariant ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageValidatedProofStepPreservesInvariant ctx evt inv hstep
  in rewrite processImageValidatedTraceCons ctx evt evts in
       imageValidatedProofTracePreservesInvariant (processImageValidated ctx evt).ctx evts nextInv htail

||| Build the native invariant-preservation theorem directly from the
||| executable step checks.
public export
buildImageTraceInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageInvariant ctx
 -> Maybe (ImageInvariant (processNativeImageTrace ctx evts))
buildImageTraceInvariant ctx evts inv =
  case decImageTracePreservesInvariant ctx evts of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageProofTracePreservesInvariant ctx evts inv hpreserve)

||| Build the validated invariant-preservation theorem directly from the
||| executable step checks.
public export
buildValidatedImageTraceInvariant
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageInvariant ctx
 -> Maybe (ImageInvariant (processImageValidatedTrace ctx evts))
buildValidatedImageTraceInvariant ctx evts inv =
  case decImageValidatedTracePreservesInvariant ctx evts of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageValidatedProofTracePreservesInvariant ctx evts inv hpreserve)

||| Inductive preservation theorem for the reduced semantic boundary.
public export
imageProofTracePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageSemanticBoundary ctx
 -> ImageTracePreservesSemanticBoundary ctx evts
 -> ImageSemanticBoundary (processNativeImageTrace ctx evts)
imageProofTracePreservesSemanticBoundary ctx [] inv TracePreservesNil =
  rewrite processNativeImageTraceNil ctx in inv
imageProofTracePreservesSemanticBoundary ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageProofStepPreservesSemanticBoundary ctx evt inv hstep
  in rewrite processNativeImageTraceCons ctx evt evts in
       imageProofTracePreservesSemanticBoundary (processNativeImage ctx evt).ctx evts nextInv htail

||| Inductive preservation theorem for the reduced semantic boundary on the
||| validated reducer path.
public export
imageValidatedProofTracePreservesSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageSemanticBoundary ctx
 -> ImageValidatedTracePreservesSemanticBoundary ctx evts
 -> ImageSemanticBoundary (processImageValidatedTrace ctx evts)
imageValidatedProofTracePreservesSemanticBoundary ctx [] inv TracePreservesNil =
  rewrite processImageValidatedTraceNil ctx in inv
imageValidatedProofTracePreservesSemanticBoundary ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageValidatedProofStepPreservesSemanticBoundary ctx evt inv hstep
  in rewrite processImageValidatedTraceCons ctx evt evts in
       imageValidatedProofTracePreservesSemanticBoundary (processImageValidated ctx evt).ctx evts nextInv htail

||| Build the native semantic-boundary-preservation theorem directly from the
||| executable step checks.
public export
buildImageTraceSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageSemanticBoundary ctx
 -> Maybe (ImageSemanticBoundary (processNativeImageTrace ctx evts))
buildImageTraceSemanticBoundary ctx evts inv =
  case decImageTracePreservesSemanticBoundary ctx evts of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageProofTracePreservesSemanticBoundary ctx evts inv hpreserve)

||| Build the validated semantic-boundary-preservation theorem directly from
||| the executable step checks.
public export
buildValidatedImageTraceSemanticBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageSemanticBoundary ctx
 -> Maybe (ImageSemanticBoundary (processImageValidatedTrace ctx evts))
buildValidatedImageTraceSemanticBoundary ctx evts inv =
  case decImageValidatedTracePreservesSemanticBoundary ctx evts of
    No _ => Nothing
    Yes hpreserve =>
      Just (imageValidatedProofTracePreservesSemanticBoundary ctx evts inv hpreserve)

||| Inductive preservation theorem for the reduced observable boundary alone.
public export
imageProofTracePreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageObservableBoundary ctx
 -> ImageTracePreservesObservableBoundary ctx evts
 -> ImageObservableBoundary (processNativeImageTrace ctx evts)
imageProofTracePreservesObservableBoundary ctx [] inv TracePreservesNil =
  rewrite processNativeImageTraceNil ctx in inv
imageProofTracePreservesObservableBoundary ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageProofStepPreservesObservableBoundary ctx evt inv hstep
  in rewrite processNativeImageTraceCons ctx evt evts in
       imageProofTracePreservesObservableBoundary (processNativeImage ctx evt).ctx evts nextInv htail

||| Inductive preservation theorem for the reduced observable boundary on the
||| validated reducer path.
public export
imageValidatedProofTracePreservesObservableBoundary
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> ImageValidatedTracePreservesObservableBoundary ctx evts
 -> ImageObservableBoundary (processImageValidatedTrace ctx evts)
imageValidatedProofTracePreservesObservableBoundary ctx [] inv TracePreservesNil =
  rewrite processImageValidatedTraceNil ctx in inv
imageValidatedProofTracePreservesObservableBoundary ctx (evt :: evts) inv (TracePreservesCons hstep htail) =
  let nextInv = imageValidatedProofStepPreservesObservableBoundary ctx evt inv hstep
  in rewrite processImageValidatedTraceCons ctx evt evts in
       imageValidatedProofTracePreservesObservableBoundary (processImageValidated ctx evt).ctx evts nextInv htail

||| Final typed trace refinement theorem for the smaller proof-facing snapshot
||| surface on the native event path.
public export
observedObservableSnapshotTraceRefinesExecution
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageTracePreservesObservableBoundary ctx (proofSnapshotTraceEvents trace)
 -> ObservedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> ObservedObservableSnapshotTraceRefinement ctx trace
observedObservableSnapshotTraceRefinesExecution ctx trace obs hpreserve hsim =
  let finalBoundary =
        imageProofTracePreservesObservableBoundary ctx
                                                  (proofSnapshotTraceEvents trace)
                                                  obs
                                                  hpreserve
      emittedSafe =
        observedObservableTraceSimulationProducesSafeSnapshots ctx
                                                              trace
                                                              obs
                                                              hpreserve
                                                              hsim
  in MkObservedObservableSnapshotTraceRefinement finalBoundary emittedSafe

||| Final typed trace refinement theorem for the smaller proof-facing snapshot
||| surface on the validated event path.
public export
observedValidatedObservableSnapshotTraceRefinesExecution
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageValidatedTracePreservesObservableBoundary ctx (validatedProofSnapshotTraceEvents trace)
 -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> ObservedValidatedObservableSnapshotTraceRefinement ctx trace
observedValidatedObservableSnapshotTraceRefinesExecution ctx trace obs hpreserve hsim =
  let finalBoundary =
        imageValidatedProofTracePreservesObservableBoundary
          ctx
          (validatedProofSnapshotTraceEvents trace)
          obs
          hpreserve
      emittedSafe =
        observedValidatedObservableTraceSimulationProducesSafeSnapshots
          ctx
          trace
          obs
          hpreserve
          hsim
  in MkObservedValidatedObservableSnapshotTraceRefinement
       finalBoundary
       emittedSafe

||| Final typed replay/execution refinement theorem on the full replay
||| snapshot surface for native image-event traces.
public export
observedImageTraceRefinesExecution
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageTracePreservesObservableBoundary ctx (observedImageTraceEvents trace)
 -> ObservedImageTraceSimulates ctx trace
 -> ObservedImageTraceRefinement ctx trace
observedImageTraceRefinesExecution ctx trace obs hpreserve hsim =
  let semanticPreserve =
        replace
          {p = \evts => ImageTracePreservesObservableBoundary ctx evts}
          (sym (semanticSnapshotReplayTraceEvents trace))
          hpreserve
      semanticSim =
        observedImageTraceSimulatesProjectsToSemanticTrace hsim
      semanticRefinement =
        observedObservableSnapshotTraceRefinesExecution
          ctx
          (semanticSnapshotTraceOfReplayTrace trace)
          obs
          semanticPreserve
          semanticSim
      finalBoundary =
        replace
          {p = \evts => ImageObservableBoundary (processNativeImageTrace ctx evts)}
          (semanticSnapshotReplayTraceEvents trace)
          semanticRefinement.finalBoundary
      emittedSafe =
        observedSemanticTraceSafeProjectsToReplayTraceSafe
          {trace}
          semanticRefinement.emittedSnapshotsSafe
  in MkObservedImageTraceRefinement finalBoundary emittedSafe

||| Final typed replay/execution refinement theorem on the full replay
||| snapshot surface for validated image-event traces.
public export
observedValidatedImageTraceRefinesExecution
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ImageValidatedTracePreservesObservableBoundary ctx (validatedObservedImageTraceEvents trace)
 -> ObservedValidatedImageTraceSimulates ctx trace
 -> ObservedValidatedImageTraceRefinement ctx trace
observedValidatedImageTraceRefinesExecution ctx trace obs hpreserve hsim =
  let semanticPreserve =
        replace
          {p = \evts => ImageValidatedTracePreservesObservableBoundary ctx evts}
          (sym (validatedSemanticSnapshotReplayTraceEvents trace))
          hpreserve
      semanticSim =
        observedValidatedImageTraceSimulatesProjectsToSemanticTrace hsim
      semanticRefinement =
        observedValidatedObservableSnapshotTraceRefinesExecution
          ctx
          (validatedSemanticSnapshotTraceOfReplayTrace trace)
          obs
          semanticPreserve
          semanticSim
      finalBoundary =
        replace
          {p = \evts => ImageObservableBoundary (processImageValidatedTrace ctx evts)}
          (validatedSemanticSnapshotReplayTraceEvents trace)
          semanticRefinement.validatedFinalBoundary
      emittedSafe =
        observedValidatedSemanticTraceSafeProjectsToReplayTraceSafe
          {trace}
          semanticRefinement.validatedEmittedSnapshotsSafe
  in MkObservedValidatedImageTraceRefinement finalBoundary emittedSafe

||| Build the native proof-facing trace-refinement theorem directly from the
||| executable observable-boundary preservation checks.
public export
buildObservedObservableSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ObservedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> Maybe (ObservedObservableSnapshotTraceRefinement ctx trace)
buildObservedObservableSnapshotTraceRefinement ctx trace obs hsim =
  case decImageTracePreservesObservableBoundary ctx (proofSnapshotTraceEvents trace) of
    No _ => Nothing
    Yes hpreserve =>
      Just (observedObservableSnapshotTraceRefinesExecution
              ctx
              trace
              obs
              hpreserve
              hsim)

||| Build the validated proof-facing trace-refinement theorem directly from the
||| executable observable-boundary preservation checks.
public export
buildObservedValidatedObservableSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ObservableImageSnapshot))
 -> ImageObservableBoundary ctx
 -> ObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx trace
 -> Maybe (ObservedValidatedObservableSnapshotTraceRefinement ctx trace)
buildObservedValidatedObservableSnapshotTraceRefinement ctx trace obs hsim =
  case decImageValidatedTracePreservesObservableBoundary
         ctx
         (validatedProofSnapshotTraceEvents trace) of
    No _ => Nothing
    Yes hpreserve =>
      Just (observedValidatedObservableSnapshotTraceRefinesExecution
              ctx
              trace
              obs
              hpreserve
              hsim)

||| Build the native full replay trace-refinement theorem directly from the
||| executable observable-boundary preservation checks.
public export
buildObservedImageTraceRefinement
  : (ctx : ImageContext)
 -> (trace : List (ImageEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ObservedImageTraceSimulates ctx trace
 -> Maybe (ObservedImageTraceRefinement ctx trace)
buildObservedImageTraceRefinement ctx trace obs hsim =
  case decImageTracePreservesObservableBoundary ctx (observedImageTraceEvents trace) of
    No _ => Nothing
    Yes hpreserve =>
      Just (observedImageTraceRefinesExecution
              ctx
              trace
              obs
              hpreserve
              hsim)

||| Build the validated full replay trace-refinement theorem directly from the
||| executable observable-boundary preservation checks.
public export
buildObservedValidatedImageTraceRefinement
  : (ctx : ImageContext)
 -> (trace : List (ImageValidatedEvent, ImageObservedSnapshot))
 -> ImageObservableBoundary ctx
 -> ObservedValidatedImageTraceSimulates ctx trace
 -> Maybe (ObservedValidatedImageTraceRefinement ctx trace)
buildObservedValidatedImageTraceRefinement ctx trace obs hsim =
  case decImageValidatedTracePreservesObservableBoundary
         ctx
         (validatedObservedImageTraceEvents trace) of
    No _ => Nothing
    Yes hpreserve =>
      Just (observedValidatedImageTraceRefinesExecution
              ctx
              trace
              obs
              hpreserve
              hsim)

||| Build the native proof-facing trace-refinement theorem for the reducer's
||| own emitted snapshots.
public export
buildSelfObservedObservableSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedObservableSnapshotTraceRefinement
             ctx
             (proofSnapshotTraceOf ctx evts))
buildSelfObservedObservableSnapshotTraceRefinement ctx evts obs =
  buildObservedObservableSnapshotTraceRefinement
    ctx
    (proofSnapshotTraceOf ctx evts)
    obs
    (selfObservedObservableSnapshotTraceRefinesSemanticBoundary ctx evts)

||| Build the native semantic proof-trace refinement theorem for the
||| reducer's own emitted semantic snapshots.
public export
buildSelfObservedSemanticSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedSemanticSnapshotTraceRefinement
             ctx
             (semanticSnapshotTraceOf ctx evts))
buildSelfObservedSemanticSnapshotTraceRefinement =
  buildSelfObservedObservableSnapshotTraceRefinement

||| Build the validated proof-facing trace-refinement theorem for the
||| reducer's own emitted snapshots.
public export
buildSelfObservedValidatedObservableSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedValidatedObservableSnapshotTraceRefinement
             ctx
             (validatedProofSnapshotTraceOf ctx evts))
buildSelfObservedValidatedObservableSnapshotTraceRefinement ctx evts obs =
  buildObservedValidatedObservableSnapshotTraceRefinement
    ctx
    (validatedProofSnapshotTraceOf ctx evts)
    obs
    (selfObservedValidatedObservableSnapshotTraceRefinesSemanticBoundary ctx evts)

||| Build the validated semantic proof-trace refinement theorem for the
||| reducer's own emitted semantic snapshots.
public export
buildSelfObservedValidatedSemanticSnapshotTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedValidatedSemanticSnapshotTraceRefinement
             ctx
             (validatedSemanticSnapshotTraceOf ctx evts))
buildSelfObservedValidatedSemanticSnapshotTraceRefinement =
  buildSelfObservedValidatedObservableSnapshotTraceRefinement

||| Build the native full replay trace-refinement theorem for the reducer's
||| own emitted snapshots.
public export
buildSelfObservedImageTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedImageTraceRefinement
             ctx
             (observedImageTraceOf ctx evts))
buildSelfObservedImageTraceRefinement ctx evts obs =
  buildObservedImageTraceRefinement
    ctx
    (observedImageTraceOf ctx evts)
    obs
    (selfObservedImageTraceSimulates ctx evts)

||| Build the validated full replay trace-refinement theorem for the reducer's
||| own emitted snapshots.
public export
buildSelfObservedValidatedImageTraceRefinement
  : (ctx : ImageContext)
 -> (evts : List ImageValidatedEvent)
 -> ImageObservableBoundary ctx
 -> Maybe (ObservedValidatedImageTraceRefinement
             ctx
             (validatedObservedImageTraceOf ctx evts))
buildSelfObservedValidatedImageTraceRefinement ctx evts obs =
  buildObservedValidatedImageTraceRefinement
    ctx
    (validatedObservedImageTraceOf ctx evts)
    obs
    (selfObservedValidatedImageTraceSimulates ctx evts)
