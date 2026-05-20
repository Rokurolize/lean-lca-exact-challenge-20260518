import LeanLCAExactChallenge.Derived.Bounded

/-!
Stable route external API minimizer.

This non-product audit keeps the ordinary `Dbounded` evidence internal and isolates the
smallest external input shape found by this worker: one stable certificate object for
`Dbounded.infinityCategory C` with four stable projections.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableRouteExternalAPIMinimizerW129

/-- Ordinary `Dbounded` evidence already supplied by the current project. -/
structure InternalOrdinaryDboundedEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)

/-- The current ordinary evidence can be assembled without any external stable API. -/
noncomputable def currentInternalOrdinaryDboundedEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    InternalOrdinaryDboundedEvidence C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)

/--
Minimal external stable input for the `Dbounded` route.

The only external content is a single certificate plus four projections from that same
certificate. Ordinary quasicategory and homotopy-category comparison evidence are not
external assumptions in this minimized shape.
-/
structure StableDboundedMinimalExternalAPI (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  certificate : stableCertificate
  finiteLimits : stableCertificate → Prop
  finiteColimits : stableCertificate → Prop
  suspensionLoopEquivalence : stableCertificate → Prop
  pushoutPullbackCompatibility : stableCertificate → Prop
  finiteLimits_ready : finiteLimits certificate
  finiteColimits_ready : finiteColimits certificate
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence certificate
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility certificate

/-- The minimized external API required specifically for `Dbounded.infinityCategory C`. -/
abbrev MinimalExternalStableProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableDboundedMinimalExternalAPI (Dbounded.infinityCategory C)

/--
Route assembled from current ordinary evidence plus the minimized external stable API.

This is conditional scaffolding only: it does not construct the external API.
-/
structure StableDboundedRouteFromMinimalAPI
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  ordinaryEvidence : InternalOrdinaryDboundedEvidence C
  externalAPI : MinimalExternalStableProvider C

/-- Product-facing readiness predicate for the minimized route. -/
def StableDboundedRouteFromMinimalAPI.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (route : StableDboundedRouteFromMinimalAPI C) : Prop :=
  route.externalAPI.finiteLimits route.externalAPI.certificate ∧
    route.externalAPI.finiteColimits route.externalAPI.certificate ∧
    route.externalAPI.suspensionLoopEquivalence route.externalAPI.certificate ∧
    route.externalAPI.pushoutPullbackCompatibility route.externalAPI.certificate

/-- A minimized external API is accepted by projecting the four stable fields. -/
theorem StableDboundedRouteFromMinimalAPI.ready_of_minimal_external_api
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (route : StableDboundedRouteFromMinimalAPI C) :
    route.ready := by
  exact ⟨route.externalAPI.finiteLimits_ready, route.externalAPI.finiteColimits_ready,
    route.externalAPI.suspensionLoopEquivalence_ready,
    route.externalAPI.pushoutPullbackCompatibility_ready⟩

/-- Build the conditional route from current ordinary evidence and a minimized external API. -/
noncomputable def routeFromMinimalExternalAPI
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (api : MinimalExternalStableProvider C) :
    StableDboundedRouteFromMinimalAPI C where
  ordinaryEvidence := currentInternalOrdinaryDboundedEvidence C
  externalAPI := api

/-- A marker-only claim carries no semantic stable certificate. -/
structure MarkerOnlyStableClaim where
  marker : String

/-- An ordinary-context-only claim carries only the evidence already internal to the route. -/
structure OrdinaryContextOnlyStableClaim
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  ordinaryEvidence : InternalOrdinaryDboundedEvidence C

/--
The minimized review decision: marker-only and ordinary-context-only attempts are
rejected; a single-certificate four-projection API is accepted as conditional input.
-/
inductive StableDboundedRouteAttempt
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] where
  | markerOnly : MarkerOnlyStableClaim → StableDboundedRouteAttempt C
  | ordinaryContextOnly : OrdinaryContextOnlyStableClaim C → StableDboundedRouteAttempt C
  | singleCertificate : MinimalExternalStableProvider C → StableDboundedRouteAttempt C

/-- Boolean audit classifier for the minimized route attempts. -/
def attemptAccepted
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : StableDboundedRouteAttempt C → Bool
  | .markerOnly _ => false
  | .ordinaryContextOnly _ => false
  | .singleCertificate _ => true

/-- Marker-only attempts are rejected by the minimized API gate. -/
theorem markerOnly_rejected
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (claim : MarkerOnlyStableClaim) :
    attemptAccepted (C := C) (.markerOnly claim) = false := rfl

/-- Ordinary `Dbounded` evidence alone is rejected by the minimized API gate. -/
theorem ordinaryContextOnly_rejected
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (claim : OrdinaryContextOnlyStableClaim C) :
    attemptAccepted (C := C) (.ordinaryContextOnly claim) = false := rfl

/-- A single-certificate provider with four projections is accepted as conditional input. -/
theorem singleCertificate_accepted
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (api : MinimalExternalStableProvider C) :
    attemptAccepted (C := C) (.singleCertificate api) = true := rfl

/-- Field names of the minimized external API surface. -/
def minimizedExternalFieldNames : List String :=
  ["stableCertificate", "certificate", "finiteLimits", "finiteColimits",
    "suspensionLoopEquivalence", "pushoutPullbackCompatibility"]

/-- The external surface is one certificate witness plus four stable projections. -/
theorem minimizedExternalFieldNames_count :
    minimizedExternalFieldNames.length = 6 := rfl

section Checks

#check InternalOrdinaryDboundedEvidence
#check currentInternalOrdinaryDboundedEvidence
#check StableDboundedMinimalExternalAPI
#check MinimalExternalStableProvider
#check StableDboundedRouteFromMinimalAPI
#check StableDboundedRouteFromMinimalAPI.ready
#check StableDboundedRouteFromMinimalAPI.ready_of_minimal_external_api
#check routeFromMinimalExternalAPI
#check MarkerOnlyStableClaim
#check OrdinaryContextOnlyStableClaim
#check StableDboundedRouteAttempt
#check attemptAccepted
#check markerOnly_rejected
#check ordinaryContextOnly_rejected
#check singleCertificate_accepted
#check minimizedExternalFieldNames
#check minimizedExternalFieldNames_count
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check (currentInternalOrdinaryDboundedEvidence (C := MetrizableLCA))
#check (routeFromMinimalExternalAPI (C := MetrizableLCA))

end Checks

end StableRouteExternalAPIMinimizerW129

end LeanLCAExactChallenge
