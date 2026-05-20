import LeanLCAExactChallenge.Derived.Bounded

/-!
Stable `Dbounded` certificate provider route audit.

This non-product file separates the current ordinary `Dbounded` evidence from the
single-certificate provider interface still needed for a stable infinity-category
claim. It does not construct such a provider.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableDboundedCertificateProviderRouteW126

/-- Whether a currently known declaration is only context, or a real stable projection. -/
inductive ProviderComponent where
  | ordinaryContext
  | stableProjection
  deriving DecidableEq, Repr

/-- A named current candidate and the reason it does or does not provide a stable field. -/
structure OrdinaryCandidate where
  name : String
  component : ProviderComponent
  reason : String

/--
Current evidence available for `Dbounded.infinityCategory C`.

The two Lean fields are real current declarations. The candidate rows record that the
closest finite-limit, finite-colimit, suspension/loop, and pushout/pullback routes are
ordinary-category context, not projections from one stable infinity-category certificate.
-/
structure OrdinaryDboundedProviderContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)
  finiteLimitCandidate : OrdinaryCandidate
  finiteColimitCandidate : OrdinaryCandidate
  suspensionLoopCandidate : OrdinaryCandidate
  pushoutPullbackCandidate : OrdinaryCandidate

/-- The reproducible current ordinary context map found by this provider-route audit. -/
noncomputable def currentOrdinaryContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryDboundedProviderContext C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)
  finiteLimitCandidate :=
    { name := "localized ordinary category zero-object and calculus-of-fractions data"
      component := ProviderComponent.ordinaryContext
      reason := "This is ordinary localized-category structure, not finite limits of a stable quasicategory." }
  finiteColimitCandidate :=
    { name := "localized ordinary category zero-object and biproduct context"
      component := ProviderComponent.ordinaryContext
      reason := "This does not project finite colimits from a stable infinity-category certificate." }
  suspensionLoopCandidate :=
    { name := "ordinary shift, comm-shift, and triangulated localization declarations"
      component := ProviderComponent.ordinaryContext
      reason := "Ordinary shift or triangulated data is not a suspension-loop equivalence projection on `SSet.QCat`." }
  pushoutPullbackCandidate :=
    { name := "ordinary pretriangulated and triangulated localization declarations"
      component := ProviderComponent.ordinaryContext
      reason := "Ordinary triangulated localization does not expose stable pushout-pullback compatibility." }

/--
Single-certificate provider interface required for a stable `Dbounded` route.

All four projections must be obtained from the same `stableCertificate` object. This is
the interface a real provider theorem should target; ordinary nerve evidence alone has no
field of this shape.
-/
structure StableDboundedProviderInterface (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  finiteLimits : stableCertificate → Prop
  finiteColimits : stableCertificate → Prop
  suspensionLoopEquivalence : stableCertificate → Prop
  pushoutPullbackCompatibility : stableCertificate → Prop

/--
Concrete provider-route shape for `Dbounded.infinityCategory C`.

The route may cite current ordinary context, but readiness comes only from the four stable
projections on one certificate.
-/
structure StableDboundedProviderRoute
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  ordinaryContext : OrdinaryDboundedProviderContext C
  providerInterface : StableDboundedProviderInterface (Dbounded.infinityCategory C)
  certificate : providerInterface.stableCertificate
  finiteLimits : providerInterface.finiteLimits certificate
  finiteColimits : providerInterface.finiteColimits certificate
  suspensionLoopEquivalence : providerInterface.suspensionLoopEquivalence certificate
  pushoutPullbackCompatibility :
    providerInterface.pushoutPullbackCompatibility certificate

/-- Product-facing readiness predicate for a real provider route. -/
def StableDboundedProviderRoute.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (route : StableDboundedProviderRoute C) : Prop :=
  route.providerInterface.finiteLimits route.certificate ∧
    route.providerInterface.finiteColimits route.certificate ∧
    route.providerInterface.suspensionLoopEquivalence route.certificate ∧
    route.providerInterface.pushoutPullbackCompatibility route.certificate

/-- A real route is ready exactly by projecting the four fields from its one certificate. -/
theorem StableDboundedProviderRoute.ready_of_route
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (route : StableDboundedProviderRoute C) :
    route.ready := by
  exact ⟨route.finiteLimits, route.finiteColimits, route.suspensionLoopEquivalence,
    route.pushoutPullbackCompatibility⟩

/-- Audit predicate: every current candidate row is ordinary context only. -/
def OrdinaryDboundedProviderContext.allCandidatesAreOrdinaryContext
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (ctx : OrdinaryDboundedProviderContext C) : Prop :=
  ctx.finiteLimitCandidate.component = ProviderComponent.ordinaryContext ∧
    ctx.finiteColimitCandidate.component = ProviderComponent.ordinaryContext ∧
    ctx.suspensionLoopCandidate.component = ProviderComponent.ordinaryContext ∧
    ctx.pushoutPullbackCandidate.component = ProviderComponent.ordinaryContext

/-- The current `Dbounded` candidate map has no row classified as a stable projection. -/
theorem currentOrdinaryContext_allCandidatesAreOrdinaryContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    (currentOrdinaryContext C).allCandidatesAreOrdinaryContext := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The narrow external API still missing: promote ordinary context to a full provider route. -/
abbrev OrdinaryContextToStableProviderRoute
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) :=
  OrdinaryDboundedProviderContext C → StableDboundedProviderRoute C

/--
Search status for this audit: current context is known, but the real stable route is not
supplied by the current project or local mathlib declarations checked by this worker.
-/
structure ProviderRouteSearchState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  ordinaryContext : OrdinaryDboundedProviderContext C
  stableRoute : Option (StableDboundedProviderRoute C)
  missingExternalAPIName : String

/-- Current provider-route search state: ordinary context present, stable route absent. -/
noncomputable def currentProviderRouteSearchState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    ProviderRouteSearchState C where
  ordinaryContext := currentOrdinaryContext C
  stableRoute := none
  missingExternalAPIName := "OrdinaryContextToStableProviderRoute"

/-- This audit found no current stable provider route to extract. -/
theorem currentProviderRoute_not_supplied
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    (currentProviderRouteSearchState C).stableRoute = none := rfl

section Checks

#check ProviderComponent.ordinaryContext
#check ProviderComponent.stableProjection
#check OrdinaryDboundedProviderContext
#check currentOrdinaryContext
#check StableDboundedProviderInterface
#check StableDboundedProviderRoute
#check StableDboundedProviderRoute.ready
#check StableDboundedProviderRoute.ready_of_route
#check OrdinaryDboundedProviderContext.allCandidatesAreOrdinaryContext
#check currentOrdinaryContext_allCandidatesAreOrdinaryContext
#check OrdinaryContextToStableProviderRoute
#check ProviderRouteSearchState
#check currentProviderRouteSearchState
#check currentProviderRoute_not_supplied
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_closed2
#check Triangulated.Localization.pretriangulated
#check Triangulated.Localization.isTriangulated
#check (currentOrdinaryContext (C := MetrizableLCA))
#check (currentProviderRouteSearchState (C := MetrizableLCA))

end Checks

end StableDboundedCertificateProviderRouteW126

end LeanLCAExactChallenge
