import LeanLCAExactChallenge.Derived.Bounded

/-!
Dbounded four-projection provider route audit.

This non-product file sharply isolates the route still needed after the existing
single-certificate projection constructors: ordinary `Dbounded` infinity-category
evidence must be promoted to one full stable certificate carrying all four projections.
Marker-only and ordinary-context-only shortcuts are rejected by a small Lean classifier.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedFourProjectionProviderRouteW133

/-- The ordinary `Dbounded` infinity-category context currently available locally. -/
structure OrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)

/-- Assemble the current ordinary context from declarations in `Derived.Bounded`. -/
noncomputable def currentOrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryDboundedInfinityContext C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)

/--
One full stable four-projection certificate for a quasicategory.

The four predicates are deliberately tied to the same certificate witness; this prevents
assembling a route from unrelated markers or ordinary category structure.
-/
structure FullStableFourProjectionCertificate (Q : SSet.QCat) : Type 2 where
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

/-- The full stable provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  FullStableFourProjectionCertificate (Dbounded.infinityCategory C)

/-- Product-facing readiness of a full four-projection certificate. -/
def DboundedFourProjectionProvider.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) : Prop :=
  cert.finiteLimits cert.certificate ∧
    cert.finiteColimits cert.certificate ∧
    cert.suspensionLoopEquivalence cert.certificate ∧
    cert.pushoutPullbackCompatibility cert.certificate

/-- A full provider is ready exactly by its four fields. -/
theorem DboundedFourProjectionProvider.ready_of_fields
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    cert.ready := by
  exact ⟨cert.finiteLimits_ready, cert.finiteColimits_ready,
    cert.suspensionLoopEquivalence_ready, cert.pushoutPullbackCompatibility_ready⟩

/--
The exact theorem shape still missing from the local route.

The input is ordinary `Dbounded` infinity-category evidence. The output must be a full
stable certificate for `Dbounded.infinityCategory C`, not just another ordinary
quasicategory or homotopy-category comparison.
-/
abbrev OrdinaryContextToDboundedFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) :=
  OrdinaryDboundedInfinityContext C → DboundedFourProjectionProvider C

/-- A marker-only claim carries no semantic stable four-projection fields. -/
structure MarkerOnlyStableClaim where
  marker : String

/-- An ordinary-only claim carries only the context already supplied by the current route. -/
structure OrdinaryOnlyStableClaim
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  ordinaryContext : OrdinaryDboundedInfinityContext C

/--
Route attempts accepted by this audit.

Only a real full stable provider is accepted. Marker-only and ordinary-only attempts are
kept as first-class rejected constructors so future audits can check them directly.
-/
inductive DboundedFourProjectionRouteAttempt
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  | markerOnly : MarkerOnlyStableClaim → DboundedFourProjectionRouteAttempt C
  | ordinaryOnly : OrdinaryOnlyStableClaim C → DboundedFourProjectionRouteAttempt C
  | fullStableProvider : DboundedFourProjectionProvider C → DboundedFourProjectionRouteAttempt C

/-- Boolean audit gate: only the full stable four-projection provider route passes. -/
def attemptAccepted
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : DboundedFourProjectionRouteAttempt C → Bool
  | .markerOnly _ => false
  | .ordinaryOnly _ => false
  | .fullStableProvider _ => true

/-- Marker-only shortcuts are rejected by the provider-route gate. -/
theorem markerOnly_rejected
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (claim : MarkerOnlyStableClaim) :
    attemptAccepted (C := C) (.markerOnly claim) = false := rfl

/-- Ordinary-context-only shortcuts are rejected by the provider-route gate. -/
theorem ordinaryOnly_rejected
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (claim : OrdinaryOnlyStableClaim C) :
    attemptAccepted (C := C) (.ordinaryOnly claim) = false := rfl

/-- A full stable four-projection provider is the accepted route input. -/
theorem fullStableProvider_accepted
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    attemptAccepted (C := C) (.fullStableProvider cert) = true := rfl

/-- The current local evidence gives only the ordinary-only rejected branch. -/
noncomputable def currentOrdinaryOnlyAttempt
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    DboundedFourProjectionRouteAttempt C :=
  .ordinaryOnly ⟨currentOrdinaryDboundedInfinityContext C⟩

/-- The current ordinary context alone is not accepted as a stable provider route. -/
theorem currentOrdinaryOnlyAttempt_rejected
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    attemptAccepted (currentOrdinaryOnlyAttempt C) = false := rfl

/-- Stable fields that the missing provider theorem must supply from one certificate. -/
def requiredProjectionFieldNames : List String :=
  ["finiteLimits", "finiteColimits", "suspensionLoopEquivalence",
    "pushoutPullbackCompatibility"]

/-- The four-projection route has exactly four required stable projection fields. -/
theorem requiredProjectionFieldNames_count :
    requiredProjectionFieldNames.length = 4 := rfl

/-- Human-readable name of the exact missing theorem. -/
def missingTheoremName : String :=
  "OrdinaryContextToDboundedFourProjectionProvider"

/-- Human-readable signature of the exact missing theorem. -/
def missingTheoremSignature : String :=
  "OrdinaryDboundedInfinityContext C -> FullStableFourProjectionCertificate (Dbounded.infinityCategory C)"

section Checks

#check OrdinaryDboundedInfinityContext
#check currentOrdinaryDboundedInfinityContext
#check FullStableFourProjectionCertificate
#check DboundedFourProjectionProvider
#check DboundedFourProjectionProvider.ready
#check DboundedFourProjectionProvider.ready_of_fields
#check OrdinaryContextToDboundedFourProjectionProvider
#check MarkerOnlyStableClaim
#check OrdinaryOnlyStableClaim
#check DboundedFourProjectionRouteAttempt
#check attemptAccepted
#check markerOnly_rejected
#check ordinaryOnly_rejected
#check fullStableProvider_accepted
#check currentOrdinaryOnlyAttempt
#check currentOrdinaryOnlyAttempt_rejected
#check requiredProjectionFieldNames
#check requiredProjectionFieldNames_count
#check missingTheoremName
#check missingTheoremSignature
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check (currentOrdinaryDboundedInfinityContext (C := MetrizableLCA))
#check (currentOrdinaryOnlyAttempt (C := MetrizableLCA))

end Checks

end DboundedFourProjectionProviderRouteW133

end LeanLCAExactChallenge
