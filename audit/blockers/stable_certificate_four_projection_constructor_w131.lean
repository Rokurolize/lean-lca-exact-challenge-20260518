import LeanLCAExactChallenge.Derived.Bounded

/-!
Stable certificate four-projection constructor audit.

This non-product file records the smallest compiling constructor this worker could
make without inventing a stable infinity-category API: if a single certificate with the
four required projections is supplied for `Dbounded.infinityCategory C`, the finite-limit
projection can be extracted as an independent provider. The file also names the exact
missing constructor signature for producing that projection from the current ordinary
`Dbounded` evidence.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableCertificateFourProjectionConstructorW131

/-- The currently available ordinary evidence for `Dbounded.infinityCategory C`. -/
structure OrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)

/-- Assemble the current ordinary `Dbounded` evidence from local declarations. -/
noncomputable def currentOrdinaryDboundedInfinityContext
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryDboundedInfinityContext C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)

/--
One certificate carrying all four stable projections required by the minimized stable
route. The projection predicates are intentionally abstract because no local semantic
stable-quasicategory API currently exists for these fields.
-/
structure StableFourProjectionCertificate (Q : SSet.QCat) : Type 2 where
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

/-- A finite-limit projection extracted from a stable certificate. -/
structure StableFiniteLimitsProjection (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  certificate : stableCertificate
  finiteLimits : stableCertificate → Prop
  finiteLimits_ready : finiteLimits certificate

/--
The compiling constructor for the seed-selected finite-limit projection: a full
single-certificate provider immediately gives a finite-limit projection from the same
certificate witness.
-/
def StableFourProjectionCertificate.finiteLimitsProjection
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    StableFiniteLimitsProjection Q where
  stableCertificate := cert.stableCertificate
  certificate := cert.certificate
  finiteLimits := cert.finiteLimits
  finiteLimits_ready := cert.finiteLimits_ready

/-- The extracted finite-limit projection is ready by the certificate's finite-limit field. -/
theorem StableFourProjectionCertificate.finiteLimitsProjection_ready
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    (cert.finiteLimitsProjection).finiteLimits
      (cert.finiteLimitsProjection).certificate := by
  exact (cert.finiteLimitsProjection).finiteLimits_ready

/-- The finite-limit projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedFiniteLimitsProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableFiniteLimitsProjection (Dbounded.infinityCategory C)

/-- The full four-projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableFourProjectionCertificate (Dbounded.infinityCategory C)

/--
Partial constructor for the stable route: once the full single certificate is supplied,
the seed-selected finite-limit provider is obtained without adding another certificate.
-/
noncomputable def dboundedFiniteLimitsProjectionOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedFiniteLimitsProjectionProvider C :=
  cert.finiteLimitsProjection

/--
Exact missing field signature after this constructor: the current ordinary `Dbounded`
context would need to produce a semantic finite-limit projection for
`Dbounded.infinityCategory C`. Existing local declarations only fill the input context.
-/
abbrev OrdinaryContextToDboundedFiniteLimitsProjection
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) :=
  OrdinaryDboundedInfinityContext C → DboundedFiniteLimitsProjectionProvider C

/-- The nearest ordinary finite-limit candidate found locally is not a stable projection. -/
def nearestFiniteLimitsOrdinaryCandidate : String :=
  "Deduced ordinary zero-object/localization context for `Dbounded C`, not finite limits of `Dbounded.infinityCategory C` as a stable quasicategory."

/-- The exact missing declaration name/signature for the seed-selected projection. -/
def missingFiniteLimitsProjectionSignature : String :=
  "OrdinaryContextToDboundedFiniteLimitsProjection C : OrdinaryDboundedInfinityContext C -> StableFiniteLimitsProjection (Dbounded.infinityCategory C)"

section Checks

#check OrdinaryDboundedInfinityContext
#check currentOrdinaryDboundedInfinityContext
#check StableFourProjectionCertificate
#check StableFiniteLimitsProjection
#check StableFourProjectionCertificate.finiteLimitsProjection
#check StableFourProjectionCertificate.finiteLimitsProjection_ready
#check DboundedFiniteLimitsProjectionProvider
#check DboundedFourProjectionProvider
#check dboundedFiniteLimitsProjectionOfFourProjectionProvider
#check OrdinaryContextToDboundedFiniteLimitsProjection
#check nearestFiniteLimitsOrdinaryCandidate
#check missingFiniteLimitsProjectionSignature
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check (currentOrdinaryDboundedInfinityContext (C := MetrizableLCA))
#check (dboundedFiniteLimitsProjectionOfFourProjectionProvider (C := MetrizableLCA))

end Checks

end StableCertificateFourProjectionConstructorW131

end LeanLCAExactChallenge
