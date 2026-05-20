import LeanLCAExactChallenge.Derived.Bounded

/-!
Stable certificate four-projection constructor audit.

This non-product file records a compiling constructor shape that does not invent a stable
infinity-category API: if a single certificate with the four required projections is
supplied for `Dbounded.infinityCategory C`, each projection can be extracted as an
independent provider. The file also names the missing constructor signature for producing
those projections from the current ordinary `Dbounded` evidence.
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

/-- A finite-colimit projection extracted from a stable certificate. -/
structure StableFiniteColimitsProjection (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  certificate : stableCertificate
  finiteColimits : stableCertificate → Prop
  finiteColimits_ready : finiteColimits certificate

/-- A suspension-loop equivalence projection extracted from a stable certificate. -/
structure StableSuspensionLoopProjection (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  certificate : stableCertificate
  suspensionLoopEquivalence : stableCertificate → Prop
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence certificate

/-- A pushout-pullback compatibility projection extracted from a stable certificate. -/
structure StablePushoutPullbackProjection (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  certificate : stableCertificate
  pushoutPullbackCompatibility : stableCertificate → Prop
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility certificate

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

/-- A full single-certificate provider gives a finite-colimit projection from the same
certificate witness. -/
def StableFourProjectionCertificate.finiteColimitsProjection
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    StableFiniteColimitsProjection Q where
  stableCertificate := cert.stableCertificate
  certificate := cert.certificate
  finiteColimits := cert.finiteColimits
  finiteColimits_ready := cert.finiteColimits_ready

/-- A full single-certificate provider gives a suspension-loop projection from the same
certificate witness. -/
def StableFourProjectionCertificate.suspensionLoopProjection
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    StableSuspensionLoopProjection Q where
  stableCertificate := cert.stableCertificate
  certificate := cert.certificate
  suspensionLoopEquivalence := cert.suspensionLoopEquivalence
  suspensionLoopEquivalence_ready := cert.suspensionLoopEquivalence_ready

/-- A full single-certificate provider gives a pushout-pullback projection from the same
certificate witness. -/
def StableFourProjectionCertificate.pushoutPullbackProjection
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    StablePushoutPullbackProjection Q where
  stableCertificate := cert.stableCertificate
  certificate := cert.certificate
  pushoutPullbackCompatibility := cert.pushoutPullbackCompatibility
  pushoutPullbackCompatibility_ready := cert.pushoutPullbackCompatibility_ready

/-- The extracted finite-limit projection is ready by the certificate's finite-limit field. -/
theorem StableFourProjectionCertificate.finiteLimitsProjection_ready
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    (cert.finiteLimitsProjection).finiteLimits
      (cert.finiteLimitsProjection).certificate := by
  exact (cert.finiteLimitsProjection).finiteLimits_ready

/-- The extracted finite-colimit projection is ready by the certificate's finite-colimit field. -/
theorem StableFourProjectionCertificate.finiteColimitsProjection_ready
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    (cert.finiteColimitsProjection).finiteColimits
      (cert.finiteColimitsProjection).certificate := by
  exact (cert.finiteColimitsProjection).finiteColimits_ready

/-- The extracted suspension-loop projection is ready by the certificate's suspension-loop field. -/
theorem StableFourProjectionCertificate.suspensionLoopProjection_ready
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    (cert.suspensionLoopProjection).suspensionLoopEquivalence
      (cert.suspensionLoopProjection).certificate := by
  exact (cert.suspensionLoopProjection).suspensionLoopEquivalence_ready

/-- The extracted pushout-pullback projection is ready by the certificate's compatibility field. -/
theorem StableFourProjectionCertificate.pushoutPullbackProjection_ready
    {Q : SSet.QCat} (cert : StableFourProjectionCertificate Q) :
    (cert.pushoutPullbackProjection).pushoutPullbackCompatibility
      (cert.pushoutPullbackProjection).certificate := by
  exact (cert.pushoutPullbackProjection).pushoutPullbackCompatibility_ready

/-- The finite-limit projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedFiniteLimitsProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableFiniteLimitsProjection (Dbounded.infinityCategory C)

/-- The finite-colimit projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedFiniteColimitsProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableFiniteColimitsProjection (Dbounded.infinityCategory C)

/-- The suspension-loop projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedSuspensionLoopProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StableSuspensionLoopProjection (Dbounded.infinityCategory C)

/-- The pushout-pullback projection provider required specifically for `Dbounded.infinityCategory C`. -/
abbrev DboundedPushoutPullbackProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 :=
  StablePushoutPullbackProjection (Dbounded.infinityCategory C)

/-- The four extracted projection providers for `Dbounded.infinityCategory C`. -/
structure DboundedExtractedFourProjectionProviders
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 where
  finiteLimits : DboundedFiniteLimitsProjectionProvider C
  finiteColimits : DboundedFiniteColimitsProjectionProvider C
  suspensionLoop : DboundedSuspensionLoopProjectionProvider C
  pushoutPullback : DboundedPushoutPullbackProjectionProvider C

/-- Readiness predicate for all four extracted `Dbounded` stable projection providers. -/
def DboundedExtractedFourProjectionProviders.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (providers : DboundedExtractedFourProjectionProviders C) :
    Prop :=
  providers.finiteLimits.finiteLimits providers.finiteLimits.certificate ∧
    providers.finiteColimits.finiteColimits providers.finiteColimits.certificate ∧
    providers.suspensionLoop.suspensionLoopEquivalence
      providers.suspensionLoop.certificate ∧
    providers.pushoutPullback.pushoutPullbackCompatibility
      providers.pushoutPullback.certificate

/-- Product-review-shaped proposition bundle obtained after the four stable projections are
available. This strips the certificate-dependent provider records down to the four
semantic propositions a future product gate has to consume. -/
structure DboundedFourProjectionReadinessEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 where
  finiteLimits : Prop
  finiteColimits : Prop
  suspensionLoopEquivalence : Prop
  pushoutPullbackCompatibility : Prop
  finiteLimits_ready : finiteLimits
  finiteColimits_ready : finiteColimits
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility

/-- The product-review-shaped four-field pass predicate. -/
def DboundedFourProjectionReadinessEvidence.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (evidence : DboundedFourProjectionReadinessEvidence C) :
    Prop :=
  evidence.finiteLimits ∧ evidence.finiteColimits ∧
    evidence.suspensionLoopEquivalence ∧ evidence.pushoutPullbackCompatibility

/-- Extracted provider records produce the proposition bundle consumed by the next stable
product gate. -/
def DboundedFourProjectionReadinessEvidence.ofExtractedProviders
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (providers : DboundedExtractedFourProjectionProviders C) :
    DboundedFourProjectionReadinessEvidence C where
  finiteLimits := providers.finiteLimits.finiteLimits providers.finiteLimits.certificate
  finiteColimits := providers.finiteColimits.finiteColimits providers.finiteColimits.certificate
  suspensionLoopEquivalence :=
    providers.suspensionLoop.suspensionLoopEquivalence
      providers.suspensionLoop.certificate
  pushoutPullbackCompatibility :=
    providers.pushoutPullback.pushoutPullbackCompatibility
      providers.pushoutPullback.certificate
  finiteLimits_ready := providers.finiteLimits.finiteLimits_ready
  finiteColimits_ready := providers.finiteColimits.finiteColimits_ready
  suspensionLoopEquivalence_ready := providers.suspensionLoop.suspensionLoopEquivalence_ready
  pushoutPullbackCompatibility_ready :=
    providers.pushoutPullback.pushoutPullbackCompatibility_ready

/-- The proposition bundle obtained from extracted providers satisfies the product-review
four-field pass predicate. -/
theorem DboundedFourProjectionReadinessEvidence.ready_ofExtractedProviders
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (providers : DboundedExtractedFourProjectionProviders C) :
    (DboundedFourProjectionReadinessEvidence.ofExtractedProviders providers).ready := by
  exact ⟨providers.finiteLimits.finiteLimits_ready,
    providers.finiteColimits.finiteColimits_ready,
    providers.suspensionLoop.suspensionLoopEquivalence_ready,
    providers.pushoutPullback.pushoutPullbackCompatibility_ready⟩

/--
Consumer-side stable pass witness for a future product gate. It deliberately depends on
the four-proposition readiness bundle rather than on the original certificate provider,
so the remaining construction problem stays isolated at the provider boundary.
-/
structure DboundedStableProductGatePass
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type 2 where
  readinessEvidence : DboundedFourProjectionReadinessEvidence C
  readinessEvidence_ready : readinessEvidence.ready

/-- A readiness evidence bundle satisfying its four-field predicate is accepted by the
consumer-side stable product gate. -/
def DboundedStableProductGatePass.ofReadinessEvidence
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (evidence : DboundedFourProjectionReadinessEvidence C)
    (ready : evidence.ready) :
    DboundedStableProductGatePass C where
  readinessEvidence := evidence
  readinessEvidence_ready := ready

/-- Extracted four-projection providers are enough for the consumer-side stable pass gate. -/
def DboundedStableProductGatePass.ofExtractedProviders
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (providers : DboundedExtractedFourProjectionProviders C) :
    DboundedStableProductGatePass C :=
  DboundedStableProductGatePass.ofReadinessEvidence
    (DboundedFourProjectionReadinessEvidence.ofExtractedProviders providers)
    (DboundedFourProjectionReadinessEvidence.ready_ofExtractedProviders providers)

/-- The pass witness obtained from extracted providers carries the expected readiness
predicate, which is the exact condition a future product review can consume. -/
theorem DboundedStableProductGatePass.ready_ofExtractedProviders
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (providers : DboundedExtractedFourProjectionProviders C) :
    (DboundedStableProductGatePass.ofExtractedProviders providers).readinessEvidence.ready := by
  exact (DboundedStableProductGatePass.ofExtractedProviders providers).readinessEvidence_ready

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

/-- Extract the finite-colimit projection from a full `Dbounded` four-projection certificate. -/
noncomputable def dboundedFiniteColimitsProjectionOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedFiniteColimitsProjectionProvider C :=
  cert.finiteColimitsProjection

/-- Extract the suspension-loop projection from a full `Dbounded` four-projection certificate. -/
noncomputable def dboundedSuspensionLoopProjectionOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedSuspensionLoopProjectionProvider C :=
  cert.suspensionLoopProjection

/-- Extract the pushout-pullback projection from a full `Dbounded` four-projection certificate. -/
noncomputable def dboundedPushoutPullbackProjectionOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedPushoutPullbackProjectionProvider C :=
  cert.pushoutPullbackProjection

/-- Extract all four stable projections from the same full `Dbounded` certificate. -/
noncomputable def dboundedExtractedFourProjectionProvidersOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedExtractedFourProjectionProviders C where
  finiteLimits := dboundedFiniteLimitsProjectionOfFourProjectionProvider C cert
  finiteColimits := dboundedFiniteColimitsProjectionOfFourProjectionProvider C cert
  suspensionLoop := dboundedSuspensionLoopProjectionOfFourProjectionProvider C cert
  pushoutPullback := dboundedPushoutPullbackProjectionOfFourProjectionProvider C cert

/-- Extracted projection providers from a full certificate satisfy the four-field readiness
predicate. -/
theorem dboundedExtractedFourProjectionProviders_ready_of_fourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    (dboundedExtractedFourProjectionProvidersOfFourProjectionProvider C cert).ready := by
  exact ⟨cert.finiteLimits_ready, cert.finiteColimits_ready,
    cert.suspensionLoopEquivalence_ready, cert.pushoutPullbackCompatibility_ready⟩

/-- A full four-projection certificate also supplies the proposition bundle expected by a
future stable product review gate. -/
noncomputable def dboundedFourProjectionReadinessEvidenceOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedFourProjectionReadinessEvidence C :=
  DboundedFourProjectionReadinessEvidence.ofExtractedProviders
    (dboundedExtractedFourProjectionProvidersOfFourProjectionProvider C cert)

/-- The product-review-shaped evidence obtained from a full certificate satisfies the
four-field readiness predicate. -/
theorem dboundedFourProjectionReadinessEvidence_ready_of_fourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    (dboundedFourProjectionReadinessEvidenceOfFourProjectionProvider C cert).ready := by
  exact DboundedFourProjectionReadinessEvidence.ready_ofExtractedProviders _

/-- A full four-projection certificate supplies the consumer-side stable pass witness. -/
noncomputable def dboundedStableProductGatePassOfFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    DboundedStableProductGatePass C :=
  DboundedStableProductGatePass.ofReadinessEvidence
    (dboundedFourProjectionReadinessEvidenceOfFourProjectionProvider C cert)
    (dboundedFourProjectionReadinessEvidence_ready_of_fourProjectionProvider C cert)

/-- The pass witness extracted from a full certificate carries the four-field readiness
predicate. -/
theorem dboundedStableProductGatePass_ready_of_fourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (cert : DboundedFourProjectionProvider C) :
    (dboundedStableProductGatePassOfFourProjectionProvider C cert).readinessEvidence.ready := by
  exact (dboundedStableProductGatePassOfFourProjectionProvider C cert).readinessEvidence_ready

/--
Exact missing field signature after these constructors: the current ordinary `Dbounded`
context would need to produce the full semantic four-projection certificate for
`Dbounded.infinityCategory C`. Existing local declarations only fill the input context.
-/
abbrev OrdinaryContextToDboundedFourProjectionProvider
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) :=
  OrdinaryDboundedInfinityContext C → DboundedFourProjectionProvider C

/-- The nearest ordinary candidates found locally are not stable projection providers. -/
def nearestOrdinaryStableProjectionCandidates : List String :=
  ["ordinary quasicategory witness for `Dbounded.infinityNerve C`",
    "ordinary homotopy category comparison `hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)`",
    "ordinary zero-object/localization context for `Dbounded C`"]

/-- The exact missing declaration name/signature for the full stable projection provider. -/
def missingFourProjectionProviderSignature : String :=
  "OrdinaryContextToDboundedFourProjectionProvider C : OrdinaryDboundedInfinityContext C -> StableFourProjectionCertificate (Dbounded.infinityCategory C)"

section Checks

#check OrdinaryDboundedInfinityContext
#check currentOrdinaryDboundedInfinityContext
#check StableFourProjectionCertificate
#check StableFiniteLimitsProjection
#check StableFiniteColimitsProjection
#check StableSuspensionLoopProjection
#check StablePushoutPullbackProjection
#check StableFourProjectionCertificate.finiteLimitsProjection
#check StableFourProjectionCertificate.finiteColimitsProjection
#check StableFourProjectionCertificate.suspensionLoopProjection
#check StableFourProjectionCertificate.pushoutPullbackProjection
#check StableFourProjectionCertificate.finiteLimitsProjection_ready
#check StableFourProjectionCertificate.finiteColimitsProjection_ready
#check StableFourProjectionCertificate.suspensionLoopProjection_ready
#check StableFourProjectionCertificate.pushoutPullbackProjection_ready
#check DboundedFiniteLimitsProjectionProvider
#check DboundedFiniteColimitsProjectionProvider
#check DboundedSuspensionLoopProjectionProvider
#check DboundedPushoutPullbackProjectionProvider
#check DboundedExtractedFourProjectionProviders
#check DboundedExtractedFourProjectionProviders.ready
#check DboundedFourProjectionReadinessEvidence
#check DboundedFourProjectionReadinessEvidence.ready
#check DboundedFourProjectionReadinessEvidence.ofExtractedProviders
#check DboundedFourProjectionReadinessEvidence.ready_ofExtractedProviders
#check DboundedStableProductGatePass
#check DboundedStableProductGatePass.ofReadinessEvidence
#check DboundedStableProductGatePass.ofExtractedProviders
#check DboundedStableProductGatePass.ready_ofExtractedProviders
#check DboundedFourProjectionProvider
#check dboundedFiniteLimitsProjectionOfFourProjectionProvider
#check dboundedFiniteColimitsProjectionOfFourProjectionProvider
#check dboundedSuspensionLoopProjectionOfFourProjectionProvider
#check dboundedPushoutPullbackProjectionOfFourProjectionProvider
#check dboundedExtractedFourProjectionProvidersOfFourProjectionProvider
#check dboundedExtractedFourProjectionProviders_ready_of_fourProjectionProvider
#check dboundedFourProjectionReadinessEvidenceOfFourProjectionProvider
#check dboundedFourProjectionReadinessEvidence_ready_of_fourProjectionProvider
#check dboundedStableProductGatePassOfFourProjectionProvider
#check dboundedStableProductGatePass_ready_of_fourProjectionProvider
#check OrdinaryContextToDboundedFourProjectionProvider
#check nearestOrdinaryStableProjectionCandidates
#check missingFourProjectionProviderSignature
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check (currentOrdinaryDboundedInfinityContext (C := MetrizableLCA))
#check (dboundedFiniteLimitsProjectionOfFourProjectionProvider (C := MetrizableLCA))
#check (dboundedFiniteColimitsProjectionOfFourProjectionProvider (C := MetrizableLCA))
#check (dboundedSuspensionLoopProjectionOfFourProjectionProvider (C := MetrizableLCA))
#check (dboundedPushoutPullbackProjectionOfFourProjectionProvider (C := MetrizableLCA))
#check (dboundedExtractedFourProjectionProvidersOfFourProjectionProvider (C := MetrizableLCA))
#check (dboundedStableProductGatePassOfFourProjectionProvider (C := MetrizableLCA))

end Checks

end StableCertificateFourProjectionConstructorW131

end LeanLCAExactChallenge
