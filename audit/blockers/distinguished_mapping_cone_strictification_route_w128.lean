import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Distinguished mapping-cone strictification route guard.

The alternating-tail counterexample rejects the unconditional bridge from arbitrary
homotopy equivalences to cochain-complex isomorphisms. This file keeps that negative
guard separate from a narrower distinguished-only route: an external certificate may mark
which weak endpoint witnesses are eligible, and an upgrade on only those eligible
witnesses is enough for the bounded `triangleh` strictification frontier.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- The weak endpoint witness shape supplied by distinguished mapping-cone presentations:
strictly bounded representatives map to the selected source and selected cone only in the
homotopy category. -/
structure DistinguishedEndpointWeakWitness
    [HasZeroObject C] [HasBinaryBiproducts C]
    (T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))) where
  sourceRepresentative : CochainComplex C ℤ
  coneRepresentative : CochainComplex C ℤ
  selectedSource : CochainComplex C ℤ
  selectedTarget : CochainComplex C ℤ
  selectedMap : selectedSource ⟶ selectedTarget
  triangleSourceIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₁ ≅ T.obj₁
  triangleConeIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₃ ≅ T.obj₃
  triangleComm :
    (CochainComplex.mappingCone.triangleh selectedMap).mor₃ ≫
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map
          triangleSourceIso.hom =
      triangleConeIso.hom ≫ T.mor₃
  sourceBounded : boundedCochainComplex C sourceRepresentative
  coneBounded : boundedCochainComplex C coneRepresentative
  sourceHomotopyCategoryIso :
    Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj sourceRepresentative ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj selectedSource)
  coneHomotopyCategoryIso :
    Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj coneRepresentative ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone selectedMap))

omit [QuillenExactCategory C] in
/-- A distinguished-only certificate predicate. It is deliberately an input, not derived
from arbitrary homotopy equivalence data. -/
abbrev DistinguishedEndpointEligibility
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    DistinguishedEndpointWeakWitness C T →
    Prop

omit [QuillenExactCategory C] in
/-- The external provider still missing for the distinguished-only route: produce an
eligible weak endpoint witness for each distinguished triangle with bounded endpoints. -/
abbrev DistinguishedEndpointEligibilityProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (Eligible : DistinguishedEndpointEligibility C) : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    (h₁ : boundedHomotopyObject C T.obj₁)
    (h₃ : boundedHomotopyObject C T.obj₃),
      ∃ w : DistinguishedEndpointWeakWitness C T, Eligible hT h₁ h₃ w

omit [QuillenExactCategory C] in
/-- The only strictification upgrade allowed by this route: promote homotopy-category
endpoint isomorphisms to cochain-complex isomorphisms for eligible distinguished endpoint
witnesses, not for arbitrary homotopy equivalences. -/
abbrev DistinguishedEndpointCochainIsoUpgrade
    [HasZeroObject C] [HasBinaryBiproducts C]
    (Eligible : DistinguishedEndpointEligibility C) : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    (h₁ : boundedHomotopyObject C T.obj₁)
    (h₃ : boundedHomotopyObject C T.obj₃)
    (w : DistinguishedEndpointWeakWitness C T),
      Eligible hT h₁ h₃ w →
        Nonempty (w.sourceRepresentative ≅ w.selectedSource) ∧
        Nonempty (w.coneRepresentative ≅ CochainComplex.mappingCone w.selectedMap)

omit [QuillenExactCategory C] in
/-- The broadest distinguished-only eligibility predicate: every weak endpoint witness
coming from a distinguished triangle is eligible. This is still narrower than arbitrary
homotopy-equivalence transport because it is parameterized by a distinguished triangle and
an explicit mapping-cone witness. -/
abbrev DistinguishedEndpointTrivialEligibility
    [HasZeroObject C] [HasBinaryBiproducts C] :
    DistinguishedEndpointEligibility C :=
  fun _hT _h₁ _h₃ _w => True

omit [QuillenExactCategory C] in
/-- The existing weak endpoint payload already supplies eligible distinguished witnesses
for the trivial eligibility predicate. Thus the nontrivial remaining input is the
cochain-isomorphism upgrade on those witnesses. -/
theorem distinguishedEndpointEligibilityProvider_trivial
    [HasZeroObject C] [HasBinaryBiproducts C] :
    DistinguishedEndpointEligibilityProvider C
      (DistinguishedEndpointTrivialEligibility C) := by
  intro T hT h₁ h₃
  rcases homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished
      C hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hKiso, hConeIso⟩
  exact ⟨{
    sourceRepresentative := Ksrc
    coneRepresentative := Kcone
    selectedSource := K
    selectedTarget := L
    selectedMap := f
    triangleSourceIso := e₁
    triangleConeIso := e₃
    triangleComm := comm
    sourceBounded := hKsrc
    coneBounded := hKcone
    sourceHomotopyCategoryIso := hKiso
    coneHomotopyCategoryIso := hConeIso }, trivial⟩

omit [QuillenExactCategory C] in
/-- With the witness provider now discharged by the existing distinguished-triangle
payload, the bounded route is reduced to a cochain-isomorphism upgrade for distinguished
weak endpoint witnesses. -/
theorem boundedTrianglehIso13CochainDataStrictification_of_trivialEligibilityUpgrade
    [HasZeroObject C] [HasBinaryBiproducts C]
    (upgrade : DistinguishedEndpointCochainIsoUpgrade C
      (DistinguishedEndpointTrivialEligibility C)) :
    boundedTrianglehIso13CochainDataStrictification C := by
  intro T hT h₁ h₃
  rcases distinguishedEndpointEligibilityProvider_trivial C hT h₁ h₃ with ⟨w, hw⟩
  rcases upgrade hT h₁ h₃ w hw with ⟨hSourceIso, hConeIso⟩
  exact
    ⟨w.sourceRepresentative, w.coneRepresentative, w.selectedSource, w.selectedTarget,
      w.selectedMap, w.triangleSourceIso, w.triangleConeIso, hSourceIso.some,
      hConeIso.some, w.triangleComm, w.sourceBounded, w.coneBounded⟩

omit [QuillenExactCategory C] in
/-- The corresponding bounded strict-realization consequence after the provider side has
been discharged. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_trivialEligibilityUpgrade
    [HasZeroObject C] [HasBinaryBiproducts C]
    (upgrade : DistinguishedEndpointCochainIsoUpgrade C
      (DistinguishedEndpointTrivialEligibility C)) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data C
    (boundedTrianglehIso13CochainDataStrictification_of_trivialEligibilityUpgrade
      C upgrade)

omit [QuillenExactCategory C] in
/-- A distinguished-only certificate provider and eligible-witness upgrade are enough for
the expanded cochain-data strictification frontier. -/
theorem boundedTrianglehIso13CochainDataStrictification_of_distinguishedEndpointCertificate
    [HasZeroObject C] [HasBinaryBiproducts C]
    {Eligible : DistinguishedEndpointEligibility C}
    (provider : DistinguishedEndpointEligibilityProvider C Eligible)
    (upgrade : DistinguishedEndpointCochainIsoUpgrade C Eligible) :
    boundedTrianglehIso13CochainDataStrictification C := by
  intro T hT h₁ h₃
  rcases provider hT h₁ h₃ with ⟨w, hw⟩
  rcases upgrade hT h₁ h₃ w hw with ⟨hSourceIso, hConeIso⟩
  exact
    ⟨w.sourceRepresentative, w.coneRepresentative, w.selectedSource, w.selectedTarget,
      w.selectedMap, w.triangleSourceIso, w.triangleConeIso, hSourceIso.some,
      hConeIso.some, w.triangleComm, w.sourceBounded, w.coneBounded⟩

omit [QuillenExactCategory C] in
/-- The same distinguished-only certificate route reaches the bounded strict realization
consumer used by the current middle-term frontier. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_distinguishedEndpointCertificate
    [HasZeroObject C] [HasBinaryBiproducts C]
    {Eligible : DistinguishedEndpointEligibility C}
    (provider : DistinguishedEndpointEligibilityProvider C Eligible)
    (upgrade : DistinguishedEndpointCochainIsoUpgrade C Eligible) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data C
    (boundedTrianglehIso13CochainDataStrictification_of_distinguishedEndpointCertificate
      C provider upgrade)

/-- Audit status for candidate endpoint strictification routes. -/
inductive EndpointStrictificationGuardStatus where
  | rejectedByAlternatingTail
  | openPendingDistinguishedCertificate
  deriving DecidableEq, Repr

/-- The unrestricted homotopy-equivalence bridge is the rejected route. -/
def unconditionalHomotopyEquivRouteStatus : EndpointStrictificationGuardStatus :=
  EndpointStrictificationGuardStatus.rejectedByAlternatingTail

/-- The distinguished certificate route remains open because it has an extra eligibility
certificate and never claims arbitrary homotopy-equivalence transport. -/
def distinguishedCertificateRouteStatus : EndpointStrictificationGuardStatus :=
  EndpointStrictificationGuardStatus.openPendingDistinguishedCertificate

/-- The concrete negative guard: arbitrary homotopy-equivalence endpoint strictification
is refuted in `IntModuleCat`. -/
theorem reject_unconditionalHomotopyEquiv_endpointStrictification_w128
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ endpointHomotopyEquivToSelectedCochainIsoStrictification
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

/-- The guard classifies the distinguished-certificate route separately from the rejected
unconditional route. -/
theorem distinguishedCertificateRoute_not_rejectedByAlternatingTail :
    distinguishedCertificateRouteStatus ≠ unconditionalHomotopyEquivRouteStatus := by
  intro h
  cases h

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check DistinguishedEndpointWeakWitness
#check DistinguishedEndpointEligibility
#check DistinguishedEndpointEligibilityProvider
#check DistinguishedEndpointCochainIsoUpgrade
#check DistinguishedEndpointTrivialEligibility
#check distinguishedEndpointEligibilityProvider_trivial
#check boundedTrianglehIso13CochainDataStrictification_of_trivialEligibilityUpgrade
#check boundedHomotopyObjectTrianglehIso13Realization_of_trivialEligibilityUpgrade
#check boundedTrianglehIso13CochainDataStrictification_of_distinguishedEndpointCertificate
#check boundedHomotopyObjectTrianglehIso13Realization_of_distinguishedEndpointCertificate
#check reject_unconditionalHomotopyEquiv_endpointStrictification_w128
#check distinguishedCertificateRoute_not_rejectedByAlternatingTail
#check homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished
#check boundedTrianglehIso13CochainDataStrictification
#check endpointHomotopyEquivToSelectedCochainIsoStrictification

end Checks

end LeanLCAExactChallenge
