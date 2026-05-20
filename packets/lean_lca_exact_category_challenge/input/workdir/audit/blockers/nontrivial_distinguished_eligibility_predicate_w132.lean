import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Nontrivial distinguished endpoint eligibility predicate.

The broad eligibility route in `distinguished_mapping_cone_strictification_route_w128`
is still wide enough to package arbitrary homotopy-equivalence endpoint data, and is
refuted by the alternating-tail integer-module model. This standalone audit isolates a
strictly narrower predicate: the weak endpoint witness is eligible only when its bounded
source and cone representatives are literally the selected source and selected mapping
cone.

This avoids the refuted arbitrary endpoint-witness route. The remaining provider is a
real strict-realization theorem: for each distinguished triangle with bounded endpoint
homotopy objects, choose a mapping-cone presentation whose selected source and selected
cone are themselves strictly bounded.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- The weak endpoint witness shape used by the W132 predicate. It mirrors the W128
distinguished witness, but is prefixed so this audit file compiles standalone without
importing another non-Lake `audit` module. -/
structure W132DistinguishedEndpointWeakWitness
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
/-- A W132 eligibility predicate ranges only over distinguished triangles with bounded
endpoint homotopy objects and an explicit distinguished weak endpoint witness. -/
abbrev W132DistinguishedEndpointEligibility
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    W132DistinguishedEndpointWeakWitness C T →
    Prop

omit [QuillenExactCategory C] in
/-- Provider shape for eligible W132 weak endpoint witnesses. -/
abbrev W132DistinguishedEndpointEligibilityProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (Eligible : W132DistinguishedEndpointEligibility C) : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    (h₁ : boundedHomotopyObject C T.obj₁)
    (h₃ : boundedHomotopyObject C T.obj₃),
      ∃ w : W132DistinguishedEndpointWeakWitness C T, Eligible hT h₁ h₃ w

omit [QuillenExactCategory C] in
/-- W132 endpoint upgrade shape: only eligible distinguished witnesses, not arbitrary
homotopy-equivalence endpoint data, may be promoted to cochain-level endpoint isomorphisms.
-/
abbrev W132DistinguishedEndpointCochainIsoUpgrade
    [HasZeroObject C] [HasBinaryBiproducts C]
    (Eligible : W132DistinguishedEndpointEligibility C) : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    (h₁ : boundedHomotopyObject C T.obj₁)
    (h₃ : boundedHomotopyObject C T.obj₃)
    (w : W132DistinguishedEndpointWeakWitness C T),
      Eligible hT h₁ h₃ w →
        Nonempty (w.sourceRepresentative ≅ w.selectedSource) ∧
        Nonempty (w.coneRepresentative ≅ CochainComplex.mappingCone w.selectedMap)

omit [QuillenExactCategory C] in
/-- A nontrivial distinguished endpoint eligibility predicate.

Unlike trivial eligibility, this excludes weak witnesses whose
bounded endpoint representatives are only homotopy-category isomorphic to the selected
mapping-cone endpoints. Eligibility requires those representatives to be the selected
source and selected cone themselves. -/
abbrev W132DistinguishedEndpointStrictSelectedEligibility
    [HasZeroObject C] [HasBinaryBiproducts C] :
    W132DistinguishedEndpointEligibility C :=
  fun _hT _h₁ _h₃ w =>
    w.sourceRepresentative = w.selectedSource ∧
    w.coneRepresentative = CochainComplex.mappingCone w.selectedMap

omit [QuillenExactCategory C] in
/-- Strict-selected eligibility has the endpoint cochain-isomorphism upgrade by
construction, without claiming any arbitrary homotopy-equivalence strictification. -/
theorem w132DistinguishedEndpointCochainIsoUpgrade_strictSelected
    [HasZeroObject C] [HasBinaryBiproducts C] :
    W132DistinguishedEndpointCochainIsoUpgrade C
      (W132DistinguishedEndpointStrictSelectedEligibility C) := by
  intro T hT h₁ h₃ w hw
  rcases hw with ⟨hSource, hCone⟩
  exact ⟨⟨eqToIso hSource⟩, ⟨eqToIso hCone⟩⟩

omit [QuillenExactCategory C] in
/-- Bounded strict realization supplies the provider for the strict-selected eligibility
predicate by choosing the selected source and selected cone as the representatives. -/
theorem distinguishedEndpointEligibilityProvider_strictSelected_of_realization
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : boundedHomotopyObjectTrianglehIso13Realization C) :
    W132DistinguishedEndpointEligibilityProvider C
      (W132DistinguishedEndpointStrictSelectedEligibility C) := by
  intro T hT h₁ h₃
  rcases realize hT h₁ h₃ with ⟨K, L, f, e₁, e₃, comm, hK, hCone⟩
  let w : W132DistinguishedEndpointWeakWitness C T := {
    sourceRepresentative := K
    coneRepresentative := CochainComplex.mappingCone f
    selectedSource := K
    selectedTarget := L
    selectedMap := f
    triangleSourceIso := e₁
    triangleConeIso := e₃
    triangleComm := comm
    sourceBounded := hK
    coneBounded := hCone
    sourceHomotopyCategoryIso := ⟨Iso.refl _⟩
    coneHomotopyCategoryIso := ⟨Iso.refl _⟩ }
  exact ⟨w, by
    dsimp [W132DistinguishedEndpointStrictSelectedEligibility, w]
    exact ⟨rfl, rfl⟩⟩

omit [QuillenExactCategory C] in
/-- Conversely, a provider for strict-selected eligible witnesses reaches the existing
bounded strict-realization frontier by applying the W132 upgrade and then transporting
strict boundedness along the resulting cochain isomorphisms. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_strictSelectedProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : W132DistinguishedEndpointEligibilityProvider C
      (W132DistinguishedEndpointStrictSelectedEligibility C)) :
    boundedHomotopyObjectTrianglehIso13Realization C := by
  intro T hT h₁ h₃
  rcases provider hT h₁ h₃ with ⟨w, hw⟩
  rcases w132DistinguishedEndpointCochainIsoUpgrade_strictSelected C hT h₁ h₃ w hw with
    ⟨hSourceIso, hConeIso⟩
  exact
    ⟨w.selectedSource, w.selectedTarget, w.selectedMap, w.triangleSourceIso,
      w.triangleConeIso, w.triangleComm,
      (boundedCochainComplex C).prop_of_iso hSourceIso.some w.sourceBounded,
      (boundedCochainComplex C).prop_of_iso hConeIso.some w.coneBounded⟩

omit [QuillenExactCategory C] in
/-- The strict-selected provider is not a shortcut: it is equivalent to the current
bounded strict-realization frontier. Its value is that it sharply excludes the arbitrary
weak endpoint witnesses refuted by `IntModuleCat`. -/
theorem distinguishedEndpointEligibilityProvider_strictSelected_iff_realization
    [HasZeroObject C] [HasBinaryBiproducts C] :
    W132DistinguishedEndpointEligibilityProvider C
        (W132DistinguishedEndpointStrictSelectedEligibility C) ↔
      boundedHomotopyObjectTrianglehIso13Realization C := by
  constructor
  · exact boundedHomotopyObjectTrianglehIso13Realization_of_strictSelectedProvider C
  · exact distinguishedEndpointEligibilityProvider_strictSelected_of_realization C

/-- The known negative guard remains on the arbitrary homotopy-equivalence route, not on the
strict-selected predicate isolated here. -/
theorem reject_unconditionalHomotopyEquiv_endpointStrictification_w132
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ endpointHomotopyEquivToSelectedCochainIsoStrictification
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check W132DistinguishedEndpointWeakWitness
#check W132DistinguishedEndpointEligibility
#check W132DistinguishedEndpointEligibilityProvider
#check W132DistinguishedEndpointCochainIsoUpgrade
#check W132DistinguishedEndpointStrictSelectedEligibility
#check w132DistinguishedEndpointCochainIsoUpgrade_strictSelected
#check distinguishedEndpointEligibilityProvider_strictSelected_of_realization
#check boundedHomotopyObjectTrianglehIso13Realization_of_strictSelectedProvider
#check distinguishedEndpointEligibilityProvider_strictSelected_iff_realization
#check reject_unconditionalHomotopyEquiv_endpointStrictification_w132

end Checks

end LeanLCAExactChallenge
