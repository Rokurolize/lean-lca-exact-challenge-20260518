import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Mapping-cone selected provider probe.

The current distinguished-triangle endpoint declaration supplies a mapping-cone
presentation together with bounded strict representatives for the source and cone.
The selected source and selected cone are related to those representatives only in the
homotopy category. This audit file records the smallest extra fields that would turn
that actual weak endpoint payload into the compact selected/cochain provider.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- Exact missing fields for the mapping-cone weak endpoint payload.

The existing weak endpoint payload already has bounded representatives `Ksrc` and
`Kcone`, plus homotopy-category isomorphisms from them to the selected source `K` and
selected cone `CochainComplex.mappingCone f`. The selected/cochain provider additionally
needs actual cochain-complex isomorphisms `Ksrc ≅ K` and
`Kcone ≅ CochainComplex.mappingCone f`. -/
abbrev weakEndpointHomotopyCategoryIsoToSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {Ksrc Kcone K L : CochainComplex C ℤ} {f : K ⟶ L},
    boundedCochainComplex C Ksrc →
    boundedCochainComplex C Kcone →
    Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Ksrc ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) →
    Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Kcone ≅
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone f)) →
    Nonempty (Ksrc ≅ K) ∧ Nonempty (Kcone ≅ CochainComplex.mappingCone f)

omit [QuillenExactCategory C] in
/-- If the weak endpoint homotopy-category isomorphisms can be promoted to cochain-level
isomorphisms for the same selected mapping-cone presentation, then the compact cochain
isomorphism provider follows. -/
theorem boundedTrianglehIso13CochainIsoPayload_of_weakEndpointSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (weak : homotopyEndpointPayloadWithoutSelectedCochainIso C)
    (strictify : weakEndpointHomotopyCategoryIsoToSelectedCochainIso C) :
    boundedTrianglehIso13CochainIsoPayload C := by
  intro T hT h₁ h₃
  rcases weak hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hK, hCone⟩
  rcases strictify (Ksrc := Ksrc) (Kcone := Kcone) (K := K) (L := L) (f := f)
      hKsrc hKcone hK hCone with
    ⟨hKiso, hConeIso⟩
  exact ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hKiso, hConeIso⟩

omit [QuillenExactCategory C] in
/-- Applying the same provider to the actual distinguished-triangle weak endpoint
declaration yields the selected/cochain compact payload. This names the nearest existing
declaration and the exact extra provider it still lacks. -/
theorem boundedTrianglehIso13CochainIsoPayload_of_distinguishedEndpointSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : weakEndpointHomotopyCategoryIsoToSelectedCochainIso C) :
    boundedTrianglehIso13CochainIsoPayload C :=
  boundedTrianglehIso13CochainIsoPayload_of_weakEndpointSelectedCochainIso C
    (homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished C) strictify

omit [QuillenExactCategory C] in
/-- The direct mapping-cone endpoint provider is enough for the expanded cochain-data
frontier used by the bounded strict-realization minimizer. -/
theorem boundedTrianglehIso13CochainDataStrictification_of_distinguishedEndpointSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : weakEndpointHomotopyCategoryIsoToSelectedCochainIso C) :
    boundedTrianglehIso13CochainDataStrictification C :=
  boundedTrianglehIso13CochainDataStrictification_of_cochain_iso_payload C
    (boundedTrianglehIso13CochainIsoPayload_of_distinguishedEndpointSelectedCochainIso
      C strictify)

omit [QuillenExactCategory C] in
/-- Consequently, the same selected cochain isomorphism provider is enough for the bounded
homotopy-object middle-term closure route already implemented in product code. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_distinguishedEndpointSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : weakEndpointHomotopyCategoryIsoToSelectedCochainIso C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_iso_payload C
    (boundedTrianglehIso13CochainIsoPayload_of_distinguishedEndpointSelectedCochainIso
      C strictify)

omit [QuillenExactCategory C] in
/-- The direct homotopy-category endpoint provider is still strong enough to imply the
known-false unconditional homotopy-equivalence strictification bridge. -/
theorem endpointHomotopyEquivToSelectedCochainIsoStrictification_of_weakEndpointSelectedCochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : weakEndpointHomotopyCategoryIsoToSelectedCochainIso C) :
    endpointHomotopyEquivToSelectedCochainIsoStrictification C := by
  intro Ksrc Kcone K L f hKsrc hKcone hK hCone
  rcases strictify (Ksrc := Ksrc) (Kcone := Kcone) (K := K) (L := L) (f := f)
      hKsrc hKcone
      ⟨HomotopyCategory.isoOfHomotopyEquiv hK⟩
      ⟨HomotopyCategory.isoOfHomotopyEquiv hCone⟩ with
    ⟨hKiso, hConeIso⟩
  exact ⟨hKiso.some, hConeIso.some, trivial⟩

/-- The direct provider must not be replaced by the known-false unconditional
homotopy-equivalence strictification bridge. -/
theorem reject_unconditional_endpointHomotopyEquiv_provider_w127
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ endpointHomotopyEquivToSelectedCochainIsoStrictification
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

/-- Therefore the direct homotopy-category endpoint provider also cannot hold without
additional hypotheses controlling the selected cochain representatives. -/
theorem reject_unconditional_weakEndpointSelectedCochainIso_provider_w127
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ weakEndpointHomotopyCategoryIsoToSelectedCochainIso
        AlternatingTailExtendTransport.IntModuleCat := by
  intro strictify
  exact reject_unconditional_endpointHomotopyEquiv_provider_w127
    (endpointHomotopyEquivToSelectedCochainIsoStrictification_of_weakEndpointSelectedCochainIso
      AlternatingTailExtendTransport.IntModuleCat strictify)

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished
#check weakEndpointHomotopyCategoryIsoToSelectedCochainIso
#check boundedTrianglehIso13CochainIsoPayload_of_weakEndpointSelectedCochainIso
#check boundedTrianglehIso13CochainIsoPayload_of_distinguishedEndpointSelectedCochainIso
#check boundedTrianglehIso13CochainDataStrictification_of_distinguishedEndpointSelectedCochainIso
#check boundedHomotopyObjectTrianglehIso13Realization_of_distinguishedEndpointSelectedCochainIso
#check endpointHomotopyEquivToSelectedCochainIsoStrictification_of_weakEndpointSelectedCochainIso
#check reject_unconditional_endpointHomotopyEquiv_provider_w127
#check reject_unconditional_weakEndpointSelectedCochainIso_provider_w127

end Checks

end LeanLCAExactChallenge
