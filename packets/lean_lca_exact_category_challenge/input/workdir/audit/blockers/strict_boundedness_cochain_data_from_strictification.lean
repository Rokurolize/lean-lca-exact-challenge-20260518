import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- Backward-compatible audit name for the product-side cochain-data consumer. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13CochainDataStrictification C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data C strictify

/-- The exact-acyclic and bounded routes need different strictification outputs.

The exact route asks for `exactAcyclic C L` for the selected middle strict complex. The
bounded route asks instead for cochain-level transport of strict boundedness to the selected
source and selected mapping cone. Providing both inputs gives the two `Closed₂` classes
consumed by the ordinary bounded homotopy Verdier scaffolding. -/
theorem exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exact_realization_and_cochain_data
    [HasZeroObject C] [HasBinaryBiproducts C]
    (exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C)
    (boundedStrictify : boundedTrianglehIso13CochainDataStrictification C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ ∧
      (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations
    C exactRealize
    (boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
      C boundedStrictify)

omit [QuillenExactCategory C] in
/-- The local consequence of a weak endpoint payload: mathlib extracts homotopy
equivalences from homotopy-category isomorphisms, not strict cochain isomorphisms. -/
theorem homotopyEndpointPayload_extracts_homotopyEquivData
    [HasZeroObject C] [HasBinaryBiproducts C]
    (weak : homotopyEndpointPayloadWithoutSelectedCochainIso C)
    {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)))
    (h₁ : boundedHomotopyObject C T.obj₁)
    (h₃ : boundedHomotopyObject C T.obj₃) :
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
      (_ηK : HomotopyEquiv Ksrc K)
      (_ηCone : HomotopyEquiv Kcone (CochainComplex.mappingCone f)),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone := by
  rcases weak hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hK, hCone⟩
  exact ⟨Ksrc, Kcone, K, L, f, e₁, e₃,
    HomotopyCategory.homotopyEquivOfIso hK.some,
    HomotopyCategory.homotopyEquivOfIso hCone.some,
    comm, hKsrc, hKcone⟩

omit [QuillenExactCategory C] in
/-- With a separate strictification theorem from homotopy equivalences to cochain
isomorphisms, the weak endpoint payload upgrades to the cochain-level payload consumed
above. -/
theorem boundedTrianglehIso13CochainDataStrictification_of_homotopyEndpointPayload
    [HasZeroObject C] [HasBinaryBiproducts C]
    (weak : homotopyEndpointPayloadWithoutSelectedCochainIso C)
    (strictify : endpointHomotopyEquivToSelectedCochainIsoStrictification C) :
    boundedTrianglehIso13CochainDataStrictification C := by
  intro T hT h₁ h₃
  rcases homotopyEndpointPayload_extracts_homotopyEquivData C weak hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, ηK, ηCone, comm, hKsrc, hKcone⟩
  rcases strictify (Ksrc := Ksrc) (Kcone := Kcone) (K := K) (L := L) (f := f)
      hKsrc hKcone ηK ηCone with
    ⟨eK, eCone, _⟩
  exact ⟨Ksrc, Kcone, K, L, f, e₁, e₃, eK, eCone, comm, hKsrc, hKcone⟩

/-- The exact upgrade from weak homotopy endpoints to the paired `Closed₂` conclusion is
conditional on a separate homotopy-equivalence-to-cochain-isomorphism strictification
theorem. -/
theorem closed2_pair_of_homotopyEndpointPayload_and_selectedCochainIsoStrictification
    [HasZeroObject C] [HasBinaryBiproducts C]
    (exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C)
    (weak : homotopyEndpointPayloadWithoutSelectedCochainIso C)
    (strictify : endpointHomotopyEquivToSelectedCochainIsoStrictification C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ ∧
      (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exact_realization_and_cochain_data
    C exactRealize
    (boundedTrianglehIso13CochainDataStrictification_of_homotopyEndpointPayload
      C weak strictify)

#check boundedTrianglehIso13CochainDataStrictification
#check boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data_strictification
#check exactAcyclicHomotopyIsoClosureTrianglehIso13Realization
#check exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exact_realization_and_cochain_data
#check homotopyEndpointPayloadWithoutSelectedCochainIso
#check homotopyEndpointPayload_extracts_homotopyEquivData
#check endpointHomotopyEquivToSelectedCochainIsoStrictification
#check boundedTrianglehIso13CochainDataStrictification_of_homotopyEndpointPayload
#check closed2_pair_of_homotopyEndpointPayload_and_selectedCochainIsoStrictification

end LeanLCAExactChallenge
