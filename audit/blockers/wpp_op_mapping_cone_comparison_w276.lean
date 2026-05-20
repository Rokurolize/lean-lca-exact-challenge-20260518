import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W276: `WalkingParallelPairᵒᵖ` mapping-cone comparison boundary.

W271 named the direct input
`mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison`.  This audit reduces
that input to a smaller object-level comparison: build the WPP-op cochain-complex colimit whose
objects are isomorphic to the component mapping cones and whose colimit point is isomorphic to the
mapping cone of the bounded-inclusion comparison map.  Exact acyclicity of the objects then follows
formally from the objectwise bounded weak-equivalence hypothesis.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeComparisonW276

/-- The direct bounded exact weak-equivalence class for metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/--
The W271 comparison input, restated locally so this audit file remains standalone.
-/
abbrev mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      (metrizableLCAWeakEquivalence).functorCategory WalkingParallelPairᵒᵖ f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPairᵒᵖ,
            c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
            ∃ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
              (ck : Cocone K),
                Nonempty (IsColimit ck) ∧
                  (∀ j : WalkingParallelPairᵒᵖ,
                    exactAcyclic MetrizableLCA (K.obj j)) ∧
                  Nonempty
                    (CochainComplex.mappingCone
                        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/--
Smaller object-level boundary for the WPP-op mapping-cone comparison.

This statement asks only for the comparison diagram and its isomorphisms.  It deliberately omits
the component exactness proof, which is recovered from the objectwise bounded weak-equivalence
hypothesis in the checked consumer below.
-/
abbrev walkingParallelPairOp_mappingCone_objectComparisonBoundary : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt),
      (∀ j : WalkingParallelPairᵒᵖ,
        c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
        ∃ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
          (ck : Cocone K),
            Nonempty (IsColimit ck) ∧
              (∀ j : WalkingParallelPairᵒᵖ,
                Nonempty
                  (CochainComplex.mappingCone
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≅
                      K.obj j)) ∧
              Nonempty
                (CochainComplex.mappingCone
                  ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/--
The object-level comparison boundary formally supplies W271's mapping-cone comparison input.
-/
theorem mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_objectBoundary
    (hboundary : walkingParallelPairOp_mappingCone_objectComparisonBoundary) :
    mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  rcases hboundary X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with
    ⟨K, ck, hck, hK, hcone⟩
  refine ⟨K, ck, hck, ?_, hcone⟩
  intro j
  rcases hK j with ⟨e⟩
  exact exactAcyclic_of_iso MetrizableLCA e (by
    change exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)))
    exact hf j)

/-- Machine-readable frontier state for W276. -/
structure WppOpMappingConeComparisonState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W276 boundary state. -/
def currentWppOpMappingConeComparisonState : WppOpMappingConeComparisonState where
  seed := "w276-20260520T154252Z-ae4d00787f94adc8"
  selectedRoute :=
    "reduce W271 mapping-cone comparison to object-level WPP-op cone/colimit comparison"
  checkedBoundary :=
    "walkingParallelPairOp_mappingCone_objectComparisonBoundary"
  provedConsumer :=
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_objectBoundary"
  remainingInputs :=
    ["walkingParallelPairOp_mappingCone_objectComparisonBoundary",
      "exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeComparisonState_productSuccess :
    currentWppOpMappingConeComparisonState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpMappingConeComparisonDeclarationNames : List String :=
  ["mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison",
    "walkingParallelPairOp_mappingCone_objectComparisonBoundary",
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_objectBoundary",
    "currentWppOpMappingConeComparisonState"]

theorem wppOpMappingConeComparisonDeclarationNames_count :
    wppOpMappingConeComparisonDeclarationNames.length = 4 := rfl

section Checks

#check metrizableLCAWeakEquivalence
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison
#check walkingParallelPairOp_mappingCone_objectComparisonBoundary
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_objectBoundary
#check currentWppOpMappingConeComparisonState
#check currentWppOpMappingConeComparisonState_productSuccess
#check wppOpMappingConeComparisonDeclarationNames
#check wppOpMappingConeComparisonDeclarationNames_count
#check exactAcyclic_of_iso
#check CochainComplex.mappingCone
#check BoundedComplexCategory.ι

end Checks

end WppOpMappingConeComparisonW276

end LeanLCAExactChallenge
