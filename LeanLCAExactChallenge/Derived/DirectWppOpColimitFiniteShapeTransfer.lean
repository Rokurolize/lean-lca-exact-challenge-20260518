import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.Derived.WppOpMappingConeUniqueMediator
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
WPP-op colimit stability as a finite-shape transfer input.

This module connects the WPP-op mapping-cone colimit closure route to the
`WalkingParallelPair` colimit-stability field used by the `Dbounded`
finite-shape transfer constructor.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

universe w w' v u

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Colimit stability of a morphism property transports across an equivalence of shapes. -/
theorem isStableUnderColimitsOfShape_of_shapeEquivalence
    (W : MorphismProperty C) {J : Type w} {J' : Type w'} [Category J] [Category J']
    (e : J ≌ J') [W.IsStableUnderColimitsOfShape J] :
    W.IsStableUnderColimitsOfShape J' := by
  rw [isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  rw [← W.colimitsOfShape_eq_of_equivalence e]
  exact colimitsOfShape_le

end MorphismProperty

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace DirectWppOpColimitFiniteShapeTransfer

/-- The direct bounded exact weak-equivalence property for default-universe metrizable LCAs. -/
abbrev directWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- Direct WPP-op colimit stability for bounded exact weak equivalences. -/
abbrev DirectWalkingParallelPairOpColimitStability : Prop :=
  directWeakEquivalence.IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ

/-- Constructor-level condition for direct WPP-op colimit stability. -/
abbrev DirectWalkingParallelPairOpColimitCondition : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPairᵒᵖ f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPairᵒᵖ,
            c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
              directWeakEquivalence φ

/-- Mapping-cone comparison input for WPP-op colimit comparison maps. -/
abbrev mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPairᵒᵖ f →
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

/-- Exact-acyclic WPP-op colimit closure input for cochain complexes. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        (∀ j : WalkingParallelPairᵒᵖ, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/-- The included-colimit mapping-cone construction supplies the comparison input. -/
theorem mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison_of_includedColimits :
    mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  let K := WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f
  let ck := WppOpMappingConeUniqueMediatorW308.mappingConeCocone c₁ c₂ f φ hφ
  have huniq :=
    WppOpMappingConeUniqueMediatorW308.uniqueMediatingInput_of_includedColimits
      (X₁ := X₁) (X₂ := X₂) (c₁ := c₁) (c₂ := c₂) (f := f)
      (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₁)
      hc₂ φ hφ
  have hck : IsColimit ck :=
    { desc := fun s => Classical.choose (huniq s)
      fac := by
        intro s j
        exact (Classical.choose_spec (huniq s)).1 j
      uniq := by
        intro s m hm
        exact (Classical.choose_spec (huniq s)).2 m hm }
  refine ⟨K, ck, ⟨hck⟩, ?_, ?_⟩
  · intro j
    exact hf j
  · exact ⟨Iso.refl _⟩

/-- Comparison and closure prove exact acyclicity of a WPP-op colimit comparison cone. -/
theorem exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure)
    (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (hf : directWeakEquivalence.functorCategory WalkingParallelPairᵒᵖ f)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)) := by
  rcases hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ with
    ⟨K, ck, ⟨hck⟩, hK, ⟨e⟩⟩
  exact exactAcyclic_of_iso MetrizableLCA e.symm (hclosure K ck hck hK)

/-- The comparison and closure inputs supply the direct WPP-op constructor condition. -/
theorem directWalkingParallelPairOpColimitCondition_of_comparison_and_closure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure) :
    DirectWalkingParallelPairOpColimitCondition := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  exact
    exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure
      hcomparison hclosure X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ

/-- With included colimits, the exact-acyclic closure input supplies the constructor condition. -/
theorem directWalkingParallelPairOpColimitCondition_of_includedComparison_and_closure
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure) :
    DirectWalkingParallelPairOpColimitCondition :=
  directWalkingParallelPairOpColimitCondition_of_comparison_and_closure
    mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison_of_includedColimits
    hclosure

/-- Direct WPP-op colimit stability from comparison and exact-acyclic closure. -/
theorem directWalkingParallelPairOpColimitStability_of_comparison_and_closure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure) :
    DirectWalkingParallelPairOpColimitStability :=
  MorphismProperty.IsStableUnderColimitsOfShape.mk
    (directWalkingParallelPairOpColimitCondition_of_comparison_and_closure
      hcomparison hclosure)

/-- Direct WPP-op colimit stability from exact-acyclic closure. -/
theorem directWalkingParallelPairOpColimitStability_of_exactAcyclicClosure
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure) :
    DirectWalkingParallelPairOpColimitStability :=
  directWalkingParallelPairOpColimitStability_of_comparison_and_closure
    mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison_of_includedColimits
    hclosure

/-- Direct WPP-op colimit stability from the left topological certificate and SnakeInput route. -/
theorem directWalkingParallelPairOpColimitStability_of_left_and_snakeCokernel
    (hclosed :
      WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hsnake :
      WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    DirectWalkingParallelPairOpColimitStability :=
  directWalkingParallelPairOpColimitStability_of_exactAcyclicClosure
    (WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel
      hclosed hsnake)

/-- Convert direct WPP-op colimit stability into the WPP colimit-stability shape. -/
theorem walkingParallelPairColimitStability_of_op
    (h : DirectWalkingParallelPairOpColimitStability) :
    directWeakEquivalence.IsStableUnderColimitsOfShape WalkingParallelPair := by
  letI : directWeakEquivalence.IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ := h
  exact MorphismProperty.isStableUnderColimitsOfShape_of_shapeEquivalence
    directWeakEquivalence walkingParallelPairOpEquiv.symm

/-- Direct WPP colimit stability from exact-acyclic WPP-op colimit closure. -/
theorem walkingParallelPairColimitStability_of_exactAcyclicClosure
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure) :
    directWeakEquivalence.IsStableUnderColimitsOfShape WalkingParallelPair :=
  walkingParallelPairColimitStability_of_op
    (directWalkingParallelPairOpColimitStability_of_exactAcyclicClosure hclosure)

/-- Direct WPP colimit stability from the left topological certificate and SnakeInput route. -/
theorem walkingParallelPairColimitStability_of_left_and_snakeCokernel
    (hclosed :
      WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hsnake :
      WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    directWeakEquivalence.IsStableUnderColimitsOfShape WalkingParallelPair :=
  walkingParallelPairColimitStability_of_op
    (directWalkingParallelPairOpColimitStability_of_left_and_snakeCokernel hclosed hsnake)

/-- Machine-readable state for the WPP-op colimit transfer bridge. -/
structure DirectWppOpColimitFiniteShapeTransferState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible state for the WPP-op colimit transfer bridge. -/
def currentDirectWppOpColimitFiniteShapeTransferState :
    DirectWppOpColimitFiniteShapeTransferState where
  seed := "w533-20260521T160122Z-c0c590f0fd0aa842"
  provedConsumer := "walkingParallelPairColimitStability_of_left_and_snakeCokernel"
  remainingInputs :=
    ["wppOp_lca_colimitMap_injective_inducing_closedImage",
      "addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable"]
  productSuccessClaimed := false

theorem currentDirectWppOpColimitFiniteShapeTransferState_productSuccess :
    currentDirectWppOpColimitFiniteShapeTransferState.productSuccessClaimed = false := rfl

end DirectWppOpColimitFiniteShapeTransfer

namespace Dbounded

/-- W532 finite-shape transfer inputs with WPP colimit stability supplied by WPP-op closure. -/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromOpClosure : Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  opExactAcyclicClosure :
    DirectWppOpColimitFiniteShapeTransfer.exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from WPP-op exact-acyclic closure. -/
noncomputable def metrizableWalkingParallelPairFiniteShapeTransferInputs_of_opClosure
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromOpClosure) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
      inputs.opExactAcyclicClosure
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- W532 finite-shape transfer inputs with WPP colimit stability supplied by the left/Snake route. -/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLeftSnake : Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  leftClosed :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage
  snake :
    WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from the left topological certificate and SnakeInput route. -/
noncomputable def metrizableWalkingParallelPairFiniteShapeTransferInputs_of_leftSnake
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLeftSnake) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_left_and_snakeCokernel
      inputs.leftClosed inputs.snake
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- Input names for the exact-acyclic-closure form of W532 finite-shape transfer. -/
def metrizableWalkingParallelPairFiniteShapeTransferFromOpClosureInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization"]

theorem metrizableWalkingParallelPairFiniteShapeTransferFromOpClosureInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromOpClosureInputNames.length = 3 :=
  rfl

/-- Input names for the left/Snake form of W532 finite-shape transfer. -/
def metrizableWalkingParallelPairFiniteShapeTransferFromLeftSnakeInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "WalkingParallelPair functor-category localization"]

theorem metrizableWalkingParallelPairFiniteShapeTransferFromLeftSnakeInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLeftSnakeInputNames.length = 4 :=
  rfl

end Dbounded

section Checks

#check CategoryTheory.MorphismProperty.isStableUnderColimitsOfShape_of_shapeEquivalence
#check DirectWppOpColimitFiniteShapeTransfer.directWeakEquivalence
#check DirectWppOpColimitFiniteShapeTransfer.DirectWalkingParallelPairOpColimitStability
#check DirectWppOpColimitFiniteShapeTransfer.DirectWalkingParallelPairOpColimitCondition
#check DirectWppOpColimitFiniteShapeTransfer.mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison
#check DirectWppOpColimitFiniteShapeTransfer.exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure
#check DirectWppOpColimitFiniteShapeTransfer.mappingCone_boundedInclusion_walkingParallelPairOp_colimitComparison_of_includedColimits
#check DirectWppOpColimitFiniteShapeTransfer.directWalkingParallelPairOpColimitStability_of_exactAcyclicClosure
#check DirectWppOpColimitFiniteShapeTransfer.directWalkingParallelPairOpColimitStability_of_left_and_snakeCokernel
#check DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_op
#check DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
#check DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_left_and_snakeCokernel
#check DirectWppOpColimitFiniteShapeTransfer.currentDirectWppOpColimitFiniteShapeTransferState
#check DirectWppOpColimitFiniteShapeTransfer.currentDirectWppOpColimitFiniteShapeTransferState_productSuccess
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromOpClosure
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_opClosure
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLeftSnake
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_leftSnake
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferFromOpClosureInputNames
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferFromOpClosureInputNames_count
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferFromLeftSnakeInputNames
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferFromLeftSnakeInputNames_count

end Checks

end LeanLCAExactChallenge
