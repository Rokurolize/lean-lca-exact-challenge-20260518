import LeanLCAExactChallenge.Derived.DirectWppOpColimitFiniteShapeTransfer

/-!
WPP limit stability as a finite-shape transfer input.

This module records the direct route from a cochain-level WPP limit comparison and
exact-acyclic WPP limit closure to the `WalkingParallelPair` limit-stability field
used by the `Dbounded` finite-shape transfer constructor.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DirectWppLimitFiniteShapeTransfer

/-- The direct bounded exact weak-equivalence property for default-universe metrizable LCAs. -/
abbrev directWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- Direct WPP limit stability for bounded exact weak equivalences. -/
abbrev DirectWalkingParallelPairLimitStability : Prop :=
  directWeakEquivalence.IsStableUnderLimitsOfShape WalkingParallelPair

/-- Constructor-level condition for direct WPP limit stability. -/
abbrev DirectWalkingParallelPairLimitCondition : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPair f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPair,
            φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
              directWeakEquivalence φ

/-- Mapping-cone comparison input for WPP limit comparison maps. -/
abbrev mappingCone_boundedInclusion_walkingParallelPair_limitComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPair f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPair,
            φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
            ∃ (K : WalkingParallelPair ⥤ CochainComplex MetrizableLCA.{0} ℤ)
              (ck : Cone K),
                Nonempty (IsLimit ck) ∧
                  (∀ j : WalkingParallelPair,
                    exactAcyclic MetrizableLCA (K.obj j)) ∧
                  Nonempty
                    (CochainComplex.mappingCone
                        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/-- Exact-acyclic WPP limit closure input for cochain complexes. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure : Prop :=
  ∀ (K : WalkingParallelPair ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cone K),
      IsLimit ck →
        (∀ j : WalkingParallelPair, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/-- Comparison and closure prove exact acyclicity of a WPP limit comparison cone. -/
theorem exactAcyclic_mappingCone_of_walkingParallelPair_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure)
    (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂) (f : X₁ ⟶ X₂)
    (hf : directWeakEquivalence.functorCategory WalkingParallelPair f)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPair,
      φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)) := by
  rcases hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ with
    ⟨K, ck, ⟨hck⟩, hK, ⟨e⟩⟩
  exact exactAcyclic_of_iso MetrizableLCA e.symm (hclosure K ck hck hK)

/-- The comparison and closure inputs supply the direct WPP limit constructor condition. -/
theorem directWalkingParallelPairLimitCondition_of_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitCondition := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  exact
    exactAcyclic_mappingCone_of_walkingParallelPair_comparison_and_limitClosure
      hcomparison hclosure X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ

/-- Direct WPP limit stability from comparison and exact-acyclic closure. -/
theorem directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitStability :=
  MorphismProperty.IsStableUnderLimitsOfShape.mk
    (directWalkingParallelPairLimitCondition_of_comparison_and_limitClosure
      hcomparison hclosure)

/-- Machine-readable state for the WPP limit transfer bridge. -/
structure DirectWppLimitFiniteShapeTransferState : Type where
  seed : String
  provedConsumer : String
  pendingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible state for the WPP limit transfer bridge. -/
def currentDirectWppLimitFiniteShapeTransferState :
    DirectWppLimitFiniteShapeTransferState where
  seed := "w541-direct-wpp-limit-finite-shape-transfer"
  provedConsumer := "directWalkingParallelPairLimitStability_of_comparison_and_limitClosure"
  pendingInputs :=
    ["mapping-cone WPP limit comparison",
      "WPP exact-acyclic limit closure"]
  productSuccessClaimed := false

theorem currentDirectWppLimitFiniteShapeTransferState_productSuccess :
    currentDirectWppLimitFiniteShapeTransferState.productSuccessClaimed = false := rfl

end DirectWppLimitFiniteShapeTransfer

namespace Dbounded

open DirectWppLimitFiniteShapeTransfer
open DirectWppOpColimitFiniteShapeTransfer
open WppOpExactAcyclicFrontierConsolidatedW318

abbrev MetrizableWppLimitComparisonInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.mappingCone_boundedInclusion_walkingParallelPair_limitComparison

abbrev MetrizableWppLimitClosureInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure

abbrev MetrizableWppOpExactAcyclicClosureInput : Prop :=
  exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure

abbrev MetrizableWppOpLeftClosedInput : Prop :=
  wppOp_lca_colimitMap_injective_inducing_closedImage

abbrev MetrizableWppOpSnakeInput : Prop :=
  addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable

theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
    (hcomparison : MetrizableWppLimitComparisonInput)
    (hclosure : MetrizableWppLimitClosureInput) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison hclosure

/--
W532 finite-shape transfer inputs with WPP limit stability supplied by direct
limit comparison and WPP colimit stability supplied by WPP-op closure.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndOpClosure :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit data and WPP-op colimit closure. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitAndOpClosure
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndOpClosure) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
      inputs.limitComparison
      inputs.limitClosure
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
      inputs.opExactAcyclicClosure
  functorCategoryLocalization := inputs.functorCategoryLocalization

/--
W532 finite-shape transfer inputs with WPP limit stability supplied by direct
limit comparison and WPP colimit stability supplied by the left/Snake route.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndLeftSnake :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  leftClosed : MetrizableWppOpLeftClosedInput
  snake : MetrizableWppOpSnakeInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit data and the left/Snake route. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitAndLeftSnake
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndLeftSnake) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
      inputs.limitComparison
      inputs.limitClosure
  colimitStability :=
    walkingParallelPairColimitStability_of_left_and_snakeCokernel
      inputs.leftClosed inputs.snake
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- Input names for the direct-limit plus WPP-op closure form of W532 finite-shape transfer. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP exact-acyclic limit closure",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames.length = 4 :=
  rfl

/-- Input names for the direct-limit plus left/Snake form of W532 finite-shape transfer. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP exact-acyclic limit closure",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames.length = 5 :=
  rfl

end Dbounded

end LeanLCAExactChallenge
