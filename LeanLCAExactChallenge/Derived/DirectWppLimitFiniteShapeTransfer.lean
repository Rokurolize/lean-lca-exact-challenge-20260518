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
open Topology

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

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/-- WPP limits preserve the left closed-embedding field of strict short complexes. -/
abbrev wppLimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- WPP limits preserve the right open-map field of strict short complexes. -/
abbrev wppLimit_preserves_rightOpenMap : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) →
        IsLimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCone cs) →
          (∀ j : WalkingParallelPair,
            IsOpenMap ((S.obj j).g : (S.obj j).X₂ → (S.obj j).X₃)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- WPP limits preserve right surjectivity for strict short complexes. -/
abbrev rightSurjective_walkingParallelPair_limitClosure : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Direct algebraic exactness at the WPP limit point. -/
abbrev algebraicExact_walkingParallelPair_limitClosure : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Left field consumer for the WPP limit-closure route. -/
theorem leftClosedEmbedding_walkingParallelPair_limitClosure_of_preserves
    (hpres : wppLimit_preserves_leftClosedEmbedding) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) := by
  intro S cs hcs hS
  exact hpres S cs hcs (fun j => (hS j).closed_inclusion)

/-- Right-open field consumer for the WPP limit-closure route. -/
theorem rightOpenMap_walkingParallelPair_limitClosure_of_preserves
    (hpres : wppLimit_preserves_rightOpenMap) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) := by
  intro S cs hcs hS
  exact hpres S cs
    (isLimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isLimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- Strict exactness at WPP limits from the four short-complex field inputs. -/
theorem strictShortExact_walkingParallelPair_limitClosure_of_fields
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            MetrizableLCA.strictShortExact cs.pt := by
  intro S cs hcs hS
  exact
    { closed_inclusion :=
        leftClosedEmbedding_walkingParallelPair_limitClosure_of_preserves
          hleft S cs hcs hS
      open_map :=
        rightOpenMap_walkingParallelPair_limitClosure_of_preserves
          hrightOpen S cs hcs hS
      surjective := hrightSurj S cs hcs hS
      algebraic_exact := halg S cs hcs hS }

/-- WPP exact-acyclic limit closure from four short-complex field inputs. -/
theorem exactAcyclic_walkingParallelPair_limitClosure_of_fields
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure := by
  intro K ck hck hK i
  let S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0} :=
    K ⋙ degreeShortComplexFunctor i
  let cs : Cone S := (degreeShortComplexFunctor i).mapCone ck
  have hcs : IsLimit cs := by
    refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).prev i)) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) i) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).next i)) hck)
  have hS : ∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j) := by
    intro j
    exact hK j i
  exact strictShortExact_walkingParallelPair_limitClosure_of_fields
    hleft hrightOpen hrightSurj halg S cs hcs hS

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

/-- Direct WPP limit stability from comparison and short-complex limit field inputs. -/
theorem directWalkingParallelPairLimitStability_of_comparison_and_limitFields
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitStability :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison
    (exactAcyclic_walkingParallelPair_limitClosure_of_fields
      hleft hrightOpen hrightSurj halg)

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

abbrev MetrizableWppLimitLeftClosedInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_preserves_leftClosedEmbedding

abbrev MetrizableWppLimitRightOpenInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_preserves_rightOpenMap

abbrev MetrizableWppLimitRightSurjectiveInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.rightSurjective_walkingParallelPair_limitClosure

abbrev MetrizableWppLimitAlgebraicExactInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.algebraicExact_walkingParallelPair_limitClosure

abbrev MetrizableWppOpExactAcyclicClosureInput : Prop :=
  exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure

abbrev MetrizableWppOpLeftClosedInput : Prop :=
  wppOp_lca_colimitMap_injective_inducing_closedImage

abbrev MetrizableWppOpSnakeInput : Prop :=
  addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable

/-- Four short-complex field inputs for WPP exact-acyclic limit closure. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputs : Type 1 where
  leftClosed : MetrizableWppLimitLeftClosedInput
  rightOpen : MetrizableWppLimitRightOpenInput
  rightSurjective : MetrizableWppLimitRightSurjectiveInput
  algebraicExact : MetrizableWppLimitAlgebraicExactInput

/-- Build WPP exact-acyclic limit closure from the four short-complex field inputs. -/
theorem metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputs) :
    MetrizableWppLimitClosureInput :=
  exactAcyclic_walkingParallelPair_limitClosure_of_fields
    inputs.leftClosed
    inputs.rightOpen
    inputs.rightSurjective
    inputs.algebraicExact

theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
    (hcomparison : MetrizableWppLimitComparisonInput)
    (hclosure : MetrizableWppLimitClosureInput) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison hclosure

/-- Build WPP limit stability from comparison and short-complex closure fields. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputs) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitFields
    hcomparison
    inputs.leftClosed
    inputs.rightOpen
    inputs.rightSurjective
    inputs.algebraicExact

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

/--
W532 finite-shape transfer inputs with WPP limit closure supplied by four
short-complex field inputs and WPP colimit stability supplied by WPP-op closure.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndOpClosure :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitFields : MetrizableWalkingParallelPairLimitClosureFieldInputs
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit fields and WPP-op closure. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitFieldsAndOpClosure
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndOpClosure) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
      inputs.limitComparison
      inputs.limitFields
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
      inputs.opExactAcyclicClosure
  functorCategoryLocalization := inputs.functorCategoryLocalization

/--
W532 finite-shape transfer inputs with WPP limit closure supplied by four
short-complex field inputs and WPP colimit stability supplied by the left/Snake route.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndLeftSnake :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitFields : MetrizableWalkingParallelPairLimitClosureFieldInputs
  leftClosed : MetrizableWppOpLeftClosedInput
  snake : MetrizableWppOpSnakeInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit fields and the left/Snake route. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitFieldsAndLeftSnake
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndLeftSnake) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
      inputs.limitComparison
      inputs.limitFields
  colimitStability :=
    walkingParallelPairColimitStability_of_left_and_snakeCokernel
      inputs.leftClosed inputs.snake
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- Input names for the direct-limit-field plus WPP-op closure transfer form. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP limit left closed-embedding field",
    "WPP limit right open-map field",
    "WPP limit right-surjectivity field",
    "WPP limit algebraic exactness field",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames.length =
      7 :=
  rfl

/-- Input names for the direct-limit-field plus left/Snake transfer form. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP limit left closed-embedding field",
    "WPP limit right open-map field",
    "WPP limit right-surjectivity field",
    "WPP limit algebraic exactness field",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames.length =
      8 :=
  rfl

end Dbounded

end LeanLCAExactChallenge
