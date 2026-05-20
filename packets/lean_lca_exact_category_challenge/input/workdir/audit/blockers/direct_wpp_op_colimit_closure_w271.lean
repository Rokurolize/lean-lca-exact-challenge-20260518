import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W271: direct `WalkingParallelPairᵒᵖ` colimit-closure boundary.

W265 isolated the categorical constructor input for direct colimit stability of
`boundedExactWeakEquivalence MetrizableLCA`. This file moves that boundary down one layer:
it names the mapping-cone comparison and exact-acyclic `WalkingParallelPairᵒᵖ` colimit
closure facts whose combination gives the W265/W266 direct input.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace DirectWalkingParallelPairOpColimitClosureW271

/-- The direct bounded exact weak-equivalence class for metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- The direct theorem left open by W265/W266. -/
abbrev MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget : Prop :=
  (metrizableLCAWeakEquivalence).IsStableUnderColimitsOfShape WalkingParallelPairᵒᵖ

/--
The exact constructor-level condition needed by
`MorphismProperty.IsStableUnderColimitsOfShape.mk` for the direct WPP-op target.
-/
abbrev MetrizableLCADirectWalkingParallelPairOpColimitConditionInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      (metrizableLCAWeakEquivalence).functorCategory WalkingParallelPairᵒᵖ f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPairᵒᵖ,
            c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
              metrizableLCAWeakEquivalence φ

/--
The comparison input still missing below W265.

For every colimit comparison map `φ` between bounded-complex WPP-op colimits, this asks for
a concrete WPP-op diagram of cochain complexes whose colimit object is isomorphic to the
mapping cone of the bounded inclusion image of `φ`. The component exactness hypothesis is
the objectwise weak-equivalence input transported to that comparison diagram.
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
The exact-acyclic closure input still missing below W265.

This is now stated on the concrete cochain-complex colimit supplied by the comparison input,
rather than on bounded weak equivalences or opposite localization data.
-/
abbrev exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        (∀ j : WalkingParallelPairᵒᵖ, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/--
The two lower-level inputs prove exact acyclicity of the mapping cone of the colimit comparison
map selected by the WPP-op cocone data.
-/
theorem exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure
    (hcomparison : mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure)
    (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (hf : (metrizableLCAWeakEquivalence).functorCategory WalkingParallelPairᵒᵖ f)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)) := by
  rcases hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ with
    ⟨K, ck, ⟨hck⟩, hK, ⟨e⟩⟩
  exact exactAcyclic_of_iso MetrizableLCA e.symm (hclosure K ck hck hK)

/-- The comparison and closure inputs are exactly enough to supply the W265 constructor input. -/
theorem directWalkingParallelPairOpColimitConditionInput_of_comparison_and_closure
    (hcomparison : mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    MetrizableLCADirectWalkingParallelPairOpColimitConditionInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  exact
    exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure
      hcomparison hclosure X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ

/-- The checked consumer from the lower-level W271 inputs to the direct WPP-op stability target. -/
theorem metrizableLCA_directWalkingParallelPairOpColimitStability_of_comparison_and_closure
    (hcomparison : mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget :=
  MorphismProperty.IsStableUnderColimitsOfShape.mk
    (directWalkingParallelPairOpColimitConditionInput_of_comparison_and_closure
      hcomparison hclosure)

/-- Machine-readable frontier state for W271. -/
structure DirectWalkingParallelPairOpColimitClosureState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W271 boundary state. -/
def currentDirectWalkingParallelPairOpColimitClosureState :
    DirectWalkingParallelPairOpColimitClosureState where
  seed := "w271-20260520T150209Z-fed9bfa8800ecaf3"
  selectedRoute :=
    "direct WPP-op colimit closure via mapping-cone comparison plus exact-acyclic colimit closure"
  checkedBoundary :=
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison + exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure"
  provedConsumer :=
    "metrizableLCA_directWalkingParallelPairOpColimitStability_of_comparison_and_closure"
  remainingInputs :=
    ["mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison",
      "exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure"]
  productSuccessClaimed := false

theorem currentDirectWalkingParallelPairOpColimitClosureState_productSuccess :
    currentDirectWalkingParallelPairOpColimitClosureState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def directWalkingParallelPairOpColimitClosureDeclarationNames : List String :=
  ["mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison",
    "exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure",
    "exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure",
    "directWalkingParallelPairOpColimitConditionInput_of_comparison_and_closure",
    "metrizableLCA_directWalkingParallelPairOpColimitStability_of_comparison_and_closure",
    "currentDirectWalkingParallelPairOpColimitClosureState"]

theorem directWalkingParallelPairOpColimitClosureDeclarationNames_count :
    directWalkingParallelPairOpColimitClosureDeclarationNames.length = 6 := rfl

section Checks

#check metrizableLCAWeakEquivalence
#check MetrizableLCADirectWalkingParallelPairOpColimitStabilityTarget
#check MetrizableLCADirectWalkingParallelPairOpColimitConditionInput
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check exactAcyclic_mappingCone_of_walkingParallelPairOp_comparison_and_closure
#check directWalkingParallelPairOpColimitConditionInput_of_comparison_and_closure
#check metrizableLCA_directWalkingParallelPairOpColimitStability_of_comparison_and_closure
#check currentDirectWalkingParallelPairOpColimitClosureState
#check currentDirectWalkingParallelPairOpColimitClosureState_productSuccess
#check directWalkingParallelPairOpColimitClosureDeclarationNames
#check directWalkingParallelPairOpColimitClosureDeclarationNames_count
#check exactAcyclic_of_iso
#check MorphismProperty.IsStableUnderColimitsOfShape.mk

end Checks

end DirectWalkingParallelPairOpColimitClosureW271

end LeanLCAExactChallenge
