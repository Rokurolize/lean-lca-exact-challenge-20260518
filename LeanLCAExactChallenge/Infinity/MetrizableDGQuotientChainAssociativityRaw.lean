/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainLaws

/-! # Raw associativity for the smart-truncated corrected quotient enrichment -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

lemma quotientTruncatedCompositionComponent_to_raw
    (K L M : CorrectedQuotientDGCategory)
    {p q n : ℕ} (h : p + q = n) :
    quotientTruncatedMapComponent (quotientDGEnrichedComp K L M) h ≫
        ((quotientDGEnrichedHom K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((quotientDGEnrichedHom K L).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((quotientDGEnrichedHom L M).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f q) ≫
        quotientDGCompositionComponent
          (show ComplexCategoryᵒᵖ from M).unop
          (show ComplexCategoryᵒᵖ from L).unop
          (show ComplexCategoryᵒᵖ from K).unop (by
          change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
          omega) := by
  rw [quotientTruncatedMapComponent_toRestriction]
  dsimp only [quotientTruncatedMapToCochain, quotientDGEnrichedComp,
    quotientDGEnrichedHom]
  simp only [Category.assoc]
  congr 1
  exact ιTensorObj_quotientDGComposition
    (show ComplexCategoryᵒᵖ from M).unop
    (show ComplexCategoryᵒᵖ from L).unop
    (show ComplexCategoryᵒᵖ from K).unop (by
      change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
      omega)

private lemma quotientCompositionMap_cast_right_natNeg
    (X Y Z : ComplexCategory) {n m m' : ℤ} (h : m = m')
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    quotientCompositionMap X Y Z n m' x
        ((eqToHom (congrArg (quotientGradedModule Y Z) h)).hom y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (congrArg (fun k ↦ n + k) h))).hom
          (quotientCompositionMap X Y Z n m x y) := by
  subst m'
  rfl

private lemma quotientCompositionMap_cast_left_natNeg
    (X Y Z : ComplexCategory) {n n' m : ℤ} (h : n = n')
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    quotientCompositionMap X Y Z n' m
        ((eqToHom (congrArg (quotientGradedModule X Y) h)).hom x) y =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (congrArg (fun k ↦ k + m) h))).hom
          (quotientCompositionMap X Y Z n m x y) := by
  subst n'
  rfl

set_option maxHeartbeats 2000000 in
-- The expanded threefold tensor calculation requires additional elaboration budget.
theorem quotientDGCompositionComponent_assoc_natNeg
    (W X Y Z : ComplexCategory) {p q r n : ℕ} (h : p + q + r = n) :
    (α_ ((QuotientMappingCochain X W).X (-(p : ℤ)))
          ((QuotientMappingCochain Y X).X (-(q : ℤ)))
          ((QuotientMappingCochain Z Y).X (-(r : ℤ)))).inv ≫
        (quotientDGCompositionComponent Y X W
              (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega) ⊗ₘ
            𝟙 ((QuotientMappingCochain Z Y).X (-(r : ℤ)))) ≫
        quotientDGCompositionComponent Z Y W
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega) =
      (𝟙 ((QuotientMappingCochain X W).X (-(p : ℤ))) ⊗ₘ
          quotientDGCompositionComponent Z Y X
            (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega)) ≫
        quotientDGCompositionComponent Z X W
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro a b c
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases c with ⟨c⟩
  change quotientGradedModule X W (-(p : ℤ)) at a
  change quotientGradedModule Y X (-(q : ℤ)) at b
  change quotientGradedModule Z Y (-(r : ℤ)) at c
  change
    quotientDGCompositionComponent Z Y W
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega)
        ((quotientDGCompositionComponent Y X W
              (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega) ⊗ₘ
            𝟙 ((QuotientMappingCochain Z Y).X (-(r : ℤ))))
          ((α_ ((QuotientMappingCochain X W).X (-(p : ℤ)))
            ((QuotientMappingCochain Y X).X (-(q : ℤ)))
            ((QuotientMappingCochain Z Y).X (-(r : ℤ)))).inv
              (ULift.up a ⊗ₜ[QuotientCoefficientRing]
                (ULift.up b ⊗ₜ[QuotientCoefficientRing] ULift.up c)))) =
      quotientDGCompositionComponent Z X W
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega)
        ((𝟙 ((QuotientMappingCochain X W).X (-(p : ℤ))) ⊗ₘ
            quotientDGCompositionComponent Z Y X
              (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega))
          (ULift.up a ⊗ₜ[QuotientCoefficientRing]
            (ULift.up b ⊗ₜ[QuotientCoefficientRing] ULift.up c)))
  change
    quotientDGCompositionComponent Z Y W
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega)
        (quotientDGCompositionComponent Y X W
            (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega)
              (ULift.up a ⊗ₜ[QuotientCoefficientRing] ULift.up b) ⊗ₜ
            ULift.up c) =
      quotientDGCompositionComponent Z X W
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega)
        (ULift.up a ⊗ₜ
          quotientDGCompositionComponent Z Y X
            (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega)
              (ULift.up b ⊗ₜ[QuotientCoefficientRing] ULift.up c))
  simp only [quotientDGCompositionComponent, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  change
    (eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule Z W k))
        ((Int.add_comm (-(r : ℤ)) (-((p + q : ℕ) : ℤ))).trans
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega)))).hom
      ((quotientCompositionTensorMap Z Y W (-(r : ℤ)) (-((p + q : ℕ) : ℤ))).hom
        (ULift.up c ⊗ₜ[QuotientCoefficientRing]
          (eqToHom (congrArg
            (fun k ↦ quotientCoefficientModule (quotientGradedModule Y W k))
            ((Int.add_comm (-(q : ℤ)) (-(p : ℤ))).trans
              (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega)))).hom
              ((quotientCompositionTensorMap Y X W (-(q : ℤ)) (-(p : ℤ))).hom
                (ULift.up b ⊗ₜ[QuotientCoefficientRing] ULift.up a)))) =
      (eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule Z W k))
        ((Int.add_comm (-((q + r : ℕ) : ℤ)) (-(p : ℤ))).trans
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega)))).hom
        ((quotientCompositionTensorMap Z X W (-((q + r : ℕ) : ℤ)) (-(p : ℤ))).hom
          ((eqToHom (congrArg
            (fun k ↦ quotientCoefficientModule (quotientGradedModule Z X k))
            ((Int.add_comm (-(r : ℤ)) (-(q : ℤ))).trans
              (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega)))).hom
              ((quotientCompositionTensorMap Z Y X (-(r : ℤ)) (-(q : ℤ))).hom
                (ULift.up c ⊗ₜ[QuotientCoefficientRing] ULift.up b)) ⊗ₜ
            ULift.up a))
  rw [quotientCompositionTensorMap_tmul,
    quotientCoefficient_eqToHom_apply_up,
    quotientCompositionTensorMap_tmul,
    quotientCoefficient_eqToHom_apply_up,
    quotientCompositionTensorMap_tmul,
    quotientCoefficient_eqToHom_apply_up,
    quotientCompositionTensorMap_tmul,
    quotientCoefficient_eqToHom_apply_up]
  · apply ULift.down_injective
    rw [quotientCompositionMap_cast_right_natNeg,
      quotientCompositionMap_cast_left_natNeg]
    · have hassoc := congrArg
        (fun t ↦ (eqToHom (congrArg (quotientGradedModule Z W)
          (show (-(r : ℤ)) + ((-(q : ℤ)) + (-(p : ℤ))) = -(n : ℤ) by omega))).hom t)
        (quotientCompositionMap_assoc Z Y X W
          (-(r : ℤ)) (-(q : ℤ)) (-(p : ℤ)) c b a)
      simpa only [← ModuleCat.comp_apply, eqToHom_trans] using hassoc.symm
    all_goals omega
  all_goals omega

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
