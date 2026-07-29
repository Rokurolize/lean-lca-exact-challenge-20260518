/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationNilPositiveComposition

/-! # Zero-left/positive-right summand composition

This module lifts the normalized boundary calculation to the full corrected Drinfeld summand.
The zero-word factor composes with the positive head while the recursive positive tail is carried
through unchanged.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

private theorem nilPositiveSummandCastWord_hom_eqToHom
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    ∃ hM : summandModule d = summandModule (d.castWord h),
      (summandModuleCastWordIso h d).hom = eqToHom hM := by
  subst v
  exact ⟨rfl, rfl⟩

private theorem nilPositiveSummandComp_eqToHom
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : ∃ h : A = B, f = eqToHom h)
    (hg : ∃ h : B = C, g = eqToHom h) :
    ∃ h : A = C, f ≫ g = eqToHom h := by
  obtain ⟨hAB, rfl⟩ := hf
  obtain ⟨hBC, rfl⟩ := hg
  exact ⟨hAB.trans hBC, by simp⟩

private theorem nilPositiveSummandIso_hom_eqToHom
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    ∃ h : summandModule ((nilDegreeProfile W X p).append d) =
        factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ⊗
          summandModule (tailDegreeProfile d),
      (nilPositiveSummandIso (W := W) p d).hom = eqToHom h := by
  obtain ⟨hcast, hhcast⟩ := nilPositiveSummandCastWord_hom_eqToHom
    (nilAppendPositiveWord_eq intermediate)
    ((nilDegreeProfile W X p).append d)
  obtain ⟨htail, hhtail⟩ := nilPositiveTailSummandIso_hom_eqToHom
    (W := W) p d
  have htensor : ∃ h,
      (𝟙 (factorModule (nilPositiveDegreeProfile (W := W) p d) 0) ⊗ₘ
          (nilPositiveTailSummandIso (W := W) p d).hom) = eqToHom h := by
    rw [hhtail]
    exact ⟨congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) rfl htail,
      by simp⟩
  have hfirst : ∃ h,
      (summandModuleCastWordIso (nilAppendPositiveWord_eq intermediate)
          ((nilDegreeProfile W X p).append d)).hom ≫
        eqToHom (summandModule_succ
          (nilPositiveDegreeProfile (W := W) p d)) = eqToHom h :=
    nilPositiveSummandComp_eqToHom _ _ ⟨hcast, hhcast⟩ ⟨_, rfl⟩
  unfold nilPositiveSummandIso
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom,
    eqToIso.hom]
  rw [← Category.assoc]
  exact nilPositiveSummandComp_eqToHom _ _ hfirst htensor

/-- After replacing the merged boundary factor, the remaining factor list is the original
positive tail summand. -/
def nilPositiveTargetTailEq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tensorModuleList
        (factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ::
          compositionRightSuffix d) =
      factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ⊗
        summandModule (tailDegreeProfile d) :=
  congrArg
    (fun xs : List (ModuleCat.{0} ℤ) ↦
      factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ⊗
        tensorModuleList xs)
    (finFamilyList_factorModule_tail d)

/-- Equality between the generic right suffix and the original recursive tail summand. -/
def nilPositiveTailListEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tensorModuleList (compositionRightSuffix d) =
      summandModule (tailDegreeProfile d) :=
  congrArg tensorModuleList (finFamilyList_factorModule_tail d)

/-- Passing from positive head/tail coordinates to the generic first-factor coordinates only
transports the recursive tail list. -/
theorem nilPositiveRightSource_decompose
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (summandModule_succ d).symm ≫
        (summandFirstFactorIso d).hom =
      𝟙 (factorModule d 0) ⊗ₘ
        eqToHom (nilPositiveTailListEq d).symm := by
  have hfirst : (summandFirstFactorIso d).hom = 𝟙 (summandModule d) := by
    rfl
  rw [hfirst, Category.comp_id, summandModule_succ_symm_eqToHom]

/-- The generic composite-target transport is boundary replacement followed by restoration of
the original positive tail coordinates. -/
@[reassoc]
theorem nilPositiveTarget_transport
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary
          (nilDegreeProfile W X p) d).symm) ≫
        (nilPositiveSummandIso (W := W) p d).hom =
      (tensorMapDataReplaceAfter []
          (eqToHom (nilPositiveBoundaryModule_eq (W := W) p d))
          (compositionRightSuffix d)).tensorMap ≫
        eqToHom (nilPositiveTargetTailEq (W := W) p d) := by
  rw [tensorMapDataReplaceAfter_eqToHom]
  obtain ⟨hiso, hhiso⟩ := nilPositiveSummandIso_hom_eqToHom
    (W := W) p d
  rw [hhiso]
  simp only [eqToHom_trans]

/-- The final target-list transport acts as the identity on the normalized head and restores the
original recursive tail. -/
theorem nilPositiveTargetTailEq_eqToHom
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (nilPositiveTargetTailEq (W := W) p d) =
      𝟙 (factorModule (nilPositiveDegreeProfile (W := W) p d) 0) ⊗ₘ
        eqToHom (nilPositiveTailListEq d) := by
  rw [Subsingleton.elim (nilPositiveTargetTailEq (W := W) p d)
    (congrArg
      (fun Q : ModuleCat.{0} ℤ ↦
        factorModule (nilPositiveDegreeProfile (W := W) p d) 0 ⊗ Q)
      (nilPositiveTailListEq d))]
  exact tensor_obj_eqToHom
    (factorModule (nilPositiveDegreeProfile (W := W) p d) 0)
    (nilPositiveTailListEq d)

/-- The adjacent boundary merge followed by target normalization is normalized head composition
tensored with restoration of the recursive tail. -/
@[reassoc]
theorem nilPositiveBoundaryTailMap
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (adjacentMergeAfter [] (ys := compositionRightSuffix d)
        (compositionBoundaryMap (nilDegreeProfile W X p) d)).tensorMap ≫
      (tensorMapDataReplaceAfter []
        (eqToHom (nilPositiveBoundaryModule_eq (W := W) p d))
        (compositionRightSuffix d)).tensorMap ≫
      eqToHom (nilPositiveTargetTailEq (W := W) p d) =
    (α_ (factorModule (nilDegreeProfile W X p) 0) (factorModule d 0)
      (tensorModuleList (compositionRightSuffix d))).inv ≫
      (nilPositiveHeadCompositionMap (W := W) p d ⊗ₘ
        eqToHom (nilPositiveTailListEq d)) := by
  rw [adjacentMergeAfter_tensorMap_post_assoc]
  change (α_ (factorModule (nilDegreeProfile W X p) 0) (factorModule d 0)
      (tensorModuleList (compositionRightSuffix d))).inv ≫
      ((compositionBoundaryMap (nilDegreeProfile W X p) d ≫
          eqToHom (nilPositiveBoundaryModule_eq (W := W) p d)) ⊗ₘ
        𝟙 (tensorModuleList (compositionRightSuffix d))) ≫
      eqToHom (nilPositiveTargetTailEq (W := W) p d) = _
  rw [nilPositiveTargetTailEq_eqToHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp]
  rfl

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
