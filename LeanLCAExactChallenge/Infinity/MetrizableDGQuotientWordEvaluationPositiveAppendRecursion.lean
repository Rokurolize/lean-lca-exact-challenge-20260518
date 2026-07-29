/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationTargetTransport

/-! # Positive-append recursion for corrected Drinfeld word evaluation

This module expands evaluation of an appended positive word in the target tensor coordinates
shared with recursive summand composition.  On pure tensors, the expansion is the enriched
composition of the contracted head with the recursively evaluated appended tail.
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

/-- Word evaluation is natural under the inverse of a word cast. -/
theorem evaluateWord_castWord_inv_apply
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n)
    (x : summandModule (d.castWord h)) :
    E.evaluateWord w d ((summandModuleCastWordIso h d).inv.hom x) =
      E.evaluateWord v (d.castWord h) x := by
  have hcast := E.evaluateWord_castWord_apply h d
    ((summandModuleCastWordIso h d).inv.hom x)
  have hcancel := ConcreteCategory.congr_hom
    (summandModuleCastWordIso h d).inv_hom_id x
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  rw [hcancel] at hcast
  exact hcast.symm

/-- Evaluation of an appended positive word is recursive in the common composition target
coordinates. -/
theorem evaluateWord_positive_append_coordinates
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (E.evaluateWord
        (({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y).append v) (d.append e)).comp
      (positiveCompositionTargetIso d e).inv.hom =
    (E.evaluateSucc (positiveAppendDegreeProfile d e)
      (E.evaluateWord
        (tailWord (Y := Z)
          (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v))
        (tailDegreeProfile (positiveAppendDegreeProfile d e)))).comp
      (((MonoidalCategory.tensorIso
          (eqToIso (positiveAppendFactorModule_zero d e))
          (positiveAppendTailSummandIso d e)).inv ≫
        (eqToIso (summandModule_succ
          (positiveAppendDegreeProfile d e))).inv).hom) := by
  have hIso : positiveAppendSummandIso d e =
      positiveCompositionTargetIso d e := by
    apply Iso.ext
    exact positiveAppendSummandIso_hom_eq_positiveCompositionTargetIso_hom d e
  rw [← hIso]
  unfold positiveAppendSummandIso
  simp only [Iso.trans_inv]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, ModuleCat.comp_apply]
  rw [E.evaluateWord_castWord_inv_apply]
  unfold positiveAppendWord
  rw [E.evaluateWord_succ_eq]
  rfl

/-- On pure head/tail tensors, positive-append evaluation is the enriched composition of the
contracted head with the recursively evaluated appended tail. -/
theorem evaluateWord_positive_append_apply_tensor
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0)
    (t : summandModule ((tailDegreeProfile d).append e)) :
    E.evaluateWord
        (({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y).append v) (d.append e)
        ((positiveCompositionTargetIso d e).inv.hom (x ⊗ₜ[ℤ] t)) =
      E.composeElement X
        (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v 0).obj Z
        (-1 + (positiveAppendDegreeProfile d e).arrowDegree 0)
        (tailDegree (positiveAppendDegreeProfile d e)) (n + m)
        (tailDegree_add_neg_one_add_head (positiveAppendDegreeProfile d e))
        (E.firstContractionMap (positiveAppendDegreeProfile d e)
          ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x))
        (E.evaluateWord
          (tailWord (Y := Z)
            (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v))
          (tailDegreeProfile (positiveAppendDegreeProfile d e))
          ((positiveAppendTailSummandIso d e).inv.hom t)) := by
  have hmap := LinearMap.congr_fun
    (E.evaluateWord_positive_append_coordinates d e) (x ⊗ₜ[ℤ] t)
  simp only [LinearMap.comp_apply, ModuleCat.comp_apply,
    MonoidalCategory.tensorIso_inv, eqToIso.inv,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hmap
  unfold positiveAppendDegreeProfile positiveAppendWord at hmap ⊢
  rw [E.evaluateSucc_apply_tensor] at hmap
  exact hmap

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
