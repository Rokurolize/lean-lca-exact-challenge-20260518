/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationPositiveAppendNormalization

/-! # Positive-word induction for corrected Drinfeld evaluation multiplicativity

This module proves the positive-length induction step for multiplicativity of corrected
Drinfeld word evaluation.  Recursive summand composition fixes the positive head coordinate,
so multiplicativity for the recursively composed tail lifts to the full positive word by the
normalized evaluation recursion and associativity in the target enrichment.
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

/-- Recursive positive summand composition on canonical pure head/tail coordinates. -/
theorem summandCompositionMap_positive_recursive_apply_tensor
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0)
    (y : summandModule (tailDegreeProfile d))
    (z : summandModule e) :
    (positiveCompositionTargetIso d e).hom.hom
        ((summandCompositionMap d e).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)) =
      x ⊗ₜ[ℤ] ((summandCompositionMap (tailDegreeProfile d) e).hom
        (y ⊗ₜ[ℤ] z)) := by
  have h := ConcreteCategory.congr_hom
    (summandCompositionMap_positive_recursive d e)
    ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply] at h
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (summandModule_succ d)).inv_hom_id (x ⊗ₜ[ℤ] y)
  simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
    CategoryTheory.id_apply] at hcancel
  rw [hcancel] at h
  exact h

/-- The target degree equality used when evaluating the composition of degrees `n` and `m`. -/
def wordEvaluationCompositionDegreeEq (n m : ℤ) : m + n = n + m :=
  Int.add_comm m n

/-- Multiplicativity for the recursively composed tail implies multiplicativity for a positive
word in canonical pure head/tail coordinates. -/
theorem evaluateWord_multiplicative_positive_step
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0)
    (y : summandModule (tailDegreeProfile d))
    (z : summandModule e)
    (htail :
      E.evaluateWord ((tailWord (Y := Y) intermediate).append v)
          ((tailDegreeProfile d).append e)
          ((summandCompositionMap (tailDegreeProfile d) e).hom (y ⊗ₜ[ℤ] z)) =
        E.composeElement (intermediate 0).obj Y Z
          (tailDegree d) m (tailDegree d + m)
          (wordEvaluationCompositionDegreeEq (tailDegree d) m)
          (E.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) y)
          (E.evaluateWord v e z)) :
    E.evaluateWord
        (({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y).append v) (d.append e)
        ((summandCompositionMap d e).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateWord
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] y)))
        (E.evaluateWord v e z) := by
  let tailComposition :=
    (summandCompositionMap (tailDegreeProfile d) e).hom (y ⊗ₜ[ℤ] z)
  let dValue :=
    (eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] y)
  have hcoordinates := summandCompositionMap_positive_recursive_apply_tensor
    d e x y z
  have hcancel := ConcreteCategory.congr_hom
    (positiveCompositionTargetIso d e).hom_inv_id
    ((summandCompositionMap d e).hom (dValue ⊗ₜ[ℤ] z))
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  have hinput :
      (summandCompositionMap d e).hom (dValue ⊗ₜ[ℤ] z) =
        (positiveCompositionTargetIso d e).inv.hom
          (x ⊗ₜ[ℤ] tailComposition) := by
    exact hcancel.symm.trans (congrArg
      (positiveCompositionTargetIso d e).inv.hom hcoordinates)
  change E.evaluateWord
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).append v) (d.append e)
      ((summandCompositionMap d e).hom (dValue ⊗ₜ[ℤ] z)) = _
  rw [hinput]
  rw [E.evaluateWord_positive_append_apply_tensor_normalized
    d e x tailComposition]
  rw [htail]
  have hdValue := E.evaluateWord_succ_apply_tensor_of_coordinates
    d rfl rfl x y
  have hassoc := E.composeElement_assoc_of_degree_eq X (intermediate 0).obj Y Z
    (tailDegree_add_neg_one_add_head d)
    (wordEvaluationCompositionDegreeEq n m)
    (wordEvaluationCompositionDegreeEq (tailDegree d) m)
    (positiveAppendNormalizedOutputDegreeEq d e)
    (E.firstContractionMap d x)
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile d) y)
    (E.evaluateWord v e z)
  rw [hdValue]
  exact hassoc.symm

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
