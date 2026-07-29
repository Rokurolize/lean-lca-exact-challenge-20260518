/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionRecursion

/-! # Recursive composition remainders for corrected Drinfeld word evaluation

This module removes the equality transports surrounding a normalized composition remainder and
uses the positive-word merge recursion to factor the whole remainder through the recursive tail.
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

/-- The transports surrounding a normalized remainder are heterogeneously invisible. -/
theorem summandCompositionRemainder_heq_merge
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    HEq (summandCompositionRemainder d e)
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)).tensorMap := by
  unfold summandCompositionRemainder
  slice_lhs 1 2 => rw [eqToHom_trans]
  apply HEq.trans
    (CategoryTheory.eqToHom_comp_heq
      ((adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)).tensorMap ≫
          eqToHom (congrArg tensorModuleList (compositionTargetListEq d e)))
      ((congrArg tensorModuleList (compositionSourceListEq d e)).trans
        (congrArg tensorModuleList (compositionBoundaryListEq d e))))
  exact CategoryTheory.comp_eqToHom_heq _ _

/-- The normalized composition remainder is recursive under the unchanged positive head. -/
theorem summandCompositionRemainder_positive_recursive
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandCompositionRemainder d e =
      eqToHom (congrArg tensorModuleList
        (positiveCompositionSourceListEq d e)) ≫
        tensorModuleListWhiskerLeft [factorModule d 0]
          (summandCompositionRemainder (tailDegreeProfile d) e) ≫
        eqToHom (congrArg tensorModuleList
          (positiveCompositionTargetListEq d e).symm) := by
  apply eq_of_heq
  apply HEq.trans (summandCompositionRemainder_heq_merge d e)
  apply HEq.trans (compositionAdjacentMergeTensorMap_tail_heq d e)
  rw [summandCompositionRemainder_whiskerLeft]
  simp only [Category.assoc]
  rw [AdjacentMergeData.prefix_tensorMap]
  slice_rhs 1 3 => rw [eqToHom_trans, eqToHom_trans]
  slice_rhs 3 4 => rw [eqToHom_trans]
  exact ((CategoryTheory.eqToHom_comp_heq
    (_ ≫ eqToHom _) _).trans
      (CategoryTheory.comp_eqToHom_heq _ _)).symm

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
