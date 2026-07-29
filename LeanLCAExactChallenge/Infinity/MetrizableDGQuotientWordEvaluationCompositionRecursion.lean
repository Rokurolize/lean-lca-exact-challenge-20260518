/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionInduction

/-! # Recursive composition coordinates for corrected Drinfeld word evaluation

This module proves that composition of a positive-word summand leaves its first factor untouched
at the list, boundary, and adjacent-merge levels.  The remaining merge is exactly the composition
merge for the recursive tail word.
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

/-- The non-head part of a positive composition prefix is the tail composition prefix. -/
theorem compositionMiddleFactors_eq_tailLeftPrefix
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionMiddleFactors d = compositionLeftPrefix (tailDegreeProfile d) := by
  unfold compositionMiddleFactors compositionLeftPrefix
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  congr 1
  funext i
  rw [tailFactorModule]
  congr 1

/-- The boundary module of a positive word is the boundary module of its tail. -/
theorem compositionBoundaryModule_eq_tail
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    compositionBoundaryModule d e =
      compositionBoundaryModule (tailDegreeProfile d) e := by
  unfold compositionBoundaryModule
  rw [tailWord_arrowSource, tailDegreeProfile_arrowDegree]
  rfl

/-- The boundary composition map of a positive word is the boundary map of its tail. -/
theorem compositionBoundaryMap_tail_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq (compositionBoundaryMap d e)
      (compositionBoundaryMap (tailDegreeProfile d) e) := by
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_heq
  · rw [tailWord_arrowSource]
    rfl
  · rw [tailWord_arrowTarget]
    rfl
  · rfl
  · rfl
  · rw [tailDegreeProfile_arrowDegree]
    rfl
  · rfl
  · rw [tailDegreeProfile_arrowDegree]
    rfl

/-- The factor list of a positive word is its head factor followed by its tail factors. -/
theorem finFamilyList_factorModule_eq_head_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    finFamilyList (factorModule d) =
      factorModule d 0 :: finFamilyList (factorModule (tailDegreeProfile d)) := by
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ]
  congr 2
  funext i
  rw [tailFactorModule]

/-- Appending to a positive word preserves its head factor and appends only to the tail. -/
theorem finFamilyList_factorModule_append_eq_head_tail
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    finFamilyList (factorModule (d.append e)) =
      factorModule d 0 ::
        finFamilyList (factorModule ((tailDegreeProfile d).append e)) := by
  rw [finFamilyList_factorModule_append_boundary,
    compositionLeftPrefix_succ_eq,
    compositionMiddleFactors_eq_tailLeftPrefix,
    compositionBoundaryModule_eq_tail,
    finFamilyList_factorModule_append_boundary]
  rfl

/-- The merge realizing positive-word composition is the tail merge prefixed by the head. -/
theorem compositionAdjacentMerge_tail_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e) (compositionBoundaryMap d e))
      ((adjacentMergeAfter (compositionLeftPrefix (tailDegreeProfile d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (tailDegreeProfile d) e)).prefix
          [factorModule d 0]) := by
  have hprefix : compositionLeftPrefix d =
      [factorModule d 0] ++ compositionLeftPrefix (tailDegreeProfile d) := by
    rw [compositionLeftPrefix_succ_eq,
      compositionMiddleFactors_eq_tailLeftPrefix]
    rfl
  have hlast : factorModule d (Fin.last (k + 1)) =
      factorModule (tailDegreeProfile d) (Fin.last k) := by
    rw [tailFactorModule]
    rfl
  apply HEq.trans (adjacentMergeAfter_congr hprefix hlast rfl
    (compositionBoundaryModule_eq_tail d e) rfl
    (compositionBoundaryMap_tail_heq d e))
  exact (adjacentMergeAfter_prefix_heq
    (compositionLeftPrefix (tailDegreeProfile d)) [factorModule d 0]
    (compositionBoundaryMap (tailDegreeProfile d) e)).symm

/-- The tensor map for positive-word composition is the tail merge tensor map under one
unchanged head prefix. -/
theorem compositionAdjacentMergeTensorMap_tail_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)).tensorMap
      (((adjacentMergeAfter (compositionLeftPrefix (tailDegreeProfile d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (tailDegreeProfile d) e)).prefix
          [factorModule d 0]).tensorMap) := by
  have hlast : factorModule d (Fin.last (k + 1)) =
      factorModule (tailDegreeProfile d) (Fin.last k) := by
    rw [tailFactorModule]
    rfl
  apply AdjacentMergeData.tensorMap_heq
  · rw [compositionLeftPrefix_succ_eq,
      compositionMiddleFactors_eq_tailLeftPrefix, hlast]
    rfl
  · rw [compositionLeftPrefix_succ_eq,
      compositionMiddleFactors_eq_tailLeftPrefix,
      compositionBoundaryModule_eq_tail]
    rfl
  · exact compositionAdjacentMerge_tail_heq d e

/-- Source-list transport exposing the unchanged head before recursive tail composition. -/
def positiveCompositionSourceListEq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
      [factorModule d 0] ++
        (finFamilyList (factorModule (tailDegreeProfile d)) ++
          finFamilyList (factorModule e)) := by
  rw [finFamilyList_factorModule_eq_head_tail]
  rfl

/-- Target-list transport exposing the unchanged head after recursive tail composition. -/
def positiveCompositionTargetListEq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    finFamilyList (factorModule (d.append e)) =
      [factorModule d 0] ++
        finFamilyList (factorModule ((tailDegreeProfile d).append e)) := by
  rw [finFamilyList_factorModule_append_eq_head_tail]
  rfl

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
