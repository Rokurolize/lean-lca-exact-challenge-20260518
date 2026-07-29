/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationComposition

/-! # Inductive composition coordinates for corrected Drinfeld word evaluation

This module identifies the recursive tail of an appended positive word with the append of the
original tail.  It also lifts that dependent profile transport to the tensor summands used by the
multiplicativity induction for `evaluateCochainMap`.
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

/-- Casting a profile along a word equality does not change its degree list. -/
theorem degreeList_castWord
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (h : w = v) :
    (d.castWord h).degreeList = d.degreeList := by
  subst v
  rfl

/-- The degree list of a positive word is its head degree followed by its tail list. -/
theorem degreeList_eq_head_cons_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    d.degreeList = d.arrowDegree 0 :: (tailDegreeProfile d).degreeList := by
  rw [DegreeProfile.degreeList, DegreeProfile.degreeList,
    finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ]
  rfl

/-- Boundary merging a nonempty tail preserves a preceding head coordinate. -/
theorem degreeBoundaryMerge_head_cons
    (x : ℤ) (xs ys : List ℤ) (hxs : xs ≠ []) (hys : ys ≠ []) :
    degreeBoundaryMerge (x :: xs) ys = x :: degreeBoundaryMerge xs ys := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons x' xs =>
      cases ys with
      | nil => exact False.elim (hys rfl)
      | cons y ys => rfl

/-- The appended profile, expressed on the canonical positive-append word. -/
def positiveAppendDegreeProfile
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    DegreeProfile (positiveAppendWord (X := X) intermediate v) (n + m) :=
  (d.append e).castWord (positiveAppendWord_eq_append intermediate v).symm

/-- The head degree of an appended positive profile is unchanged. -/
theorem positiveAppendDegreeProfile_arrowDegree_zero
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (positiveAppendDegreeProfile d e).arrowDegree 0 = d.arrowDegree 0 := by
  unfold positiveAppendDegreeProfile
  rw [DegreeProfile.castWord_arrowDegree]
  change appendArrowDegree d e (appendLeftArrowIndex (0 : Fin (k + 1))) = _
  rw [appendArrowDegree_left]
  rfl

/-- Appending to a positive profile preserves the head coordinate and appends only to its tail. -/
theorem positiveAppendDegreeProfile_degreeList
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (positiveAppendDegreeProfile d e).degreeList =
      d.arrowDegree 0 :: ((tailDegreeProfile d).append e).degreeList := by
  calc
    (positiveAppendDegreeProfile d e).degreeList =
        (d.append e).degreeList := by
      exact degreeList_castWord (d.append e)
        (positiveAppendWord_eq_append intermediate v).symm
    _ = degreeBoundaryMerge d.degreeList e.degreeList :=
      DegreeProfile.degreeList_append d e
    _ = degreeBoundaryMerge
        (d.arrowDegree 0 :: (tailDegreeProfile d).degreeList) e.degreeList := by
      rw [degreeList_eq_head_cons_tail d]
    _ = d.arrowDegree 0 ::
        degreeBoundaryMerge (tailDegreeProfile d).degreeList e.degreeList := by
      exact degreeBoundaryMerge_head_cons _ _ _
        (tailDegreeProfile d).degreeList_ne_nil e.degreeList_ne_nil
    _ = d.arrowDegree 0 :: ((tailDegreeProfile d).append e).degreeList := by
      rw [DegreeProfile.degreeList_append]

/-- Removing the head from an appended positive profile gives the appended tail profile. -/
def positiveAppendTailProfile
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    DegreeProfile ((tailWord (Y := Y) intermediate).append v) (tailDegree d + m) :=
  (tailDegreeProfile (positiveAppendDegreeProfile d e)).transport
    (tailWord_positiveAppend intermediate v)
    (by
      unfold tailDegree
      rw [positiveAppendDegreeProfile_arrowDegree_zero]
      omega)

/-- The recursive tail of an appended positive profile is the append of the original tail. -/
theorem positiveAppendTailProfile_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    positiveAppendTailProfile d e = (tailDegreeProfile d).append e := by
  apply DegreeProfile.eq_of_degreeList_eq
  have hsplit := degreeList_eq_head_cons_tail (positiveAppendDegreeProfile d e)
  have hhead := positiveAppendDegreeProfile_arrowDegree_zero d e
  have hsplit' :
      (positiveAppendDegreeProfile d e).degreeList =
        d.arrowDegree 0 ::
          (tailDegreeProfile (positiveAppendDegreeProfile d e)).degreeList := by
    exact hsplit.trans (congrArg
      (fun a : ℤ ↦ a ::
        (tailDegreeProfile (positiveAppendDegreeProfile d e)).degreeList) hhead)
  have hfull := positiveAppendDegreeProfile_degreeList d e
  have htail :
      (tailDegreeProfile (positiveAppendDegreeProfile d e)).degreeList =
        ((tailDegreeProfile d).append e).degreeList := by
    exact List.cons.inj (hsplit'.symm.trans hfull) |>.2
  calc
    (positiveAppendTailProfile d e).degreeList =
        (tailDegreeProfile (positiveAppendDegreeProfile d e)).degreeList := by
      exact DegreeProfile.degreeList_transport
        (tailWord_positiveAppend intermediate v)
        (by
          unfold tailDegree
          rw [positiveAppendDegreeProfile_arrowDegree_zero]
          omega)
        (tailDegreeProfile (positiveAppendDegreeProfile d e))
    _ = ((tailDegreeProfile d).append e).degreeList := htail

/-- The first factor module of an appended positive profile is the original head factor. -/
theorem positiveAppendFactorModule_zero
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    factorModule (positiveAppendDegreeProfile d e) 0 = factorModule d 0 := by
  rw [factorModule_zero_succ, factorModule_zero_succ,
    positiveAppendDegreeProfile_arrowDegree_zero]
  rfl

/-- Canonical transport from the recursive tail summand to the appended tail summand. -/
def positiveAppendTailSummandIso
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandModule (tailDegreeProfile (positiveAppendDegreeProfile d e)) ≅
      summandModule ((tailDegreeProfile d).append e) :=
  summandModuleTransportIso
      (tailWord_positiveAppend intermediate v)
      (by
        rw [positiveAppendDegreeProfile_arrowDegree_zero]
        omega)
      (tailDegreeProfile (positiveAppendDegreeProfile d e)) ≪≫
    eqToIso (congrArg summandModule (positiveAppendTailProfile_eq d e))

/-- A composed positive summand is its original head factor tensored with the composed tail. -/
def positiveAppendSummandIso
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandModule (d.append e) ≅
      factorModule d 0 ⊗ summandModule ((tailDegreeProfile d).append e) :=
  summandModuleCastWordIso (positiveAppendWord_eq_append intermediate v).symm
      (d.append e) ≪≫
    eqToIso (summandModule_succ (positiveAppendDegreeProfile d e)) ≪≫
    MonoidalCategory.tensorIso
      (eqToIso (positiveAppendFactorModule_zero d e))
      (positiveAppendTailSummandIso d e)

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
