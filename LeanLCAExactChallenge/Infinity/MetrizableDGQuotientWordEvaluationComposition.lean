/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationFunctor

/-! # Composition coordinates for corrected Drinfeld word evaluation

This module supplies the positive-append and head/contraction/tail transports used by the
inductive multiplicativity proof for `evaluateCochainMap`.
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

/-- Extensionality for words whose intermediate-object family has a dependent domain. -/
theorem word_ext_of_length_eq
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    (hlen : w.length = v.length)
    (hinter : ∀ i : Fin w.length,
      w.intermediate i = v.intermediate (Fin.cast hlen i)) :
    w = v := by
  cases w with
  | mk l f =>
      cases v with
      | mk m g =>
          dsimp at hlen
          subst m
          congr
          funext i
          exact hinter i

/-- The head/tail/right-word coordinates of an appended positive word. -/
def positiveAppendIntermediate
    {Y Z : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory)
    (v : DrinfeldWord Y Z) :
    Fin ((k + v.length) + 1) → CorrectedAcyclicComplexCategory :=
  Fin.cases (intermediate 0)
    (Fin.addCases (fun i : Fin k ↦ intermediate i.succ) v.intermediate)

/-- A positive append presented in head/tail/right-word coordinates. -/
def positiveAppendWord
    {X Y Z : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory)
    (v : DrinfeldWord Y Z) : DrinfeldWord X Z where
  length := (k + v.length) + 1
  intermediate := positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v

/-- The canonical positive-append coordinates present the ordinary appended word. -/
theorem positiveAppendWord_eq_append
    {X Y Z : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory)
    (v : DrinfeldWord Y Z) :
    positiveAppendWord (X := X) intermediate v =
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).append v := by
  cases v with
  | mk l right =>
      apply word_ext_of_length_eq
        (w := positiveAppendWord (X := X) intermediate
          ({ length := l, intermediate := right } : DrinfeldWord Y Z))
        (v := ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y).append
            ({ length := l, intermediate := right } : DrinfeldWord Y Z))
        (by
        simp only [positiveAppendWord, append]
        omega)
      intro i
      change Fin ((k + l) + 1) at i
      refine Fin.cases ?_ (fun q ↦ ?_) i
      · simp only [positiveAppendWord, positiveAppendIntermediate, append,
          Fin.cases_zero]
        congr 1
      · have htail := congrFun
          (finAddCases_succAbove_append_left k l intermediate right 0) q
        simpa [positiveAppendWord, positiveAppendIntermediate, append,
          Fin.succAbove, Fin.lt_def] using htail.symm

/-- Removing the head coordinate of a positive append leaves the tail word followed by the
right word. -/
theorem tailWord_positiveAppend
    {Y Z : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory)
    (v : DrinfeldWord Y Z) :
    tailWord (Y := Z)
        (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v) =
      (tailWord (Y := Y) intermediate).append v := by
  cases v with
  | mk l right =>
      apply word_ext_of_length_eq
        (w := tailWord (Y := Z)
          (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate
            ({ length := l, intermediate := right } : DrinfeldWord Y Z)))
        (v := (tailWord (Y := Y) intermediate).append
          ({ length := l, intermediate := right } : DrinfeldWord Y Z)) rfl
      intro i
      rfl

/-- A positive word is the first ordinary arrow, the formal contraction at its first
intermediate object, and the remaining tail word. -/
theorem positiveWord_eq_head_contraction_tail
    {X Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory) :
    ((nil X (intermediate 0).obj).append
        (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0))).append
      (tailWord (Y := Y) intermediate) =
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) := by
  let w := ((nil X (intermediate 0).obj).append
    (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0))).append
      (tailWord (Y := Y) intermediate)
  let v : DrinfeldWord X Y := { length := k + 1, intermediate := intermediate }
  have hlen : w.length = v.length := by
    dsimp [w, v, append, nil, singleton, tailWord]
    omega
  apply word_ext_of_length_eq hlen
  intro i
  let j : Fin (k + 1) := Fin.cast hlen i
  have hi : i = Fin.cast hlen.symm j := by
    apply Fin.ext
    rfl
  rw [hi]
  have hback : Fin.cast hlen (Fin.cast hlen.symm j) = j := by
    apply Fin.ext
    rfl
  rw [hback]
  refine Fin.cases ?_ (fun r ↦ ?_) j
  · have hz : Fin.cast hlen.symm (0 : Fin (k + 1)) =
        Fin.castAdd k (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hz]
    rfl
  · let head := (nil X (intermediate 0).obj).append
        (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0))
    have hs : Fin.cast hlen.symm (Fin.succ r) = Fin.natAdd head.length r := by
      apply Fin.ext
      dsimp [head, append, nil, singleton]
      omega
    rw [hs]
    dsimp [w, v, head, append, tailWord]
    rw [Fin.addCases_right]

/-- The raw appended degree profile for the head/contraction/tail decomposition. -/
def positiveRawDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :=
  ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
      (singletonContractingDegreeProfile (intermediate 0))).append
    (tailDegreeProfile d)

/-- The appended head/contraction/tail degree profile transports to the original profile. -/
theorem positiveRawDegreeProfile_transport
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (positiveRawDegreeProfile d).transport
        (positiveWord_eq_head_contraction_tail intermediate)
        (show (d.arrowDegree 0 + (-1)) +
            (n - d.arrowDegree 0 + 1) = n by omega) = d := by
  apply DegreeProfile.eq_of_degreeList_eq
  rw [DegreeProfile.degreeList_transport]
  unfold positiveRawDegreeProfile
  rw [DegreeProfile.degreeList_append, DegreeProfile.degreeList_append]
  simp [DegreeProfile.degreeList, finFamilyList_eq_ofFn,
    degreeBoundaryMerge, nilDegreeProfile,
    singletonContractingDegreeProfile, tailDegreeProfile,
    nil, singleton]

/-- Transport the raw appended summand to the original positive-word summand. -/
def positiveRawSummandIso
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (positiveRawDegreeProfile d) ≅ summandModule d :=
  summandModuleTransportIso
      (positiveWord_eq_head_contraction_tail intermediate)
      (show (d.arrowDegree 0 + (-1)) +
          (n - d.arrowDegree 0 + 1) = n by omega)
      (positiveRawDegreeProfile d) ≪≫
    eqToIso (congrArg summandModule (positiveRawDegreeProfile_transport d))

/-- The raw positive-word transport with its source profile written out explicitly. -/
def positiveRawSummandIsoExpanded
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule
        (((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))).append
            (tailDegreeProfile d)) ≅
      summandModule d :=
  positiveRawSummandIso d

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
