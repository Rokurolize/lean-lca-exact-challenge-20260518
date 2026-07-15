/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEraseFactors

/-! # Coherence of two consecutive Drinfeld contractions -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

theorem rawSecondContractionMerge_left_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (j : Fin (k + 1)) :
    HEq (rawSecondContractionMerge d j.castSucc j)
      (dgCochainCompTensorOfEq
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowSource j.castSucc.castSucc)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowTarget j.castSucc.succ)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowSource j.succ.succ)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowTarget j.succ.succ)
        (arrowTarget_castSucc_eq_arrowSource_succ
          ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y) j.succ)
        (p := d.arrowDegree j.castSucc.castSucc + d.arrowDegree j.castSucc.succ)
        (q := d.arrowDegree j.succ.succ)
        (r := d.arrowDegree j.castSucc.castSucc + d.arrowDegree j.castSucc.succ +
          d.arrowDegree j.succ.succ) rfl) := by
  unfold rawSecondContractionMerge
  simp [rawSecondContractionFactor]

theorem rawSecondContractionMerge_right_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (j : Fin (k + 1)) :
    HEq (rawSecondContractionMerge d j.succ j)
      (dgCochainCompTensorOfEq
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowSource j.castSucc.castSucc)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowTarget j.castSucc.castSucc)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowSource j.castSucc.succ)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowTarget j.succ.succ)
        (arrowTarget_castSucc_eq_arrowSource_succ
          ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y) j.castSucc)
        (p := d.arrowDegree j.castSucc.castSucc)
        (q := d.arrowDegree j.castSucc.succ + d.arrowDegree j.succ.succ)
        (r := d.arrowDegree j.castSucc.castSucc + d.arrowDegree j.castSucc.succ +
          d.arrowDegree j.succ.succ) (by omega)) := by
  unfold rawSecondContractionMerge
  have hne : j.succ ≠ j.castSucc := (Fin.ne_of_lt Fin.castSucc_lt_succ).symm
  simp [rawSecondContractionFactor, hne]

theorem dgCochainCompTensorOfEq_heq
    {K₁ L₁ L₁' M₁ K₂ L₂ L₂' M₂ : ComplexCategory}
    (hK : K₁ = K₂) (hL : L₁ = L₂) (hL' : L₁' = L₂') (hM : M₁ = M₂)
    (e₁ : L₁ = L₁') (e₂ : L₂ = L₂')
    {p₁ q₁ r₁ p₂ q₂ r₂ : ℤ}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (hr : r₁ = r₂)
    (hsum₁ : p₁ + q₁ = r₁) (hsum₂ : p₂ + q₂ = r₂) :
    HEq (dgCochainCompTensorOfEq K₁ L₁ L₁' M₁ e₁ hsum₁)
      (dgCochainCompTensorOfEq K₂ L₂ L₂' M₂ e₂ hsum₂) := by
  subst K₂
  subst L₂
  subst L₂'
  subst M₂
  subst p₂
  subst q₂
  subst r₂
  apply heq_of_eq
  congr

theorem adjacentFactorComposition_tail_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    HEq (adjacentFactorComposition d i.succ)
      (adjacentFactorComposition (tailDegreeProfile d) i) := by
  unfold adjacentFactorComposition factorModule
  apply dgCochainCompTensorOfEq_heq
  · simpa only [Fin.castSucc_succ] using
      (tailWord_arrowSource (X := X) (Y := Y)
        (intermediate := intermediate) i.castSucc).symm
  · simpa only [Fin.castSucc_succ] using
      (tailWord_arrowTarget (X := X) (Y := Y)
        (intermediate := intermediate) i.castSucc).symm
  · exact (tailWord_arrowSource (X := X) (Y := Y)
      (intermediate := intermediate) i.succ).symm
  · exact (tailWord_arrowTarget (X := X) (Y := Y)
      (intermediate := intermediate) i.succ).symm
  · simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]
  · simp only [tailDegreeProfile_arrowDegree]
  · simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]

theorem rawSecondContractionMerge_tail_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 3) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 3, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (rawSecondContractionMerge d i.succ j.succ)
      (rawSecondContractionMerge (tailDegreeProfile d) i j) := by
  by_cases hleft : i = j.castSucc
  · unfold rawSecondContractionMerge
    simp only [Fin.castSucc_succ, rawSecondContractionFactor, hleft,
      ↓reduceDIte, id_eq, eq_mpr_eq_cast,
      tailDegreeProfile_arrowDegree, heq_cast_iff_heq, heq_eqRec_iff_heq,
      cast_heq_iff_heq, eqRec_heq_iff_heq]
    apply dgCochainCompTensorOfEq_heq
    · simpa only [Fin.castSucc_succ] using
        (tailWord_arrowSource (X := X) (Y := Y)
          (intermediate := intermediate) j.castSucc.castSucc).symm
    · simpa only [Fin.castSucc_succ] using
        (tailWord_arrowTarget (X := X) (Y := Y)
          (intermediate := intermediate) j.castSucc.succ).symm
    · exact (tailWord_arrowSource (X := X) (Y := Y)
        (intermediate := intermediate) j.succ.succ).symm
    · exact (tailWord_arrowTarget (X := X) (Y := Y)
        (intermediate := intermediate) j.succ.succ).symm
    · rfl
    · rfl
    · rfl
  · by_cases hright : i = j.succ
    · subst i
      have hold := rawSecondContractionMerge_right_heq d j.succ
      have htail := rawSecondContractionMerge_right_heq (tailDegreeProfile d) j
      apply HEq.trans hold
      apply HEq.trans _ htail.symm
      apply dgCochainCompTensorOfEq_heq
      · simpa only [Fin.castSucc_succ] using
          (tailWord_arrowSource (X := X) (Y := Y)
            (intermediate := intermediate) j.castSucc.castSucc).symm
      · exact (tailWord_arrowTarget (X := X) (Y := Y)
          (intermediate := intermediate) j.castSucc.castSucc).symm
      · simpa only [Fin.castSucc_succ] using
          (tailWord_arrowSource (X := X) (Y := Y)
            (intermediate := intermediate) j.castSucc.succ).symm
      · exact (tailWord_arrowTarget (X := X) (Y := Y)
          (intermediate := intermediate) j.succ.succ).symm
      · simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]
      · simp only [tailDegreeProfile_arrowDegree]
        apply congrArg (fun t => d.arrowDegree t + d.arrowDegree j.succ.succ.succ)
        apply Fin.ext
        rfl
      · simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]
    · by_cases hbefore : j.castSucc < i
      · unfold rawSecondContractionMerge
        simp only [Fin.castSucc_succ, rawSecondContractionFactor, Fin.succ_inj,
          hleft, hright, ↓reduceDIte, Fin.succ_lt_succ_iff,
          hbefore, eq_mpr_eq_cast, cast_cast, tailDegreeProfile_arrowDegree,
          heq_cast_iff_heq, cast_heq_iff_heq]
        exact adjacentFactorComposition_tail_heq d j.castSucc
      · unfold rawSecondContractionMerge
        simp only [Fin.castSucc_succ, rawSecondContractionFactor, Fin.succ_inj,
          hleft, hright, ↓reduceDIte, Fin.succ_lt_succ_iff,
          hbefore, eq_mpr_eq_cast, cast_cast, tailDegreeProfile_arrowDegree,
          heq_cast_iff_heq, cast_heq_iff_heq]
        exact adjacentFactorComposition_tail_heq d j.succ

theorem pairHCoherence_congr
    {source₁ middle₁₁ middle₂₁ target₁₁ target₂₁ :
      List (ModuleCat.{0} ℤ)}
    {source₂ middle₁₂ middle₂₂ target₁₂ target₂₂ :
      List (ModuleCat.{0} ℤ)}
    {f₁ : AdjacentMergeData source₁ middle₁₁}
    {g₁ : AdjacentMergeData middle₁₁ target₁₁}
    {f₂ : AdjacentMergeData source₁ middle₂₁}
    {g₂ : AdjacentMergeData middle₂₁ target₂₁}
    {f₁' : AdjacentMergeData source₂ middle₁₂}
    {g₁' : AdjacentMergeData middle₁₂ target₁₂}
    {f₂' : AdjacentMergeData source₂ middle₂₂}
    {g₂' : AdjacentMergeData middle₂₂ target₂₂}
    (h : AdjacentMergePairHCoherence f₁ g₁ f₂ g₂)
    (hsource : source₁ = source₂)
    (hmiddle₁ : middle₁₁ = middle₁₂)
    (hmiddle₂ : middle₂₁ = middle₂₂)
    (htarget₁ : target₁₁ = target₁₂)
    (htarget₂ : target₂₁ = target₂₂)
    (hf₁ : HEq f₁ f₁') (hg₁ : HEq g₁ g₁')
    (hf₂ : HEq f₂ f₂') (hg₂ : HEq g₂ g₂') :
    AdjacentMergePairHCoherence f₁' g₁' f₂' g₂' := by
  subst source₂
  subst middle₁₂
  subst middle₂₂
  subst target₁₂
  subst target₂₂
  have ef₁ : f₁ = f₁' := eq_of_heq hf₁
  have eg₁ : g₁ = g₁' := eq_of_heq hg₁
  have ef₂ : f₂ = f₂' := eq_of_heq hf₂
  have eg₂ : g₂ = g₂' := eq_of_heq hg₂
  subst f₁'
  subst g₁'
  subst f₂'
  subst g₂'
  exact h

theorem recursiveAdjacentMergeDataOfFn_succ_heq
    {k : ℕ} (M : Fin (k + 3) → ModuleCat.{0} ℤ) (i : Fin (k + 1))
    (P : ModuleCat.{0} ℤ)
    (f : Quiver.Hom (M i.succ.castSucc ⊗ M i.succ.succ) P) :
    HEq (recursiveAdjacentMergeDataOfFn M i.succ P f)
      (@AdjacentMergeData.tail (M 0) _ _
        (recursiveAdjacentMergeDataOfFn (fun q => M q.succ) i P (by
          simpa using f))) := by
  unfold recursiveAdjacentMergeDataOfFn
  rfl

theorem recursiveAdjacentMergeDataOfFn_tail_congr
    {k : ℕ} {M N : Fin (k + 2) → ModuleCat.{0} ℤ}
    (hM : M = N) (i : Fin (k + 1)) {P Q : ModuleCat.{0} ℤ}
    (hP : P = Q)
    {f : Quiver.Hom (M i.castSucc ⊗ M i.succ) P}
    {g : Quiver.Hom (N i.castSucc ⊗ N i.succ) Q}
    (hf : HEq f g) (H : ModuleCat.{0} ℤ) :
    HEq (@AdjacentMergeData.tail H _ _
        (recursiveAdjacentMergeDataOfFn M i P f))
      (@AdjacentMergeData.tail H _ _
        (recursiveAdjacentMergeDataOfFn N i Q g)) := by
  subst N
  subst Q
  have hfg : f = g := eq_of_heq hf
  subst g
  rfl

theorem rawContractionAdjacentMergeData_tail_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    HEq (rawContractionAdjacentMergeData d i.succ)
      (@AdjacentMergeData.tail (factorModule d 0) _ _
        (rawContractionAdjacentMergeData (tailDegreeProfile d) i)) := by
  have hfactor : factorModule (tailDegreeProfile d) =
      fun q => factorModule d q.succ := by
    funext q
    exact tailFactorModule d q
  have hraw : rawContractionFactor (tailDegreeProfile d) =
      fun q => rawContractionFactor d q.succ := by
    funext q
    exact tailRawContractionFactor d q
  unfold rawContractionAdjacentMergeData
  apply HEq.trans (recursiveAdjacentMergeDataOfFn_succ_heq
    (factorModule d) i (rawContractionFactor d i.succ)
    (adjacentFactorComposition d i.succ))
  apply recursiveAdjacentMergeDataOfFn_tail_congr
    hfactor.symm i (tailRawContractionFactor d i).symm
  exact adjacentFactorComposition_tail_heq d i

theorem rawSecondContractionFactor_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 3) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 3, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    rawSecondContractionFactor (tailDegreeProfile d) i j =
      rawSecondContractionFactor d i.succ j.succ := by
  unfold rawSecondContractionFactor
  by_cases hleft : i = j.castSucc
  · subst i
    simp only [true_or, if_true, Fin.succ_castSucc,
      tailRawTripleContractionFactor]
  · by_cases hright : i = j.succ
    · subst i
      simp only [or_true, if_true, tailRawTripleContractionFactor]
    · have hleftSucc : i.succ ≠ j.succ.castSucc := by
        intro h
        apply hleft
        apply Fin.succ_inj.mp
        simpa only [Fin.succ_castSucc] using h
      simp only [hleft, hright, or_self, if_false, hleftSucc,
        Fin.succ_inj, Fin.succ_succAbove_succ,
        tailRawContractionFactor]

theorem rawSecondContractionMergeData_tail_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 3) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 3, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq (rawSecondContractionMergeData d i.succ j.succ)
      (@AdjacentMergeData.tail (factorModule d 0) _ _
        (rawSecondContractionMergeData (tailDegreeProfile d) i j)) := by
  have hfactor : factorModule (tailDegreeProfile d) =
      fun q => factorModule d q.succ := by
    funext q
    exact tailFactorModule d q
  have hraw : rawContractionFactor (tailDegreeProfile d) =
      fun q => rawContractionFactor d q.succ := by
    funext q
    exact tailRawContractionFactor d q
  have hsecondFactor := rawSecondContractionFactor_tail d i j
  have hmerged : recursiveMergedFactor (factorModule (tailDegreeProfile d)) i
        (rawContractionFactor (tailDegreeProfile d) i) =
      fun q => recursiveMergedFactor (factorModule d) i.succ
        (rawContractionFactor d i.succ) q.succ := by
    rw [hfactor, hraw]
    rfl
  unfold rawSecondContractionMergeData
  apply HEq.trans (recursiveAdjacentMergeDataOfFn_succ_heq
    (recursiveMergedFactor (factorModule d) i.succ
      (rawContractionFactor d i.succ)) j
    (rawSecondContractionFactor d i.succ j.succ)
    (rawSecondContractionMerge d i.succ j.succ))
  apply recursiveAdjacentMergeDataOfFn_tail_congr
    hmerged.symm j hsecondFactor.symm
  exact rawSecondContractionMerge_tail_heq d i j

theorem rawContractionAdjacentMerge_pair_coherence
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    AdjacentMergePairHCoherence
      (rawContractionAdjacentMergeData d i)
      (rawSecondContractionMergeData d i j)
      (rawContractionAdjacentMergeData d (i.succAbove j))
      (rawSecondContractionMergeData d (i.succAbove j) (j.predAbove i)) := by
  induction k generalizing X Y n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      cases i using Fin.cases with
      | zero =>
        apply AdjacentMergePairHCoherence.assoc
        have hleft := eq_of_heq (rawSecondContractionMerge_left_heq d 0)
        have hright := eq_of_heq (rawSecondContractionMerge_right_heq d 0)
        change rawSecondContractionMerge d 0 0 = _ at hleft
        change rawSecondContractionMerge d 1 0 = _ at hright
        have hp : (0 : Fin 1).predAbove (0 : Fin 2) = 0 :=
          Fin.predAbove_right_zero
        simpa [rawContractionAdjacentMergeData, rawSecondContractionMergeData,
          rawSecondContractionFactor,
          recursiveAdjacentMergeDataOfFn, recursiveMergedFactor,
          rawContractionFactor, rawTripleContractionFactor, factorModule,
          Fin.castSucc_succ, Fin.succAbove, Fin.predAbove, hp, hleft, hright] using
            adjacentFactorComposition_assoc intermediate d 0
      | succ i =>
        have hi : i = 0 := Fin.eq_zero i
        subst i
        apply AdjacentMergePairHCoherence.symm
        apply AdjacentMergePairHCoherence.assoc
        have hleft := eq_of_heq (rawSecondContractionMerge_left_heq d 0)
        have hright := eq_of_heq (rawSecondContractionMerge_right_heq d 0)
        change rawSecondContractionMerge d 0 0 = _ at hleft
        change rawSecondContractionMerge d 1 0 = _ at hright
        have hs : (Fin.succ 0 : Fin 2).succAbove (0 : Fin 1) = 0 :=
          Fin.one_succAbove_zero
        have hp : (0 : Fin 1).predAbove (Fin.succ 0 : Fin 2) = 0 := by
          simp
        simpa [rawContractionAdjacentMergeData, rawSecondContractionMergeData,
          rawSecondContractionFactor,
          recursiveAdjacentMergeDataOfFn, recursiveMergedFactor,
          rawContractionFactor, rawTripleContractionFactor, factorModule,
          Fin.castSucc_succ, Fin.succAbove, Fin.predAbove, hs, hp, hleft, hright] using
            adjacentFactorComposition_assoc intermediate d 0
  | succ k ih =>
      cases j using Fin.cases with
      | zero =>
          cases i using Fin.cases with
          | zero =>
              apply AdjacentMergePairHCoherence.assoc
              have hleft := eq_of_heq (rawSecondContractionMerge_left_heq d 0)
              have hright := eq_of_heq (rawSecondContractionMerge_right_heq d 0)
              change rawSecondContractionMerge d 0 0 = _ at hleft
              change rawSecondContractionMerge d 1 0 = _ at hright
              simpa [rawContractionAdjacentMergeData, rawSecondContractionMergeData,
                rawSecondContractionFactor, recursiveAdjacentMergeDataOfFn,
                recursiveMergedFactor, rawContractionFactor, rawTripleContractionFactor,
                factorModule, Fin.castSucc_succ, Fin.succAbove, Fin.predAbove,
                hleft, hright] using adjacentFactorComposition_assoc intermediate d 0
          | succ i =>
              cases i using Fin.cases with
              | zero =>
                  apply AdjacentMergePairHCoherence.symm
                  apply AdjacentMergePairHCoherence.assoc
                  have hleft := eq_of_heq (rawSecondContractionMerge_left_heq d 0)
                  have hright := eq_of_heq (rawSecondContractionMerge_right_heq d 0)
                  change rawSecondContractionMerge d 0 0 = _ at hleft
                  change rawSecondContractionMerge d 1 0 = _ at hright
                  simpa [rawContractionAdjacentMergeData, rawSecondContractionMergeData,
                    rawSecondContractionFactor, recursiveAdjacentMergeDataOfFn,
                    recursiveMergedFactor, rawContractionFactor, rawTripleContractionFactor,
                    factorModule, Fin.castSucc_succ, Fin.succAbove, Fin.predAbove,
                    hleft, hright] using adjacentFactorComposition_assoc intermediate d 0
              | succ i =>
                  apply AdjacentMergePairHCoherence.symm
                  apply AdjacentMergePairHCoherence.head_tail
      | succ j =>
          cases i using Fin.cases with
          | zero =>
              apply AdjacentMergePairHCoherence.head_tail
          | succ i =>
              have hfactor : factorModule (tailDegreeProfile d) =
                  fun q => factorModule d q.succ := by
                funext q
                exact tailFactorModule d q
              have hraw : rawContractionFactor (tailDegreeProfile d) =
                  fun q => rawContractionFactor d q.succ := by
                funext q
                exact tailRawContractionFactor d q
              have hmerged (a : Fin (k + 2)) :
                  recursiveMergedFactor (factorModule (tailDegreeProfile d)) a
                      (rawContractionFactor (tailDegreeProfile d) a) =
                    fun q => recursiveMergedFactor (factorModule d) a.succ
                      (rawContractionFactor d a.succ) q.succ := by
                rw [hfactor, hraw]
                rfl
              have hsecondMerged (a : Fin (k + 2)) (b : Fin (k + 1)) :
                  recursiveMergedFactor
                      (recursiveMergedFactor (factorModule (tailDegreeProfile d)) a
                        (rawContractionFactor (tailDegreeProfile d) a)) b
                      (rawSecondContractionFactor (tailDegreeProfile d) a b) =
                    fun q => recursiveMergedFactor
                      (recursiveMergedFactor (factorModule d) a.succ
                        (rawContractionFactor d a.succ)) b.succ
                      (rawSecondContractionFactor d a.succ b.succ) q.succ := by
                rw [hmerged a, rawSecondContractionFactor_tail d a b]
                rfl
              have h := AdjacentMergePairHCoherence.tail
                (M := factorModule d 0)
                (ih (tailDegreeProfile d) i j)
              apply pairHCoherence_congr h (by
                change factorModule d 0 ::
                    finFamilyList (factorModule (tailDegreeProfile d)) =
                  finFamilyList (factorModule d)
                rw [hfactor]) (by
                change factorModule d 0 :: finFamilyList
                    (recursiveMergedFactor (factorModule (tailDegreeProfile d)) i
                      (rawContractionFactor (tailDegreeProfile d) i)) =
                  finFamilyList (recursiveMergedFactor (factorModule d) i.succ
                    (rawContractionFactor d i.succ))
                rw [hmerged i]
                rfl)
                (by
                  rw [Fin.succ_succAbove_succ]
                  change factorModule d 0 :: finFamilyList
                      (recursiveMergedFactor (factorModule (tailDegreeProfile d))
                        (i.succAbove j)
                        (rawContractionFactor (tailDegreeProfile d)
                          (i.succAbove j))) =
                    finFamilyList (recursiveMergedFactor (factorModule d)
                      (i.succAbove j).succ
                      (rawContractionFactor d (i.succAbove j).succ))
                  rw [hmerged (i.succAbove j)]
                  rfl)
                (by
                  change factorModule d 0 :: finFamilyList
                      (recursiveMergedFactor
                        (recursiveMergedFactor
                          (factorModule (tailDegreeProfile d)) i
                          (rawContractionFactor (tailDegreeProfile d) i)) j
                        (rawSecondContractionFactor (tailDegreeProfile d) i j)) =
                    finFamilyList (recursiveMergedFactor
                      (recursiveMergedFactor (factorModule d) i.succ
                        (rawContractionFactor d i.succ)) j.succ
                      (rawSecondContractionFactor d i.succ j.succ))
                  rw [hsecondMerged i j]
                  rfl)
                (by
                  rw [Fin.succ_succAbove_succ, Fin.succ_predAbove_succ]
                  change factorModule d 0 :: finFamilyList
                      (recursiveMergedFactor
                        (recursiveMergedFactor
                          (factorModule (tailDegreeProfile d)) (i.succAbove j)
                          (rawContractionFactor (tailDegreeProfile d)
                            (i.succAbove j))) (j.predAbove i)
                        (rawSecondContractionFactor (tailDegreeProfile d)
                          (i.succAbove j) (j.predAbove i))) =
                    finFamilyList (recursiveMergedFactor
                      (recursiveMergedFactor (factorModule d) (i.succAbove j).succ
                        (rawContractionFactor d (i.succAbove j).succ))
                      (j.predAbove i).succ
                      (rawSecondContractionFactor d (i.succAbove j).succ
                        (j.predAbove i).succ))
                  rw [hsecondMerged (i.succAbove j) (j.predAbove i)]
                  rfl)
              · exact (rawContractionAdjacentMergeData_tail_heq d i).symm
              · exact (rawSecondContractionMergeData_tail_heq d i j).symm
              · rw [Fin.succ_succAbove_succ]
                exact (rawContractionAdjacentMergeData_tail_heq d
                  (i.succAbove j)).symm
              · rw [Fin.succ_succAbove_succ, Fin.succ_predAbove_succ]
                exact (rawSecondContractionMergeData_tail_heq d
                  (i.succAbove j) (j.predAbove i)).symm

theorem rawContractionPair_target_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    finFamilyList
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
          (rawSecondContractionFactor d i j)) =
      finFamilyList
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) (i.succAbove j)
            (rawContractionFactor d (i.succAbove j))) (j.predAbove i)
          (rawSecondContractionFactor d (i.succAbove j) (j.predAbove i))) :=
  (rawContractionAdjacentMerge_pair_coherence d i j).target_eq

theorem rawContractionPair_tensorMap_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    HEq
      ((rawContractionAdjacentMergeData d i).tensorMap ≫
        (rawSecondContractionMergeData d i j).tensorMap)
      ((rawContractionAdjacentMergeData d (i.succAbove j)).tensorMap ≫
        (rawSecondContractionMergeData d (i.succAbove j)
          (j.predAbove i)).tensorMap) :=
  (rawContractionAdjacentMerge_pair_coherence d i j).tensorMap_heq


end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
