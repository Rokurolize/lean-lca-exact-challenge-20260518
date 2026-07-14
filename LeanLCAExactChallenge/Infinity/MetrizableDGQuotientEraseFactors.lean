import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientFoundation

/-! # Factors after erasing a Drinfeld intermediate object -/

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

theorem eraseVertexSuccAbove_internal (k : ℕ) (i : Fin (k + 1)) (q : Fin k) :
    i.succ.castSucc.succAbove q.castSucc.succ =
      (i.succAbove q).succ.castSucc := by
  change (i.succ).castSucc.succAbove (q.succ).castSucc = _
  rw [Fin.castSucc_succAbove_castSucc, Fin.succ_succAbove_succ]

theorem eraseVertexSuccAbove_last (k : ℕ) (i : Fin (k + 1)) :
    i.succ.castSucc.succAbove (Fin.last (k + 1)) = Fin.last (k + 2) := by
  apply Fin.ext
  simp [Fin.succAbove]

def erasePosition {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) : Fin ((eraseIntermediate w i).length + 1) :=
  Fin.cast (eraseIntermediate_length w i).symm i

def eraseLift {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin (eraseIntermediate w i).length) : Fin w.length :=
  Fin.cast (eraseIntermediate_length w i) ((erasePosition w i).succAbove j)

theorem eraseIntermediate_twice_swap
    {X Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    eraseIntermediate
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) i) j =
      eraseIntermediate
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          (i.succAbove j))
        (j.predAbove i) := by
  cases k with
  | zero => rfl
  | succ k =>
      change
        ({ length := k + 1,
            intermediate := fun r ↦ intermediate (i.succAbove (j.succAbove r)) } :
          DrinfeldWord X Y) =
        { length := k + 1,
          intermediate := fun r ↦ intermediate
            ((i.succAbove j).succAbove ((j.predAbove i).succAbove r)) }
      congr 1
      funext r
      rw [Fin.succAbove_succAbove_succAbove_predAbove]

theorem contractedArrowDegree_twice_swap {k : ℕ}
    (a : Fin (k + 3) → ℤ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
    contractedArrowDegree (contractedArrowDegree a i) j =
      contractedArrowDegree (contractedArrowDegree a (i.succAbove j))
        (j.predAbove i) := by
  funext r
  have hmain :
      i.castSucc.succAbove (j.castSucc.succAbove r) =
        (i.succAbove j).castSucc.succAbove
          ((j.predAbove i).castSucc.succAbove r) := by
    simpa only [Fin.castSucc_succAbove_castSucc,
      Fin.castSucc_predAbove_castSucc] using
        (Fin.succAbove_succAbove_succAbove_predAbove
          i.castSucc j.castSucc r).symm
  unfold contractedArrowDegree
  rw [hmain]
  by_cases hleft : i = j.castSucc
  · subst i
    have hiff : j.castSucc.succAbove r = j.succ ↔ r = j := by
      rw [← Fin.succAbove_castSucc_self j]
      exact Fin.succAbove_right_inj
    by_cases hr : r = j
    · simp [hr, Fin.ne_of_lt j.castSucc_lt_succ,
        (Fin.ne_of_lt j.castSucc_lt_succ).symm]
      ring
    · simp [hr, hiff]
  · by_cases hright : i = j.succ
    · subst i
      have hiff : j.castSucc.succAbove r = j.succ ↔ r = j := by
        rw [← Fin.succAbove_castSucc_self j]
        exact Fin.succAbove_right_inj
      by_cases hr : r = j
      · simp [hr, Fin.ne_of_lt j.castSucc_lt_succ,
          (Fin.ne_of_lt j.castSucc_lt_succ).symm]
        ring
      · simp [hr, hiff]
    · have hfirst : j.castSucc.succAbove r = i ↔ r = j.predAbove i := by
        constructor
        · intro hr
          calc
            r = j.predAbove (j.castSucc.succAbove r) :=
              (Fin.predAbove_succAbove j r).symm
            _ = j.predAbove i := congrArg (j.predAbove ·) hr
        · rintro rfl
          exact Fin.succAbove_predAbove hleft
      have hgap : i.succAbove j ≠ (j.predAbove i).castSucc := by
        intro heq
        by_cases h : j.castSucc < i
        · rw [Fin.succAbove_of_castSucc_lt i j h,
            Fin.predAbove_of_castSucc_lt j i h] at heq
          have hj : j = i.pred (Fin.ne_zero_of_lt h) :=
            Fin.castSucc_injective _ heq
          apply hright
          rw [hj]
          exact (Fin.succ_pred i _).symm
        · have hle : i ≤ j.castSucc := Fin.not_lt.mp h
          rw [Fin.succAbove_of_le_castSucc i j hle,
            Fin.predAbove_of_le_castSucc j i hle,
            Fin.castSucc_castPred] at heq
          exact hright heq.symm
      have hsecond :
          (j.predAbove i).castSucc.succAbove r = i.succAbove j ↔ r = j := by
        constructor
        · intro hr
          calc
            r = (j.predAbove i).predAbove
                ((j.predAbove i).castSucc.succAbove r) :=
              (Fin.predAbove_succAbove (j.predAbove i) r).symm
            _ = (j.predAbove i).predAbove (i.succAbove j) :=
              congrArg ((j.predAbove i).predAbove ·) hr
            _ = j := Fin.predAbove_predAbove_succAbove i j
        · intro hr
          subst r
          have hpred : (j.predAbove i).predAbove (i.succAbove j) = j :=
            Fin.predAbove_predAbove_succAbove i j
          calc
            (j.predAbove i).castSucc.succAbove j =
                (j.predAbove i).castSucc.succAbove
                  ((j.predAbove i).predAbove (i.succAbove j)) :=
              congrArg ((j.predAbove i).castSucc.succAbove ·) hpred.symm
            _ = i.succAbove j := Fin.succAbove_predAbove hgap
      have hpositions : j ≠ j.predAbove i := by
        intro heq
        by_cases h : j.castSucc < i
        · rw [Fin.predAbove_of_castSucc_lt j i h] at heq
          apply hright
          rw [heq]
          exact (Fin.succ_pred i _).symm
        · have hle : i ≤ j.castSucc := Fin.not_lt.mp h
          rw [Fin.predAbove_of_le_castSucc j i hle] at heq
          apply hleft
          rw [heq, Fin.castSucc_castPred]
      have hmerged :
          (i.succAbove j).succAbove (j.predAbove i) = i :=
        Fin.succAbove_succAbove_predAbove i j
      have hleft' : j.castSucc ≠ i := Ne.symm hleft
      have hgap' : (j.predAbove i).castSucc ≠ i.succAbove j := Ne.symm hgap
      by_cases hrj : r = j <;> by_cases hrs : r = j.predAbove i <;>
        simp_all

theorem DegreeProfile.castWord_arrowDegree
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (h : w = v) (j : Fin (v.length + 1)) :
    (d.castWord h).arrowDegree j =
      d.arrowDegree
        (Fin.cast (congrArg (fun z : DrinfeldWord X Y ↦ z.length + 1) h).symm j) := by
  subst v
  rfl

theorem DegreeProfile.contract_contract_swap
    {X Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory)
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ((d.contract i).contract j).castWord
        (eraseIntermediate_twice_swap intermediate i j) =
      (d.contract (i.succAbove j)).contract (j.predAbove i) := by
  apply DegreeProfile.ext
  funext r
  have hfirst := eraseIntermediate_length
    ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
    (i.succAbove j)
  change (eraseIntermediate
    ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
    (i.succAbove j)).length + 1 = k + 2 at hfirst
  have hsecond := eraseIntermediate_length
    (eraseIntermediate
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
      (i.succAbove j)) (j.predAbove i)
  change (eraseIntermediate
    (eraseIntermediate
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
      (i.succAbove j)) (j.predAbove i)).length + 1 =
    (eraseIntermediate
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
      (i.succAbove j)).length at hsecond
  have hlength :
      ((eraseIntermediate
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          (i.succAbove j)) (j.predAbove i)).length + 1) = k + 1 := by
    omega
  let r' : Fin (k + 1) := Fin.cast hlength r
  rw [DegreeProfile.castWord_arrowDegree]
  simp only [DegreeProfile.contract, Fin.cast_eq_self]
  convert congrFun (contractedArrowDegree_twice_swap d.arrowDegree i j) r' using 1
  · congr 1
  · congr 1

/-- The factor of the erased word, viewed as a position among the old intermediate
objects.  This is also the index of the first old arrow contributing to that factor. -/
def eraseFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) : Fin w.length :=
  Fin.cast (eraseIntermediate_length w i) j

def survivingOldFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) :
    Fin (w.length + 1) :=
  i.castSucc.succAbove (eraseFactorIndex w i j)

theorem sum_univ_eq_left_add_sum_survivingOldFactorIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y}
    {A : Type*} [AddCommMonoid A] (i : Fin w.length)
    (f : Fin (w.length + 1) → A) :
    ∑ q, f q = f i.castSucc +
      ∑ j, f (survivingOldFactorIndex w i j) := by
  rw [Fin.sum_univ_succAbove f i.castSucc]
  congr 1
  symm
  apply Fintype.sum_equiv (finCongr (eraseIntermediate_length w i))
  intro j
  rfl

theorem survivingOldFactorIndex_ne_left
    {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) :
    survivingOldFactorIndex w i j ≠ i.castSucc :=
  Fin.succAbove_ne i.castSucc (eraseFactorIndex w i j)

theorem survivingOldFactorIndex_eq_right_iff
    {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) :
    survivingOldFactorIndex w i j = i.succ ↔ j = erasePosition w i := by
  unfold survivingOldFactorIndex
  rw [← Fin.succAbove_castSucc_self i, Fin.succAbove_right_inj]
  constructor
  · intro h
    apply Fin.ext
    change j.val = i.val
    exact congrArg Fin.val h
  · rintro rfl
    apply Fin.ext
    rfl

theorem survivingOldFactorIndex_injective
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    Function.Injective (survivingOldFactorIndex w i) := by
  intro j r h
  unfold survivingOldFactorIndex at h
  have hi : eraseFactorIndex w i j = eraseFactorIndex w i r :=
    Fin.succAbove_right_injective h
  apply Fin.ext
  exact congrArg (fun x : Fin w.length ↦ x.val) hi

theorem survivingOldFactorIndex_of_before
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    survivingOldFactorIndex w i j = (eraseFactorIndex w i j).castSucc := by
  unfold survivingOldFactorIndex
  rw [Fin.succAbove_of_castSucc_lt]
  simpa using h

theorem survivingOldFactorIndex_of_after
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    survivingOldFactorIndex w i j = (eraseFactorIndex w i j).succ := by
  unfold survivingOldFactorIndex
  rw [Fin.succAbove_of_le_castSucc]
  exact h.le

theorem DegreeProfile.raise_surviving_contract
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    (d.raise (survivingOldFactorIndex w i j)).contract i =
      (d.contract i).raise j := by
  apply DegreeProfile.ext
  funext r
  change contractedArrowDegree
      (fun q ↦ d.arrowDegree q +
        if q = i.castSucc.succAbove (eraseFactorIndex w i j) then 1 else 0) i
        (Fin.cast (eraseIntermediate_length w i) r) =
      contractedArrowDegree d.arrowDegree i
          (Fin.cast (eraseIntermediate_length w i) r) +
        if r = j then 1 else 0
  rw [contractedArrowDegree_raise_succAbove]
  simp [eraseFactorIndex]

theorem DegreeProfile.raise_left_contract
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (d.raise i.castSucc).contract i =
      (d.contract i).raise (erasePosition w i) := by
  apply DegreeProfile.ext
  funext r
  change contractedArrowDegree
      (fun q ↦ d.arrowDegree q + if q = i.castSucc then 1 else 0) i
        (Fin.cast (eraseIntermediate_length w i) r) =
      contractedArrowDegree d.arrowDegree i
          (Fin.cast (eraseIntermediate_length w i) r) +
        if r = erasePosition w i then 1 else 0
  rw [contractedArrowDegree_raise_left]
  change contractedArrowDegree d.arrowDegree i
        (Fin.cast (eraseIntermediate_length w i) r) +
      (if Fin.cast (eraseIntermediate_length w i) r = i then 1 else 0) =
    contractedArrowDegree d.arrowDegree i
        (Fin.cast (eraseIntermediate_length w i) r) +
      if r = erasePosition w i then 1 else 0
  by_cases h : Fin.cast (eraseIntermediate_length w i) r = i
  · have hr : r = erasePosition w i := by
      apply Fin.ext
      change r.val = i.val
      exact congrArg (fun x : Fin w.length ↦ x.val) h
    rw [if_pos h, if_pos hr]
  · have hr : r ≠ erasePosition w i := by
      intro hr
      subst r
      apply h
      apply Fin.ext
      rfl
    rw [if_neg h, if_neg hr]

@[simp]
theorem eraseFactorIndex_erasePosition
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    eraseFactorIndex w i (erasePosition w i) = i := by
  apply Fin.ext
  rfl

theorem eraseFactorIndex_castSucc
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    Fin.cast (congrArg (fun n ↦ n + 1) (eraseIntermediate_length w i)) j.castSucc =
      (eraseFactorIndex w i j).castSucc := by
  apply Fin.ext
  rfl

theorem eraseFactorIndex_succ
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    Fin.cast (congrArg (fun n ↦ n + 1) (eraseIntermediate_length w i)) j.succ =
      (eraseFactorIndex w i j).succ := by
  apply Fin.ext
  rfl

/-- The intermediate vertices after erasure are enumerated by `succAbove`. -/
theorem eraseIntermediate_object
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length) :
    (eraseIntermediate w i).object j =
      w.object (eraseLift w i j) := by
  cases w with
  | mk n intermediate =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero => exact Fin.elim0 j
          | succ k => rfl

theorem eraseIntermediate_vertex
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 2)) :
    (eraseIntermediate w i).vertex j =
      w.vertex (i.succ.castSucc.succAbove
        (Fin.cast (congrArg (fun n ↦ n + 1) (eraseIntermediate_length w i)) j)) := by
  cases w with
  | mk n intermediate =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero =>
              change Fin 1 at i
              change Fin 2 at j
              fin_cases i
              fin_cases j <;> rfl
          | succ k =>
              change Fin (k + 2) at i
              change Fin (k + 3) at j
              refine Fin.cases ?_ (fun j ↦ ?_) j
              · rfl
              · refine Fin.lastCases ?_ (fun q ↦ ?_) j
                · have hidx : i.succ.castSucc.succAbove
                        (Fin.cast (congrArg (fun n ↦ n + 1)
                          (eraseIntermediate_length
                            ({ length := k + 2, intermediate := intermediate } :
                              DrinfeldWord X Y) i)) (Fin.last (k + 1)).succ) =
                    Fin.last (k + 3) := by
                      convert eraseVertexSuccAbove_last (k + 1) i
                      all_goals apply Fin.ext
                      all_goals rfl
                  rw [hidx]
                  rw [show (Fin.last (k + 1)).succ = Fin.last (k + 2) by
                    apply Fin.ext; rfl]
                  exact (vertex_last (eraseIntermediate
                      ({ length := k + 2, intermediate := intermediate } :
                        DrinfeldWord X Y) i)).trans (vertex_last _).symm
                · have hidx : i.succ.castSucc.succAbove
                        (Fin.cast (congrArg (fun n ↦ n + 1)
                          (eraseIntermediate_length
                            ({ length := k + 2, intermediate := intermediate } :
                              DrinfeldWord X Y) i)) q.castSucc.succ) =
                      (i.succAbove q).succ.castSucc := by
                      convert eraseVertexSuccAbove_internal (k + 1) i q
                      all_goals apply Fin.ext
                      all_goals rfl
                  rw [hidx]
                  simp only [vertex, eraseIntermediate, Fin.castSucc_succ]
                  unfold object
                  simp only [Fin.cases_succ, Fin.lastCases_castSucc]

theorem eraseLift_of_before
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : j.castSucc < erasePosition w i) :
    eraseLift w i j =
      Fin.cast (eraseIntermediate_length w i) j.castSucc := by
  unfold eraseLift
  rw [Fin.succAbove_of_castSucc_lt _ _ h]

theorem eraseLift_of_after
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : erasePosition w i ≤ j.castSucc) :
    eraseLift w i j =
      Fin.cast (eraseIntermediate_length w i) j.succ := by
  unfold eraseLift
  rw [Fin.succAbove_of_le_castSucc _ _ h]

theorem eraseIntermediate_object_of_before
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : j.castSucc < erasePosition w i) :
    (eraseIntermediate w i).object j =
      w.object (Fin.cast (eraseIntermediate_length w i) j.castSucc) := by
  rw [eraseIntermediate_object, eraseLift_of_before w i j h]

theorem eraseIntermediate_object_of_after
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : erasePosition w i ≤ j.castSucc) :
    (eraseIntermediate w i).object j =
      w.object (Fin.cast (eraseIntermediate_length w i) j.succ) := by
  rw [eraseIntermediate_object, eraseLift_of_after w i j h]

/-- Before the contracted position, erasure preserves the source of an arrow factor. -/
theorem eraseIntermediate_arrowSource_of_before
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    (eraseIntermediate w i).arrowSource j =
      w.arrowSource (eraseFactorIndex w i j).castSucc := by
  unfold arrowSource
  rw [eraseIntermediate_vertex]
  rw [eraseFactorIndex_castSucc]
  congr 1
  rw [Fin.succAbove_of_castSucc_lt]
  simpa using h.le

/-- Before the contracted position, erasure preserves the target of an arrow factor. -/
theorem eraseIntermediate_arrowTarget_of_before
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    (eraseIntermediate w i).arrowTarget j =
      w.arrowTarget (eraseFactorIndex w i j).castSucc := by
  unfold arrowTarget
  rw [eraseIntermediate_vertex]
  rw [eraseFactorIndex_succ]
  congr 1
  apply Fin.ext
  rw [Fin.succAbove_of_succ_le _ _ (by
    change (eraseFactorIndex w i j).val + 2 ≤ i.val + 1
    omega)]
  rfl

/-- The source of the merged factor is the source of the arrow immediately before the
erased intermediate object. -/
theorem eraseIntermediate_arrowSource_at
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    (eraseIntermediate w i).arrowSource (erasePosition w i) =
      w.arrowSource i.castSucc := by
  unfold arrowSource
  rw [eraseIntermediate_vertex]
  congr 1
  apply Fin.ext
  simp [Fin.succAbove, erasePosition]

/-- The target of the merged factor is the target of the arrow immediately after the
erased intermediate object. -/
theorem eraseIntermediate_arrowTarget_at
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    (eraseIntermediate w i).arrowTarget (erasePosition w i) =
      w.arrowTarget i.succ := by
  unfold arrowTarget
  rw [eraseIntermediate_vertex]
  congr 1
  apply Fin.ext
  simp [Fin.succAbove, erasePosition]

/-- After the contracted position, an erased arrow factor is the successor of its old
position. -/
theorem eraseIntermediate_arrowSource_of_after
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    (eraseIntermediate w i).arrowSource j =
      w.arrowSource (eraseFactorIndex w i j).succ := by
  unfold arrowSource
  rw [eraseIntermediate_vertex]
  rw [eraseFactorIndex_castSucc]
  congr 1
  apply Fin.ext
  rw [Fin.succAbove_of_le_castSucc _ _ (by
    change i.val + 1 ≤ (eraseFactorIndex w i j).val
    omega)]
  rfl

/-- After the contracted position, an erased arrow factor is the successor of its old
position. -/
theorem eraseIntermediate_arrowTarget_of_after
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    (eraseIntermediate w i).arrowTarget j =
      w.arrowTarget (eraseFactorIndex w i j).succ := by
  unfold arrowTarget
  rw [eraseIntermediate_vertex]
  rw [eraseFactorIndex_succ]
  congr 1
  rw [Fin.succAbove_of_lt_succ]
  simpa using h.le

theorem contract_arrowDegree_of_before
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    (d.contract i).arrowDegree j =
      d.arrowDegree (eraseFactorIndex w i j).castSucc := by
  change contractedArrowDegree d.arrowDegree i (eraseFactorIndex w i j) = _
  simp only [contractedArrowDegree]
  rw [Fin.succAbove_castSucc_of_lt _ _ h]
  simp [h.ne]

theorem contract_arrowDegree_at
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (d.contract i).arrowDegree (erasePosition w i) =
      d.arrowDegree i.castSucc + d.arrowDegree i.succ := by
  change contractedArrowDegree d.arrowDegree i
    (eraseFactorIndex w i (erasePosition w i)) = _
  rw [eraseFactorIndex_erasePosition, contractedArrowDegree_self, add_comm]

theorem contract_arrowDegree_of_after
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    (d.contract i).arrowDegree j =
      d.arrowDegree (eraseFactorIndex w i j).succ := by
  change contractedArrowDegree d.arrowDegree i (eraseFactorIndex w i j) = _
  simp only [contractedArrowDegree]
  rw [Fin.succAbove_castSucc_of_le _ _ h.le]
  simp [h.ne']

/-- Away from and before a contraction, the corresponding homogeneous Hom module is
canonically unchanged. -/
def contractFactorModuleBeforeIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    factorModule (d.contract i) j ≅
      factorModule d (eraseFactorIndex w i j).castSucc := by
  apply eqToIso
  simp only [factorModule]
  rw [eraseIntermediate_arrowSource_of_before w i j h,
    eraseIntermediate_arrowTarget_of_before w i j h,
    contract_arrowDegree_of_before d i j h]

/-- At the contraction position, the new factor is the homogeneous target of composition
of the two adjacent old factors. -/
def contractFactorModuleAtIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    factorModule (d.contract i) (erasePosition w i) ≅
      (dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ) := by
  apply eqToIso
  simp only [factorModule]
  rw [eraseIntermediate_arrowSource_at w i, eraseIntermediate_arrowTarget_at w i,
    contract_arrowDegree_at d i]

/-- Away from and after a contraction, the corresponding homogeneous Hom module is the
successor old factor. -/
def contractFactorModuleAfterIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    factorModule (d.contract i) j ≅
      factorModule d (eraseFactorIndex w i j).succ := by
  apply eqToIso
  simp only [factorModule]
  rw [eraseIntermediate_arrowSource_of_after w i j h,
    eraseIntermediate_arrowTarget_of_after w i j h,
    contract_arrowDegree_of_after d i j h]

/-- Identity transport from an old factor before the contraction to its erased-word
counterpart. -/
def contractFactorBeforeTransport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : eraseFactorIndex w i j < i) :
    Quiver.Hom (factorModule d (eraseFactorIndex w i j).castSucc)
      (factorModule (d.contract i) j) :=
  (contractFactorModuleBeforeIso d i j h).inv

/-- Identity transport from an old factor after the contraction to its erased-word
counterpart. -/
def contractFactorAfterTransport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1))
    (h : i < eraseFactorIndex w i j) :
    Quiver.Hom (factorModule d (eraseFactorIndex w i j).succ)
      (factorModule (d.contract i) j) :=
  (contractFactorModuleAfterIso d i j h).inv

/-- Homogeneous composition of the two factors adjacent to the erased intermediate
object, with its codomain transported to the contracted factor module. -/
def contractFactorComposition
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      (factorModule (d.contract i) (erasePosition w i)) :=
  adjacentFactorComposition d i ≫ (contractFactorModuleAtIso d i).inv

/-- The factor list obtained by replacing the two entries adjacent to `i` by `P`. -/
def mergedFactor {k : ℕ} (M : Fin (k + 1) → ModuleCat.{0} ℤ)
    (i : Fin k) (P : ModuleCat.{0} ℤ) (j : Fin k) : ModuleCat.{0} ℤ :=
  if j < i then M j.castSucc else if j = i then P else M j.succ

/-- `AdjacentMergeData` for an arbitrary finite family, with the merge at a specified
finite position. -/
def adjacentMergeDataOfFn : {k : ℕ} → (M : Fin (k + 1) → ModuleCat.{0} ℤ) →
    (i : Fin k) → (P : ModuleCat.{0} ℤ) →
    Quiver.Hom (M i.castSucc ⊗ M i.succ) P →
    AdjacentMergeData (finFamilyList M) (finFamilyList (mergedFactor M i P))
  | 0, _, i, _, _ => Fin.elim0 i
  | k + 1, M, i, P, f => by
      cases i using Fin.cases with
      | zero =>
          simpa [finFamilyList, mergedFactor] using
            (AdjacentMergeData.head
              (Ms := finFamilyList (fun q : Fin k ↦ M q.succ.succ)) f)
      | succ q =>
          let tailM : Fin (k + 1) → ModuleCat.{0} ℤ := fun j ↦ M j.succ
          have ftail : Quiver.Hom (tailM q.castSucc ⊗ tailM q.succ) P := by
            simpa [tailM] using f
          have tail := adjacentMergeDataOfFn tailM q P ftail
          have hmerged : finFamilyList (mergedFactor M q.succ P) =
              M 0 :: finFamilyList (mergedFactor tailM q P) := by
            rw [finFamilyList]
            congr 1
            apply congrArg finFamilyList
            funext j
            by_cases hlt : j < q
            · simp only [mergedFactor, Fin.succ_lt_succ_iff, hlt, ↓reduceIte, tailM]
              congr 1
            · by_cases heq : j = q
              · subst j
                simp [mergedFactor, tailM]
              · simp only [mergedFactor, Fin.succ_lt_succ_iff, hlt, ↓reduceIte,
                  Fin.succ_inj, heq, tailM]
          rw [hmerged]
          simpa only [finFamilyList, tailM] using AdjacentMergeData.tail tail

def mergedFactorMap {k : ℕ}
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    (P P' : ModuleCat.{0} ℤ) (a : (j : Fin (k + 1)) → Quiver.Hom (M j) (N j))
    (g : Quiver.Hom P P') (j : Fin k) :
    Quiver.Hom (mergedFactor M i P j) (mergedFactor N i P' j) := by
  by_cases hlt : j < i
  · simpa [mergedFactor, hlt] using a j.castSucc
  · by_cases heq : j = i
    · subst j
      simpa [mergedFactor] using g
    · simpa [mergedFactor, hlt, heq] using a j.succ

def recursiveMergedFactor : {k : ℕ} →
    (Fin (k + 1) → ModuleCat.{0} ℤ) → Fin k → ModuleCat.{0} ℤ →
      Fin k → ModuleCat.{0} ℤ
  | 0, _, i, _ => Fin.elim0 i
  | k + 1, M, i, P => by
      cases i using Fin.cases with
      | zero => exact Fin.cases P (fun j : Fin k ↦ M j.succ.succ)
      | succ q =>
          exact Fin.cases (M 0)
            (recursiveMergedFactor (fun j : Fin (k + 1) ↦ M j.succ) q P)

theorem recursiveMergedFactor_eq_mergedFactor : {k : ℕ} →
    (M : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P : ModuleCat.{0} ℤ) →
      recursiveMergedFactor M i P = mergedFactor M i P
  | 0, _, i, _ => Fin.elim0 i
  | k + 1, M, i, P => by
      cases i using Fin.cases with
      | zero =>
          funext j
          cases j using Fin.cases with
          | zero => simp [recursiveMergedFactor, mergedFactor]
          | succ j => simp [recursiveMergedFactor, mergedFactor]
      | succ q =>
          funext j
          cases j using Fin.cases with
          | zero => simp [recursiveMergedFactor, mergedFactor]
          | succ j =>
              change recursiveMergedFactor
                  (fun r : Fin (k + 1) ↦ M r.succ) q P j =
                mergedFactor M q.succ P j.succ
              rw [congrFun (recursiveMergedFactor_eq_mergedFactor
                (fun r : Fin (k + 1) ↦ M r.succ) q P) j]
              by_cases hlt : j < q
              · simp [mergedFactor, hlt]
              · by_cases heq : j = q
                · subst j
                  simp [mergedFactor]
                · simp [mergedFactor, hlt, heq]

def recursiveAdjacentMergeDataOfFn : {k : ℕ} →
    (M : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P : ModuleCat.{0} ℤ) → Quiver.Hom (M i.castSucc ⊗ M i.succ) P →
      AdjacentMergeData (finFamilyList M)
        (finFamilyList (recursiveMergedFactor M i P))
  | 0, _, i, _, _ => Fin.elim0 i
  | k + 1, M, i, P, f => by
      cases i using Fin.cases with
      | zero =>
          simpa [finFamilyList, recursiveMergedFactor] using
            (AdjacentMergeData.head
              (Ms := finFamilyList (fun q : Fin k ↦ M q.succ.succ)) f)
      | succ q =>
          let tailM : Fin (k + 1) → ModuleCat.{0} ℤ := fun j ↦ M j.succ
          have ftail : Quiver.Hom (tailM q.castSucc ⊗ tailM q.succ) P := by
            simpa [tailM] using f
          simpa [finFamilyList, recursiveMergedFactor, tailM] using
            AdjacentMergeData.tail
              (recursiveAdjacentMergeDataOfFn tailM q P ftail)

def recursiveMergedFactorMap : {k : ℕ} →
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P P' : ModuleCat.{0} ℤ) →
    ((j : Fin (k + 1)) → Quiver.Hom (M j) (N j)) → Quiver.Hom P P' →
      (j : Fin k) →
        Quiver.Hom (recursiveMergedFactor M i P j)
          (recursiveMergedFactor N i P' j)
  | 0, _, _, i, _, _, _, _ => Fin.elim0 i
  | k + 1, M, N, i, P, P', a, g => by
      cases i using Fin.cases with
      | zero => exact Fin.cases g (fun j : Fin k ↦ a j.succ.succ)
      | succ q =>
          exact Fin.cases (a 0)
            (recursiveMergedFactorMap
              (fun j : Fin (k + 1) ↦ M j.succ)
              (fun j : Fin (k + 1) ↦ N j.succ) q P P'
              (fun j ↦ a j.succ) g)

theorem recursiveAdjacentMergeDataOfFn_naturality : {k : ℕ} →
    (M N : Fin (k + 1) → ModuleCat.{0} ℤ) → (i : Fin k) →
    (P P' : ModuleCat.{0} ℤ) →
    (f : Quiver.Hom (M i.castSucc ⊗ M i.succ) P) →
    (f' : Quiver.Hom (N i.castSucc ⊗ N i.succ) P') →
    (a : (j : Fin (k + 1)) → Quiver.Hom (M j) (N j)) →
    (g : Quiver.Hom P P') → ((a i.castSucc ⊗ₘ a i.succ) ≫ f' = f ≫ g) →
    AdjacentMergeNaturality
      (recursiveAdjacentMergeDataOfFn M i P f)
      (recursiveAdjacentMergeDataOfFn N i P' f')
      (TensorMapData.ofFn M N a)
      (TensorMapData.ofFn (recursiveMergedFactor M i P)
        (recursiveMergedFactor N i P')
        (recursiveMergedFactorMap M N i P P' a g))
  | 0, _, _, i, _, _, _, _, _, _, _ => Fin.elim0 i
  | k + 1, M, N, i, P, P', f, f', a, g, h => by
      cases i using Fin.cases with
      | zero =>
          let tailMap := TensorMapData.ofFn
            (fun j : Fin k ↦ M j.succ.succ)
            (fun j : Fin k ↦ N j.succ.succ)
            (fun j ↦ a j.succ.succ)
          simpa [recursiveAdjacentMergeDataOfFn, recursiveMergedFactor,
            recursiveMergedFactorMap, TensorMapData.ofFn, finFamilyList, tailMap] using
              AdjacentMergeNaturality.head f f' (a 0) (a 1) g tailMap h
      | succ q =>
          let tailM : Fin (k + 1) → ModuleCat.{0} ℤ := fun j ↦ M j.succ
          let tailN : Fin (k + 1) → ModuleCat.{0} ℤ := fun j ↦ N j.succ
          let tailA : (j : Fin (k + 1)) → Quiver.Hom (tailM j) (tailN j) :=
            fun j ↦ a j.succ
          have naturality := recursiveAdjacentMergeDataOfFn_naturality
            tailM tailN q P P' f f' tailA g h
          simpa [recursiveAdjacentMergeDataOfFn, recursiveMergedFactor,
            recursiveMergedFactorMap, TensorMapData.ofFn, finFamilyList,
            tailM, tailN, tailA] using
              AdjacentMergeNaturality.tail (a 0) naturality

/-- Regard an old intermediate-object position as a factor position of the erased word. -/
def uneraseFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i j : Fin w.length) : Fin ((eraseIntermediate w i).length + 1) :=
  ⟨j, by
    rw [eraseIntermediate_length]
    exact j.isLt⟩

@[simp]
theorem eraseFactorIndex_uneraseFactorIndex
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i j : Fin w.length) :
    eraseFactorIndex w i (uneraseFactorIndex w i j) = j := by
  apply Fin.ext
  rfl

@[simp]
theorem uneraseFactorIndex_eraseFactorIndex
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length)
    (j : Fin ((eraseIntermediate w i).length + 1)) :
    uneraseFactorIndex w i (eraseFactorIndex w i j) = j := by
  apply Fin.ext
  rfl

@[simp]
theorem uneraseFactorIndex_self
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    uneraseFactorIndex w i i = erasePosition w i := by
  apply Fin.ext
  rfl

theorem contract_suffix_sum_eq_oldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    ∑ j ∈ Finset.univ.filter
        (fun j : Fin ((eraseIntermediate w i).length + 1) ↦
          uneraseFactorIndex w i q < j),
        (d.contract i).arrowDegree j =
      ∑ r ∈ Finset.univ.filter (fun r : Fin w.length ↦ q < r),
        contractedArrowDegree d.arrowDegree i r := by
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Fintype.sum_equiv (finCongr (eraseIntermediate_length w i))
  intro j
  rfl

/-- Contracted factor family, indexed by the original intermediate positions. -/
def contractedFactorAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin w.length) : ModuleCat.{0} ℤ :=
  factorModule (d.contract i) (uneraseFactorIndex w i j)

@[simp]
theorem contractedFactorAtOldIndex_eq_factorModule
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) :
    contractedFactorAtOldIndex d i = factorModule (d.contract i) := by
  rfl

/-- At the merged old index, the contracted factor is the homogeneous adjacent-composition
target. -/
def contractFactorAtOldIndexIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractedFactorAtOldIndex d i i ≅
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) := by
  simpa only [contractedFactorAtOldIndex, uneraseFactorIndex_self] using
    contractFactorModuleAtIso d i

/-- Adjacent composition transported only to the merged old-index factor. -/
def contractionMergeAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      (contractedFactorAtOldIndex d i i) :=
  adjacentFactorComposition d i ≫ (contractFactorAtOldIndexIso d i).inv

/-- The canonical adjacent merge of the old factor family.  Its target is the contracted
family indexed through the old finite ordinal, with the non-merged entries still represented
by their canonically identical old modules. -/
def contractionAdjacentMergeData
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeData (finFamilyList (factorModule d))
      (finFamilyList (mergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))) :=
  adjacentMergeDataOfFn (factorModule d) i (contractedFactorAtOldIndex d i i)
    (contractionMergeAtOldIndex d i)

/-- Pointwise transport from the output of the adjacent merge to the actual contracted
factor family. -/
def contractionMergedFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin w.length) :
    Quiver.Hom
      (mergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i) j)
      (contractedFactorAtOldIndex d i j) := by
  by_cases hlt : j < i
  · have hbefore : eraseFactorIndex w i (uneraseFactorIndex w i j) < i := by
      simpa using hlt
    simpa [mergedFactor, hlt, contractedFactorAtOldIndex] using
      contractFactorBeforeTransport d i (uneraseFactorIndex w i j) hbefore
  · by_cases heq : j = i
    · subst j
      simpa [mergedFactor] using (𝟙 (contractedFactorAtOldIndex d i i))
    · have hafter : i < eraseFactorIndex w i (uneraseFactorIndex w i j) := by
        simp only [eraseFactorIndex_uneraseFactorIndex]
        exact lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm heq)
      simpa [mergedFactor, hlt, heq, contractedFactorAtOldIndex] using
        contractFactorAfterTransport d i (uneraseFactorIndex w i j) hafter

def recursiveContractionAdjacentMergeData
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeData (finFamilyList (factorModule d))
      (finFamilyList
        (recursiveMergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))) :=
  recursiveAdjacentMergeDataOfFn (factorModule d) i (contractedFactorAtOldIndex d i i)
    (contractionMergeAtOldIndex d i)

theorem recursiveContractionMergedFactor_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) :
    recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) q =
      contractedFactorAtOldIndex d i q := by
  rw [recursiveMergedFactor_eq_mergedFactor]
  by_cases hlt : q < i
  · have hbefore :
        eraseFactorIndex w i (uneraseFactorIndex w i q) < i := by
      simpa using hlt
    simp only [mergedFactor, hlt, if_true, contractedFactorAtOldIndex,
      factorModule]
    rw [eraseIntermediate_arrowSource_of_before w i
        (uneraseFactorIndex w i q) hbefore,
      eraseIntermediate_arrowTarget_of_before w i
        (uneraseFactorIndex w i q) hbefore,
      contract_arrowDegree_of_before d i
        (uneraseFactorIndex w i q) hbefore,
      eraseFactorIndex_uneraseFactorIndex]
  · by_cases heq : q = i
    · subst q
      simp [mergedFactor]
    · have hafter :
          i < eraseFactorIndex w i (uneraseFactorIndex w i q) := by
        rw [eraseFactorIndex_uneraseFactorIndex]
        exact lt_of_le_of_ne (Fin.not_lt.mp hlt) (Ne.symm heq)
      simp only [mergedFactor, hlt, heq, if_false,
        contractedFactorAtOldIndex, factorModule]
      rw [eraseIntermediate_arrowSource_of_after w i
          (uneraseFactorIndex w i q) hafter,
        eraseIntermediate_arrowTarget_of_after w i
          (uneraseFactorIndex w i q) hafter,
        contract_arrowDegree_of_after d i
          (uneraseFactorIndex w i q) hafter,
        eraseFactorIndex_uneraseFactorIndex]

def recursiveContractionMergedFactorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin w.length) :
    Quiver.Hom
      (recursiveMergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i) j)
      (contractedFactorAtOldIndex d i j) :=
  eqToHom (recursiveContractionMergedFactor_eq d i j)

def rawContractionFactor
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex
    (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
      (d.arrowDegree i.castSucc + d.arrowDegree i.succ)

abbrev tailWord
    {Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory) :
    DrinfeldWord (intermediate 0).obj Y where
  length := k
  intermediate := fun i ↦ intermediate i.succ

def tailDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile (tailWord (Y := Y) intermediate)
      (n - d.arrowDegree 0 + 1) where
  arrowDegree := fun i : Fin (k + 1) ↦ d.arrowDegree i.succ
  totalDegree := by
    have hd := d.totalDegree
    change (∑ i : Fin (k + 2), d.arrowDegree i) - (k + 1) = n at hd
    rw [Fin.sum_univ_succ] at hd
    change (∑ i : Fin (k + 1), d.arrowDegree i.succ) - k =
      n - d.arrowDegree 0 + 1
    omega

@[simp]
theorem tailDegreeProfile_arrowDegree
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (tailDegreeProfile d).arrowDegree i = d.arrowDegree i.succ := rfl

@[simp]
theorem tailWord_vertex
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    (i : Fin (k + 2)) :
    (tailWord (Y := Y) intermediate).vertex i =
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).vertex i.succ) := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · change (intermediate 0).obj =
      Fin.lastCases Y (fun i : Fin (k + 1) ↦ (intermediate i).obj) 0
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
  · refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · have htail : (Fin.last k).succ =
          Fin.last ((tailWord (Y := Y) intermediate).length + 1) := by
          apply Fin.ext
          rfl
      have horiginal : (Fin.last k).succ.succ =
          Fin.last
            (({ length := k + 1, intermediate := intermediate } :
              DrinfeldWord X Y).length + 1) := by
          apply Fin.ext
          rfl
      conv_lhs => rw [htail]
      conv_rhs => rw [horiginal]
      rw [vertex_last, vertex_last]
    · unfold vertex
      simp only [Fin.cases_succ]
      rw [show i.castSucc.succ = i.succ.castSucc by
        apply Fin.ext
        rfl]
      unfold object tailWord
      simp only [Fin.lastCases_castSucc]

@[simp]
theorem tailWord_arrowSource
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    (i : Fin (k + 1)) :
    (tailWord (Y := Y) intermediate).arrowSource i =
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).arrowSource i.succ) := by
  unfold arrowSource
  simpa only [Fin.castSucc_succ] using
    (tailWord_vertex (X := X) (Y := Y) (intermediate := intermediate) i.castSucc)

@[simp]
theorem tailWord_arrowTarget
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    (i : Fin (k + 1)) :
    (tailWord (Y := Y) intermediate).arrowTarget i =
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).arrowTarget i.succ) := by
  unfold arrowTarget
  exact tailWord_vertex (X := X) (Y := Y)
    (intermediate := intermediate) i.succ

@[simp]
theorem tailFactorModule
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    factorModule (tailDegreeProfile d) i = factorModule d i.succ := by
  unfold factorModule
  rw [tailWord_arrowSource, tailWord_arrowTarget,
    tailDegreeProfile_arrowDegree]

@[simp]
theorem tailRawContractionFactor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin k) :
    rawContractionFactor (tailDegreeProfile d) i =
      rawContractionFactor d i.succ := by
  unfold rawContractionFactor
  rw [tailWord_arrowSource (X := X) (Y := Y)
      (intermediate := intermediate) i.castSucc,
    tailWord_arrowTarget (X := X) (Y := Y)
      (intermediate := intermediate) i.succ]
  simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]

def rawTripleContractionFactor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (j : Fin (k + 1)) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex
    (({ length := k + 2, intermediate := intermediate } :
      DrinfeldWord X Y).arrowSource j.castSucc.castSucc)
    (({ length := k + 2, intermediate := intermediate } :
      DrinfeldWord X Y).arrowTarget j.succ.succ)).X
      (d.arrowDegree j.castSucc.castSucc +
        d.arrowDegree j.castSucc.succ + d.arrowDegree j.succ.succ)

@[simp]
theorem tailRawTripleContractionFactor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 3) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 3, intermediate := intermediate } : DrinfeldWord X Y) n)
    (j : Fin (k + 1)) :
    rawTripleContractionFactor (tailDegreeProfile d) j =
      rawTripleContractionFactor d j.succ := by
  unfold rawTripleContractionFactor
  simp only [tailWord_arrowSource (X := X) (Y := Y)
      (intermediate := intermediate) j.castSucc.castSucc,
    tailWord_arrowTarget (X := X) (Y := Y)
      (intermediate := intermediate) j.succ.succ]
  simp only [tailDegreeProfile_arrowDegree, Fin.castSucc_succ]

def rawContractionAdjacentMergeData
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeData (finFamilyList (factorModule d))
      (finFamilyList
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))) :=
  recursiveAdjacentMergeDataOfFn (factorModule d) i (rawContractionFactor d i)
    (adjacentFactorComposition d i)

def rawSecondContractionFactor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) : ModuleCat.{0} ℤ :=
  if i = j.castSucc ∨ i = j.succ then rawTripleContractionFactor d j
  else rawContractionFactor d (i.succAbove j)

def rawSecondContractionMerge
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    Quiver.Hom
      (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) j.castSucc ⊗
        recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) j.succ)
      (rawSecondContractionFactor d i j) := by
  rw [recursiveMergedFactor_eq_mergedFactor]
  by_cases hleft : i = j.castSucc
  · subst i
    have hnotlt : ¬ j.succ < j.castSucc :=
      not_lt_of_ge (Fin.le_of_lt Fin.castSucc_lt_succ)
    have hne : j.succ ≠ j.castSucc :=
      (Fin.ne_of_lt Fin.castSucc_lt_succ).symm
    simp only [mergedFactor, Fin.lt_irrefl, if_false,
      hnotlt, hne, rawSecondContractionFactor, true_or, if_true]
    simpa [rawContractionFactor, rawTripleContractionFactor, factorModule,
      Fin.castSucc_succ] using dgCochainCompTensorOfEq
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
          DrinfeldWord X Y) j.succ) rfl
  · by_cases hright : i = j.succ
    · subst i
      simp only [mergedFactor, Fin.castSucc_lt_succ, if_true,
        Fin.lt_irrefl, if_false,
        rawSecondContractionFactor, or_true]
      simpa [rawContractionFactor, rawTripleContractionFactor, factorModule,
        Fin.castSucc_succ] using dgCochainCompTensorOfEq
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
            DrinfeldWord X Y) j.castSucc) (by omega)
    · have hoverlap : ¬ (i = j.castSucc ∨ i = j.succ) := by
        simp [hleft, hright]
      by_cases hbefore : j.castSucc < i
      · have hjnext : j.succ < i := by
          have hval : j.val < i.val := hbefore
          have hneval : i.val ≠ j.val + 1 := by
            intro h
            apply hright
            apply Fin.ext
            simpa using h
          change j.val + 1 < i.val
          omega
        simpa [mergedFactor, hbefore, hjnext, rawSecondContractionFactor,
          hoverlap, Fin.succAbove_of_castSucc_lt i j hbefore,
          rawContractionFactor, factorModule, Fin.castSucc_succ] using
          adjacentFactorComposition d j.castSucc
      · have hafter : i < j.castSucc := by
          exact lt_of_le_of_ne (Fin.not_lt.mp hbefore) hleft
        have hafter' : i < j.succ := lt_trans hafter Fin.castSucc_lt_succ
        have hnotAfter : ¬ j.succ < i := not_lt_of_ge hafter'.le
        simpa [mergedFactor, hbefore, Ne.symm hleft, hnotAfter,
          Ne.symm hright,
          rawSecondContractionFactor, hoverlap,
          Fin.succAbove_of_le_castSucc i j hafter.le,
          rawContractionFactor, factorModule, Fin.castSucc_succ] using
          adjacentFactorComposition d j.succ

def rawSecondContractionMergeData
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    AdjacentMergeData
      (finFamilyList
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)))
      (finFamilyList
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
          (rawSecondContractionFactor d i j))) :=
  recursiveAdjacentMergeDataOfFn
    (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) j
    (rawSecondContractionFactor d i j) (rawSecondContractionMerge d i j)

def transportedSecondContractionMergeAtCanonical
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    Quiver.Hom
      (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i) j.castSucc ⊗
        recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i) j.succ)
      (contractedFactorAtOldIndex (d.contract i) j j) :=
  (recursiveContractionMergedFactorMap d i j.castSucc ⊗ₘ
      recursiveContractionMergedFactorMap d i j.succ) ≫
    contractionMergeAtOldIndex (d.contract i) j

def transportedSecondContractionMergeData
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    AdjacentMergeData
      (finFamilyList
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i)))
      (finFamilyList
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i)) j
          (contractedFactorAtOldIndex (d.contract i) j j))) :=
  recursiveAdjacentMergeDataOfFn
    (recursiveMergedFactor (factorModule d) i
      (contractedFactorAtOldIndex d i i)) j
    (contractedFactorAtOldIndex (d.contract i) j j)
    (transportedSecondContractionMergeAtCanonical d i j)

theorem transportedSecondContractionMerge_naturality
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    AdjacentMergeNaturality
      (transportedSecondContractionMergeData d i j)
      (recursiveContractionAdjacentMergeData (d.contract i) j)
      (TensorMapData.ofFn
        (recursiveMergedFactor (factorModule d) i
          (contractedFactorAtOldIndex d i i))
        (factorModule (d.contract i))
        (recursiveContractionMergedFactorMap d i))
      (TensorMapData.ofFn
        (recursiveMergedFactor
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i)) j
          (contractedFactorAtOldIndex (d.contract i) j j))
        (recursiveMergedFactor (factorModule (d.contract i)) j
          (contractedFactorAtOldIndex (d.contract i) j j))
        (recursiveMergedFactorMap
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i))
          (factorModule (d.contract i)) j
          (contractedFactorAtOldIndex (d.contract i) j j)
          (contractedFactorAtOldIndex (d.contract i) j j)
          (recursiveContractionMergedFactorMap d i)
          (𝟙 (contractedFactorAtOldIndex (d.contract i) j j)))) := by
  apply recursiveAdjacentMergeDataOfFn_naturality
  simp [transportedSecondContractionMergeAtCanonical]

@[simp]
theorem recursiveContractionMergedFactorMap_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    recursiveContractionMergedFactorMap d 0 0 =
      𝟙 (contractedFactorAtOldIndex d 0 0) := by
  unfold recursiveContractionMergedFactorMap
  have h : recursiveMergedFactor (factorModule d) 0
      (contractedFactorAtOldIndex d 0 0) 0 =
        contractedFactorAtOldIndex d 0 0 := rfl
  rw [Subsingleton.elim (recursiveContractionMergedFactor_eq d 0 0) h]
  rfl

def recursiveContractionMergedFactorsTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom
      (tensorModuleList
        (finFamilyList
          (recursiveMergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))))
      (tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i))) :=
  (TensorMapData.ofFn _ _ (recursiveContractionMergedFactorMap d i)).tensorMap

def recursiveContractionTensorMapAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d)
      (tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i))) :=
  (recursiveContractionAdjacentMergeData d i).tensorMap ≫
    recursiveContractionMergedFactorsTensorMap d i

/-- Tensor the pointwise before/middle/after transports following the adjacent merge. -/
def contractionMergedFactorsTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom
      (tensorModuleList
        (finFamilyList (mergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))))
      (tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i))) :=
  (TensorMapData.ofFn _ _ (contractionMergedFactorMap d i)).tensorMap

/-- The canonical contraction tensor map for an arbitrary word and degree profile, with the
contracted factors indexed by the old finite ordinal. -/
def contractionTensorMapAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d)
      (tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i))) :=
  recursiveContractionTensorMapAtOldIndex d i

theorem contractedFactorsOldIndex_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (contractedFactorAtOldIndex d i) =
      finFamilyList (factorModule (d.contract i)) := by
  cases w with
  | mk k intermediate =>
      cases k with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero =>
              fin_cases i
              rfl
          | succ k => rfl

/-- Canonical tensor-level reindexing from old contraction positions to the contracted
word's factor family. -/
def contractedFactorsOldIndexIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    tensorModuleList (finFamilyList (contractedFactorAtOldIndex d i)) ≅
      summandModule (d.contract i) :=
  eqToIso (congrArg tensorModuleList (contractedFactorsOldIndex_eq d i))

/-- The general contraction map between the actual word summands. -/
def contractionTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d) (summandModule (d.contract i)) :=
  contractionTensorMapAtOldIndex d i ≫
    (contractedFactorsOldIndexIso d i).hom

theorem adjacentMergeData_head_empty_tensorMap
    {M N P : ModuleCat.{0} ℤ} (f : Quiver.Hom (M ⊗ N) P) :
    (@AdjacentMergeData.head M N P [] f).tensorMap =
      (α_ M N (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
        (ρ_ (M ⊗ N)).hom ≫ f ≫ (ρ_ P).inv := by
  dsimp only [AdjacentMergeData.tensorMap, tensorModuleList, tensorModuleListOver]
  simp

/-- The finite-family adjacent merge at the unique position of a two-factor family is the
head merge with no remaining factors. -/
theorem adjacentMergeDataOfFn_one_tensorMap
    (M : Fin 2 → ModuleCat.{0} ℤ) (P : ModuleCat.{0} ℤ)
    (f : Quiver.Hom (M 0 ⊗ M 1) P) :
    (adjacentMergeDataOfFn M (0 : Fin 1) P f).tensorMap =
      (α_ (M 0) (M 1) (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
        (ρ_ (M 0 ⊗ M 1)).hom ≫ f ≫ (ρ_ P).inv := by
  change (@AdjacentMergeData.head (M 0) (M 1) P [] f).tensorMap = _
  exact adjacentMergeData_head_empty_tensorMap f

theorem recursiveAdjacentMergeDataOfFn_one_tensorMap
    (M : Fin 2 → ModuleCat.{0} ℤ) (P : ModuleCat.{0} ℤ)
    (f : Quiver.Hom (M 0 ⊗ M 1) P) :
    (recursiveAdjacentMergeDataOfFn M (0 : Fin 1) P f).tensorMap =
      (α_ (M 0) (M 1) (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
        (ρ_ (M 0 ⊗ M 1)).hom ≫ f ≫ (ρ_ P).inv := by
  change (@AdjacentMergeData.head (M 0) (M 1) P [] f).tensorMap = _
  exact adjacentMergeData_head_empty_tensorMap f

/-- A pointwise tensor map on a singleton family is conjugated by the right unitors. -/
theorem tensorMapData_ofFn_one_tensorMap
    (M N : Fin 1 → ModuleCat.{0} ℤ)
    (f : (j : Fin 1) → Quiver.Hom (M j) (N j)) :
    (TensorMapData.ofFn M N f).tensorMap =
      (ρ_ (M 0)).hom ≫ f 0 ≫ (ρ_ (N 0)).inv := by
  change f 0 ▷ 𝟙_ (ModuleCat.{0} ℤ) =
    (ρ_ (M 0)).hom ≫ f 0 ≫ (ρ_ (N 0)).inv
  rw [← cancel_mono (ρ_ (N 0)).hom]
  slice_rhs 3 4 => rw [Iso.inv_hom_id]
  simp only [Category.comp_id]
  exact MonoidalCategory.rightUnitor_naturality (f 0)

def singletonCompositionFactorMap
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    Quiver.Hom (factorModule d 0 ⊗ factorModule d 1)
      ((dgHomZModuleCochainComplex X Y).X
        (d.arrowDegree 0 + d.arrowDegree 1)) := by
  have hs₀ : (singleton X Y A).arrowSource 0 = X := rfl
  have ht₀ : (singleton X Y A).arrowTarget 0 = A.obj := rfl
  have hs₁ : (singleton X Y A).arrowSource 1 = A.obj := rfl
  have ht₁ : (singleton X Y A).arrowTarget 1 = Y :=
    vertex_last (singleton X Y A)
  simp only [factorModule]
  rw [hs₀, ht₀, hs₁, ht₁]
  exact dgCochainCompTensor X A.obj Y rfl

def singletonCompositionFactorMapAt
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      ((dgHomZModuleCochainComplex
        ((singleton X Y A).arrowSource i.castSucc)
        ((singleton X Y A).arrowTarget i.succ)).X
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) :=
  adjacentFactorComposition d i

theorem contractFactorComposition_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractFactorComposition d i =
      singletonCompositionFactorMapAt X Y A d i ≫
        (contractFactorModuleAtIso d i).inv := rfl

theorem singletonCompositionFactorMapAt_heq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    HEq (singletonCompositionFactorMapAt X Y A d i)
      (singletonCompositionFactorMap X Y A d) := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  unfold singletonCompositionFactorMapAt singletonCompositionFactorMap
  rfl

/-- The all-word contraction map on a one-letter word has the semantic adjacent-composition
normal form after identifying its target with the adjacent homogeneous Hom module. -/
theorem contractionTensorMap_singleton_normalized
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractionTensorMap d i ≫
        (singletonContractedSummandIsoAdjacentTarget X Y A d i).hom =
      (singletonSummandIsoTensorAt X Y A d i).hom ≫
        adjacentFactorComposition d i := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  unfold contractionTensorMap contractionTensorMapAtOldIndex
  unfold recursiveContractionTensorMapAtOldIndex
    recursiveContractionAdjacentMergeData
  rw [recursiveAdjacentMergeDataOfFn_one_tensorMap]
  unfold recursiveContractionMergedFactorsTensorMap
  rw [tensorMapData_ofFn_one_tensorMap]
  rw [recursiveContractionMergedFactorMap_singleton]
  unfold contractedFactorsOldIndexIso
  unfold contractedFactorAtOldIndex
  unfold contractionMergeAtOldIndex
    contractFactorAtOldIndexIso singletonContractedSummandIsoAdjacentTarget
    singletonSummandIsoTensorAt uneraseFactorIndex erasePosition
  simp only [singleton_length, Fin.isValue, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, eraseIntermediate_singleton, Fin.eta,
    recursiveMergedFactor, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Fin.zero_eta, Fin.cast_eq_self, eq_mpr_eq_cast, cast_eq, Category.assoc,
    Iso.inv_hom_id_assoc, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, Iso.trans_hom, eqToIso.hom,
    Fin.castSucc_succ, Nat.reduceAdd, Fin.cases_zero]
  slice_lhs 4 6 =>
    exact (contractFactorModuleAtIso d 0).inv_hom_id
  exact Category.comp_id
    ((singletonSummandIsoTensor X Y A d).hom ≫
      adjacentFactorComposition d 0)

/-- One signed contraction term, included into the degree-`n+1` quotient carrier. -/
def contractionLargeMap {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin w.length) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  d.contractionSign i •
    ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
      Limits.Sigma.ι
        (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
        ⟨eraseIntermediate w i, d.contract i⟩)

/-- Sum of all signed contraction terms leaving one homogeneous word summand. -/
def contractionDifferentialFromSummand {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  ∑ i, contractionLargeMap d i

/-- The contraction part of the Drinfeld differential on the whole coproduct carrier. -/
def quotientContractionDifferential (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y (n + 1)) :=
  Limits.Sigma.desc fun s : GradedSummandIndex X Y n ↦
    contractionDifferentialFromSummand s.2

@[reassoc (attr := simp)]
theorem quotientContractionDifferential_inclusion
    (X Y : ComplexCategory) (n : ℤ) (s : GradedSummandIndex X Y n) :
    Limits.Sigma.ι (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        quotientContractionDifferential X Y n =
      contractionDifferentialFromSummand s.2 :=
  Limits.Sigma.ι_desc _ s

@[simp]
theorem contractionDifferentialFromSummand_nil
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    contractionDifferentialFromSummand d = 0 := by
  change (∑ i : Fin 0, contractionLargeMap d i) = 0
  exact Finset.sum_empty

/-- The full candidate Drinfeld differential is the sum of the internal-Hom and contraction
parts. -/
def quotientTotalDifferential (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y (n + 1)) :=
  quotientInternalDifferential X Y n + quotientContractionDifferential X Y n

@[reassoc (attr := simp)]
theorem quotientTotalDifferential_inclusion
    (X Y : ComplexCategory) (n : ℤ) (s : GradedSummandIndex X Y n) :
    Limits.Sigma.ι (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        quotientTotalDifferential X Y n =
      internalDifferentialFromSummand s.2 + contractionDifferentialFromSummand s.2 := by
  rw [quotientTotalDifferential, Preadditive.comp_add,
    quotientInternalDifferential_inclusion X Y n s,
    quotientContractionDifferential_inclusion X Y n s]

@[reassoc]
theorem quotientTotalDifferential_nil_inclusion
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) ⟨nil X Y, d⟩ ≫
        quotientTotalDifferential X Y n = internalDifferentialFromSummand d := by
  rw [quotientTotalDifferential_inclusion]
  simp

theorem contractionDifferentialFromSummand_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractionDifferentialFromSummand d = contractionLargeMap d i := by
  unfold contractionDifferentialFromSummand
  apply Fintype.sum_eq_single i
  intro j hji
  exfalso
  apply hji
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  change i.val < 1 at hi
  change j.val < 1 at hj
  omega

@[reassoc]
theorem quotientTotalDifferential_singleton_inclusion
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t)
          ⟨singleton X Y A, d⟩ ≫
        quotientTotalDifferential X Y n =
      internalDifferentialFromSummand d + contractionLargeMap d i := by
  rw [quotientTotalDifferential_inclusion,
    contractionDifferentialFromSummand_singleton X Y A d i]

/-- Algebraic four-term expansion of the square of the candidate total differential. -/
theorem quotientTotalDifferential_comp (X Y : ComplexCategory) (n : ℤ) :
    quotientTotalDifferential X Y n ≫ quotientTotalDifferential X Y (n + 1) =
      quotientInternalDifferential X Y n ≫ quotientInternalDifferential X Y (n + 1) +
        quotientInternalDifferential X Y n ≫
          quotientContractionDifferential X Y (n + 1) +
        quotientContractionDifferential X Y n ≫
          quotientInternalDifferential X Y (n + 1) +
        quotientContractionDifferential X Y n ≫
          quotientContractionDifferential X Y (n + 1) := by
  simp only [quotientTotalDifferential, Preadditive.add_comp, Preadditive.comp_add]
  abel

theorem largeModule_zsmul_comp
    {P Q R : ModuleCat.{1} ℤ} (n : ℤ) (f : Quiver.Hom P Q) (g : Quiver.Hom Q R) :
    (n • f) ≫ g = n • (f ≫ g) :=
  (Preadditive.rightComp P g).map_zsmul n f

@[reassoc]
theorem contractionLargeMap_comp_internalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionLargeMap d i ≫ quotientInternalDifferential X Y (n + 1) =
      d.contractionSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
          internalDifferentialFromSummand (d.contract i)) := by
  unfold contractionLargeMap
  rw [largeModule_zsmul_comp, Category.assoc,
    quotientInternalDifferential_inclusion X Y (n + 1) ⟨eraseIntermediate w i, d.contract i⟩]

@[reassoc]
theorem contractionLargeMap_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionLargeMap d i ≫ quotientContractionDifferential X Y (n + 1) =
      d.contractionSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
          contractionDifferentialFromSummand (d.contract i)) := by
  unfold contractionLargeMap
  rw [largeModule_zsmul_comp, Category.assoc,
    quotientContractionDifferential_inclusion X Y (n + 1) ⟨eraseIntermediate w i, d.contract i⟩]

@[reassoc]
theorem internalDifferentialLargeMap_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) :
    internalDifferentialLargeMap d j ≫
        quotientContractionDifferential X Y (n + 1) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d j) ≫
        contractionDifferentialFromSummand (d.raise j) := by
  simp only [internalDifferentialLargeMap, Category.assoc]
  rw [quotientContractionDifferential_inclusion X Y (n + 1) ⟨w, d.raise j⟩]

theorem paritySign_add_one (m : ℤ) :
    (if Even (m + 1) then (1 : ℤ) else -1) =
      -(if Even m then (1 : ℤ) else -1) := by
  by_cases h : Even m <;> simp [h]

theorem paritySign_eq_negOnePow (m : ℤ) :
    (if Even m then (1 : ℤ) else -1) = (m.negOnePow : ℤ) := by
  by_cases h : Even m
  · rw [if_pos h, Int.negOnePow_even m h]
    rfl
  · have ho : Odd m := (Int.not_even_iff_odd).mp h
    rw [if_neg h, Int.negOnePow_odd m ho]
    rfl

theorem negOnePow_coe_mul_self (m : ℤ) :
    (m.negOnePow : ℤ) * m.negOnePow = 1 := by
  change ((m.negOnePow * m.negOnePow : ℤˣ) : ℤ) = 1
  rw [Int.units_mul_self]
  rfl

theorem DegreeProfile.internalSign_eq_negOnePow
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) :
    d.internalSign i = (d.suffixTotal i).negOnePow := by
  rw [DegreeProfile.internalSign, paritySign_eq_negOnePow]

theorem DegreeProfile.contractionSign_eq_negOnePow
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSign i = (d.contractionSuffix i).negOnePow := by
  rw [DegreeProfile.contractionSign, paritySign_eq_negOnePow]

theorem DegreeProfile.suffixTotal_castSucc_add_one
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.suffixTotal i.castSucc + 1 = d.contractionSuffix i := by
  unfold DegreeProfile.suffixTotal DegreeProfile.contractionSuffix
  simp only [Fin.lt_def, Fin.val_castSucc]
  omega

theorem DegreeProfile.contractionSuffix_eq_suffixTotal_succ_add
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSuffix i = d.suffixTotal i.succ + d.arrowDegree i.succ := by
  have hfilter :
      Finset.univ.filter
          (fun j : Fin (w.length + 1) ↦ i.val < j.val) =
        insert i.succ
          (Finset.univ.filter
            (fun j : Fin (w.length + 1) ↦ i.succ < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j = i.succ
      · exact Or.inl hj
      · right
        change i.val + 1 < j.val
        have hne : j.val ≠ i.val + 1 := by
          intro hval
          apply hj
          apply Fin.ext
          simpa using hval
        omega
    · rintro (rfl | h)
      · simp
      · change i.val + 1 < j.val at h
        omega
  unfold DegreeProfile.contractionSuffix DegreeProfile.suffixTotal
  rw [hfilter, Finset.sum_insert]
  · simp only [Fin.val_succ]
    omega
  · simp

theorem DegreeProfile.internalSign_castSucc_eq_neg_contractionSign
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.internalSign i.castSucc = -d.contractionSign i := by
  rw [d.internalSign_eq_negOnePow, d.contractionSign_eq_negOnePow,
    ← d.suffixTotal_castSucc_add_one i, Int.negOnePow_succ]
  simp

theorem DegreeProfile.contractionSign_mul_internalSign_succ
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSign i * d.internalSign i.succ =
      (d.arrowDegree i.succ).negOnePow := by
  rw [d.contractionSign_eq_negOnePow, d.internalSign_eq_negOnePow,
    d.contractionSuffix_eq_suffixTotal_succ_add i,
    Int.negOnePow_add]
  change ((d.suffixTotal i.succ).negOnePow : ℤ) *
      (d.arrowDegree i.succ).negOnePow *
      (d.suffixTotal i.succ).negOnePow = _
  have hs : ((d.suffixTotal i.succ).negOnePow : ℤ) *
      (d.suffixTotal i.succ).negOnePow = 1 := by
    exact negOnePow_coe_mul_self (d.suffixTotal i.succ)
  rw [mul_assoc, mul_left_comm, hs, mul_one]

theorem DegreeProfile.contractionSign_mul_self
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSign i * d.contractionSign i = 1 := by
  rw [d.contractionSign_eq_negOnePow]
  exact negOnePow_coe_mul_self (d.contractionSuffix i)

theorem DegreeProfile.suffixTotal_raise_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : j < i) :
    (d.raise i).suffixTotal j = d.suffixTotal j + 1 := by
  simp [DegreeProfile.suffixTotal, DegreeProfile.raise, Finset.sum_add_distrib, h]
  omega

theorem DegreeProfile.suffixTotal_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : i ≤ j) :
    (d.raise i).suffixTotal j = d.suffixTotal j := by
  simp [DegreeProfile.suffixTotal, DegreeProfile.raise, Finset.sum_add_distrib,
    not_lt_of_ge h]

theorem DegreeProfile.internalSign_raise_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : j < i) :
    (d.raise i).internalSign j = -d.internalSign j := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.suffixTotal_raise_of_lt i j h, paritySign_add_one]

theorem DegreeProfile.internalSign_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : i ≤ j) :
    (d.raise i).internalSign j = d.internalSign j := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.suffixTotal_raise_of_le i j h]

theorem DegreeProfile.contractionSuffix_raise_of_gt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) (i : Fin w.length)
    (h : i.val < j.val) :
    (d.raise j).contractionSuffix i = d.contractionSuffix i + 1 := by
  simp [DegreeProfile.contractionSuffix, DegreeProfile.raise, Finset.sum_add_distrib, h]
  omega

theorem DegreeProfile.contractionSuffix_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) (i : Fin w.length)
    (h : j.val ≤ i.val) :
    (d.raise j).contractionSuffix i = d.contractionSuffix i := by
  simp [DegreeProfile.contractionSuffix, DegreeProfile.raise, Finset.sum_add_distrib,
    not_lt_of_ge h]

theorem DegreeProfile.contractionSign_raise_of_gt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) (i : Fin w.length)
    (h : i.val < j.val) :
    (d.raise j).contractionSign i = -d.contractionSign i := by
  rw [DegreeProfile.contractionSign, DegreeProfile.contractionSign,
    d.contractionSuffix_raise_of_gt j i h, paritySign_add_one]

theorem DegreeProfile.contractionSign_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) (i : Fin w.length)
    (h : j.val ≤ i.val) :
    (d.raise j).contractionSign i = d.contractionSign i := by
  rw [DegreeProfile.contractionSign, DegreeProfile.contractionSign,
    d.contractionSuffix_raise_of_le j i h]

theorem DegreeProfile.contract_suffixTotal_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hqi : q < i) :
    (d.contract i).suffixTotal (uneraseFactorIndex w i q) =
      d.suffixTotal q.castSucc + 1 := by
  unfold DegreeProfile.suffixTotal
  rw [contract_suffix_sum_eq_oldIndex,
    sum_filter_contractedArrowDegree_gt_of_lt d.arrowDegree i q hqi]
  have hl := eraseIntermediate_length w i
  simp only [uneraseFactorIndex, Fin.val_castSucc]
  omega

theorem DegreeProfile.contract_suffixTotal_of_gt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hiq : i < q) :
    (d.contract i).suffixTotal (uneraseFactorIndex w i q) =
      d.suffixTotal q.succ := by
  unfold DegreeProfile.suffixTotal
  rw [contract_suffix_sum_eq_oldIndex,
    sum_filter_contractedArrowDegree_gt_of_le d.arrowDegree i q hiq.le]
  have hl := eraseIntermediate_length w i
  simp only [uneraseFactorIndex, Fin.val_succ]
  omega

theorem DegreeProfile.contract_suffixTotal_self
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (d.contract i).suffixTotal (erasePosition w i) =
      d.suffixTotal i.succ := by
  rw [← uneraseFactorIndex_self w i]
  unfold DegreeProfile.suffixTotal
  rw [contract_suffix_sum_eq_oldIndex,
    sum_filter_contractedArrowDegree_gt_of_le d.arrowDegree i i le_rfl]
  have hl := eraseIntermediate_length w i
  simp only [uneraseFactorIndex, Fin.val_succ]
  omega

theorem DegreeProfile.contract_contractionSuffix_of_before
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : j.castSucc < erasePosition w i) :
    (d.contract i).contractionSuffix j =
      d.contractionSuffix (eraseLift w i j) + 1 := by
  let q : Fin w.length :=
    Fin.cast (eraseIntermediate_length w i) j.castSucc
  have hq : q < i := by
    change j.val < i.val
    exact h
  have hsum :
      (∑ r ∈ Finset.univ.filter
          (fun r : Fin ((eraseIntermediate w i).length + 1) ↦ j.val < r.val),
        (d.contract i).arrowDegree r) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin w.length ↦ q < r),
          contractedArrowDegree d.arrowDegree i r := by
    have hfilter :
        Finset.univ.filter
            (fun r : Fin ((eraseIntermediate w i).length + 1) ↦ j.val < r.val) =
          Finset.univ.filter
            (fun r : Fin ((eraseIntermediate w i).length + 1) ↦
              uneraseFactorIndex w i q < r) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change j.val < r.val ↔ j.val < r.val
      rfl
    rw [hfilter]
    exact contract_suffix_sum_eq_oldIndex d i q
  have hl := eraseIntermediate_length w i
  have holdFilter :
      Finset.univ.filter
          (fun r : Fin (w.length + 1) ↦ q.castSucc < r) =
        Finset.univ.filter
          (fun r : Fin (w.length + 1) ↦ j.val < r.val) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change q.val < r.val ↔ j.val < r.val
    simp [q]
  unfold DegreeProfile.contractionSuffix
  rw [eraseLift_of_before w i j h]
  rw [hsum,
    sum_filter_contractedArrowDegree_gt_of_lt d.arrowDegree i q hq]
  rw [holdFilter]
  simp only [Fin.val_castSucc, Fin.val_cast]
  omega

theorem DegreeProfile.contract_contractionSuffix_of_after
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : erasePosition w i ≤ j.castSucc) :
    (d.contract i).contractionSuffix j =
      d.contractionSuffix (eraseLift w i j) := by
  let q : Fin w.length :=
    Fin.cast (eraseIntermediate_length w i) j.castSucc
  have hq : i ≤ q := by
    change i.val ≤ j.val
    exact h
  have hsum :
      (∑ r ∈ Finset.univ.filter
          (fun r : Fin ((eraseIntermediate w i).length + 1) ↦ j.val < r.val),
        (d.contract i).arrowDegree r) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin w.length ↦ q < r),
          contractedArrowDegree d.arrowDegree i r := by
    have hfilter :
        Finset.univ.filter
            (fun r : Fin ((eraseIntermediate w i).length + 1) ↦ j.val < r.val) =
          Finset.univ.filter
            (fun r : Fin ((eraseIntermediate w i).length + 1) ↦
              uneraseFactorIndex w i q < r) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change j.val < r.val ↔ j.val < r.val
      rfl
    rw [hfilter]
    exact contract_suffix_sum_eq_oldIndex d i q
  have hl := eraseIntermediate_length w i
  have holdFilter :
      Finset.univ.filter
          (fun r : Fin (w.length + 1) ↦ q.succ < r) =
        Finset.univ.filter
          (fun r : Fin (w.length + 1) ↦ j.val + 1 < r.val) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change q.val + 1 < r.val ↔ j.val + 1 < r.val
    simp [q]
  unfold DegreeProfile.contractionSuffix
  rw [eraseLift_of_after w i j h]
  rw [hsum,
    sum_filter_contractedArrowDegree_gt_of_le d.arrowDegree i q hq]
  rw [holdFilter]
  simp only [Fin.val_succ, Fin.val_cast]
  omega

theorem DegreeProfile.contractionSign_contract_of_before
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : j.castSucc < erasePosition w i) :
    (d.contract i).contractionSign j =
      -d.contractionSign (eraseLift w i j) := by
  rw [DegreeProfile.contractionSign, DegreeProfile.contractionSign,
    d.contract_contractionSuffix_of_before i j h, paritySign_add_one]

theorem DegreeProfile.contractionSign_contract_of_after
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length)
    (j : Fin (eraseIntermediate w i).length)
    (h : erasePosition w i ≤ j.castSucc) :
    (d.contract i).contractionSign j =
      d.contractionSign (eraseLift w i j) := by
  rw [DegreeProfile.contractionSign, DegreeProfile.contractionSign,
    d.contract_contractionSuffix_of_after i j h]

theorem DegreeProfile.internalSign_contract_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hqi : q < i) :
    (d.contract i).internalSign (uneraseFactorIndex w i q) =
      -d.internalSign q.castSucc := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.contract_suffixTotal_of_lt i q hqi, paritySign_add_one]

theorem DegreeProfile.internalSign_contract_of_gt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hiq : i < q) :
    (d.contract i).internalSign (uneraseFactorIndex w i q) =
      d.internalSign q.succ := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.contract_suffixTotal_of_gt i q hiq]

theorem DegreeProfile.internalSign_contract_self
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    (d.contract i).internalSign (erasePosition w i) =
      d.internalSign i.succ := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.contract_suffixTotal_self i]

theorem DegreeProfile.mixedCoefficient_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hqi : q < i) :
    d.internalSign q.castSucc * (d.raise q.castSucc).contractionSign i =
      -(d.contractionSign i *
        (d.contract i).internalSign (uneraseFactorIndex w i q)) := by
  rw [d.contractionSign_raise_of_le q.castSucc i hqi.le,
    d.internalSign_contract_of_lt i q hqi]
  ring

theorem DegreeProfile.mixedCoefficient_of_gt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i q : Fin w.length) (hiq : i < q) :
    d.internalSign q.succ * (d.raise q.succ).contractionSign i =
      -(d.contractionSign i *
        (d.contract i).internalSign (uneraseFactorIndex w i q)) := by
  have hgt : i.val < q.succ.val := by
    change i.val < q.val + 1
    omega
  rw [d.contractionSign_raise_of_gt q.succ i hgt,
    d.internalSign_contract_of_gt i q hiq]
  ring

theorem DegreeProfile.mixedCoefficient_right
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.internalSign i.succ * (d.raise i.succ).contractionSign i =
      -(d.contractionSign i *
        (d.contract i).internalSign (erasePosition w i)) := by
  have hgt : i.val < i.succ.val := by simp
  rw [d.contractionSign_raise_of_gt i.succ i hgt,
    d.internalSign_contract_self i]
  ring

theorem DegreeProfile.mixedCoefficient_left
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.internalSign i.castSucc * (d.raise i.castSucc).contractionSign i =
      -(d.contractionSign i *
        (d.contract i).internalSign (erasePosition w i) *
          (d.arrowDegree i.succ).negOnePow) := by
  rw [d.contractionSign_raise_of_le i.castSucc i le_rfl,
    d.internalSign_contract_self i,
    d.internalSign_castSucc_eq_neg_contractionSign i,
    d.contractionSign_mul_internalSign_succ i]
  have hc := d.contractionSign_mul_self i
  have hr := negOnePow_coe_mul_self (d.arrowDegree i.succ)
  ring_nf at hc hr ⊢
  rw [hc, hr]

def contractionSuffixFor {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) : ℤ :=
  (∑ j ∈ Finset.univ.filter
      (fun j : Fin (k + 1) ↦ i.val < j.val), a j) -
    (k - (i.val + 1))

def contractionSignFor {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) : ℤ :=
  if Even (contractionSuffixFor a i) then 1 else -1

theorem DegreeProfile.contractionSuffix_eq_contractionSuffixFor
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSuffix i = contractionSuffixFor d.arrowDegree i := rfl

theorem DegreeProfile.contractionSign_eq_contractionSignFor
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    d.contractionSign i = contractionSignFor d.arrowDegree i := rfl

theorem contractionSuffixFor_contract_of_lt {k : ℕ}
    (a : Fin (k + 2) → ℤ) (i : Fin (k + 1)) (j : Fin k)
    (h : j.castSucc < i) :
    contractionSuffixFor (contractedArrowDegree a i) j =
      contractionSuffixFor a (i.succAbove j) + 1 := by
  have hsum := sum_filter_contractedArrowDegree_gt_of_lt a i j.castSucc h
  change (∑ r ∈ Finset.univ.filter
        (fun r : Fin (k + 1) ↦ j.val < r.val), contractedArrowDegree a i r) =
      ∑ r ∈ Finset.univ.filter
        (fun r : Fin (k + 2) ↦ j.castSucc.val < r.val), a r at hsum
  have hsame :
      (∑ r ∈ Finset.univ.filter
          (fun r : Fin (k + 2) ↦ j.castSucc.val < r.val), a r) =
        ∑ r ∈ Finset.univ.filter
          (fun r : Fin (k + 2) ↦ j.val < r.val), a r := by
    congr 1
  rw [Fin.succAbove_of_castSucc_lt i j h]
  unfold contractionSuffixFor
  rw [hsum]
  rw [hsame]
  simp only [Fin.val_castSucc]
  omega

theorem contractionSuffixFor_contract_of_le {k : ℕ}
    (a : Fin (k + 2) → ℤ) (i : Fin (k + 1)) (j : Fin k)
    (h : i ≤ j.castSucc) :
    contractionSuffixFor (contractedArrowDegree a i) j =
      contractionSuffixFor a (i.succAbove j) := by
  have hsum := sum_filter_contractedArrowDegree_gt_of_le a i j.castSucc h
  change (∑ r ∈ Finset.univ.filter
        (fun r : Fin (k + 1) ↦ j.val < r.val), contractedArrowDegree a i r) =
      ∑ r ∈ Finset.univ.filter
        (fun r : Fin (k + 2) ↦ j.succ.val < r.val), a r at hsum
  have hsame :
      (∑ r ∈ Finset.univ.filter
          (fun r : Fin (k + 2) ↦ j.succ.val < r.val), a r) =
        ∑ r ∈ Finset.univ.filter
          (fun r : Fin (k + 2) ↦ j.val + 1 < r.val), a r := by
    congr 1
  rw [Fin.succAbove_of_le_castSucc i j h]
  unfold contractionSuffixFor
  rw [hsum]
  rw [hsame]
  simp only [Fin.val_succ]
  omega

theorem contractionSignFor_contract_of_lt {k : ℕ}
    (a : Fin (k + 2) → ℤ) (i : Fin (k + 1)) (j : Fin k)
    (h : j.castSucc < i) :
    contractionSignFor (contractedArrowDegree a i) j =
      -contractionSignFor a (i.succAbove j) := by
  rw [contractionSignFor, contractionSignFor,
    contractionSuffixFor_contract_of_lt a i j h, paritySign_add_one]

theorem contractionSignFor_contract_of_le {k : ℕ}
    (a : Fin (k + 2) → ℤ) (i : Fin (k + 1)) (j : Fin k)
    (h : i ≤ j.castSucc) :
    contractionSignFor (contractedArrowDegree a i) j =
      contractionSignFor a (i.succAbove j) := by
  rw [contractionSignFor, contractionSignFor,
    contractionSuffixFor_contract_of_le a i j h]

/-- Ordered pairs of distinct contraction positions, represented by the first removed
position and the position of the second removal in the shortened word. -/
abbrev ContractionPairIndex (n : ℕ) := Fin (n + 1) × Fin n

/-- Exchange the order of two contractions. -/
def contractionPairSwap {n : ℕ} (p : ContractionPairIndex n) :
    ContractionPairIndex n :=
  ⟨p.1.succAbove p.2, p.2.predAbove p.1⟩

@[simp]
theorem contractionPairSwap_fst {n : ℕ} (p : ContractionPairIndex n) :
    (contractionPairSwap p).1 = p.1.succAbove p.2 := rfl

@[simp]
theorem contractionPairSwap_snd {n : ℕ} (p : ContractionPairIndex n) :
    (contractionPairSwap p).2 = p.2.predAbove p.1 := rfl

theorem contractionPairSwap_ne {n : ℕ} (p : ContractionPairIndex n) :
    contractionPairSwap p ≠ p := by
  intro h
  exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h)

@[simp]
theorem contractionPairSwap_involutive {n : ℕ} (p : ContractionPairIndex n) :
    contractionPairSwap (contractionPairSwap p) = p := by
  apply Prod.ext
  · exact Fin.succAbove_succAbove_predAbove p.1 p.2
  · exact Fin.predAbove_predAbove_succAbove p.1 p.2

def contractionPairCoefficientFor {n : ℕ} (a : Fin (n + 2) → ℤ)
    (p : ContractionPairIndex n) : ℤ :=
  contractionSignFor a p.1 *
    contractionSignFor (contractedArrowDegree a p.1) p.2

theorem contractionPairCoefficientFor_swap {n : ℕ}
    (a : Fin (n + 2) → ℤ) (p : ContractionPairIndex n) :
    contractionPairCoefficientFor a (contractionPairSwap p) =
      -contractionPairCoefficientFor a p := by
  rcases p with ⟨i, j⟩
  by_cases h : j.castSucc < i
  · have hle : i.succAbove j ≤ (j.predAbove i).castSucc := by
      rw [Fin.succAbove_of_castSucc_lt i j h,
        Fin.predAbove_of_castSucc_lt j i h]
      exact (Fin.le_castSucc_pred_iff _).2 h
    unfold contractionPairCoefficientFor contractionPairSwap
    rw [contractionSignFor_contract_of_lt a i j h,
      contractionSignFor_contract_of_le a (i.succAbove j) (j.predAbove i) hle,
      Fin.succAbove_succAbove_predAbove]
    ring
  · have hle : i ≤ j.castSucc := Fin.not_lt.mp h
    have hlt : (j.predAbove i).castSucc < i.succAbove j := by
      rw [Fin.succAbove_of_le_castSucc i j hle,
        Fin.predAbove_of_le_castSucc j i hle]
      rw [Fin.castSucc_castPred]
      exact lt_of_le_of_lt hle Fin.castSucc_lt_succ
    unfold contractionPairCoefficientFor contractionPairSwap
    rw [contractionSignFor_contract_of_le a i j hle,
      contractionSignFor_contract_of_lt a (i.succAbove j) (j.predAbove i) hlt,
      Fin.succAbove_succAbove_predAbove]
    ring

/-- Any coefficient family negated by exchanging the two contraction orders has zero total
sum. -/
theorem sum_contractionPairIndex_eq_zero_of_swap_neg
    {n : ℕ} (f : ContractionPairIndex n → ℤ)
    (hneg : ∀ p, f (contractionPairSwap p) = -f p) :
    ∑ p, f p = 0 := by
  classical
  apply Finset.sum_ninvolution contractionPairSwap
  · intro p
    rw [hneg]
    omega
  · intro p _
    exact contractionPairSwap_ne p
  · intro p
    simp
  · intro p
    exact contractionPairSwap_involutive p

theorem sum_contractionPairCoefficientFor_eq_zero {n : ℕ}
    (a : Fin (n + 2) → ℤ) :
    ∑ p : ContractionPairIndex n, contractionPairCoefficientFor a p = 0 := by
  exact sum_contractionPairIndex_eq_zero_of_swap_neg
    (contractionPairCoefficientFor a) (contractionPairCoefficientFor_swap a)

/-- Map-valued version of contraction-pair cancellation: the structural maps are invariant
under exchanging the contraction order, while their integer coefficients change sign. -/
theorem sum_contractionPairIndex_smul_eq_zero_of_swap
    {n : ℕ} {P Q : ModuleCat.{1} ℤ}
    (c : ContractionPairIndex n → ℤ)
    (f : ContractionPairIndex n → Quiver.Hom P Q)
    (hc : ∀ p, c (contractionPairSwap p) = -c p)
    (hf : ∀ p, f (contractionPairSwap p) = f p) :
    ∑ p, c p • f p = 0 := by
  classical
  apply Finset.sum_ninvolution contractionPairSwap
  · intro p
    rw [hc, hf]
    simp
  · intro p _
    exact contractionPairSwap_ne p
  · intro p
    simp
  · intro p
    exact contractionPairSwap_involutive p




end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
