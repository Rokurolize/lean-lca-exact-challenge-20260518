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

/-- The factor of the erased word, viewed as a position among the old intermediate
objects.  This is also the index of the first old arrow contributing to that factor. -/
def eraseFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) : Fin w.length :=
  Fin.cast (eraseIntermediate_length w i) j

def survivingOldFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) (j : Fin ((eraseIntermediate w i).length + 1)) :
    Fin (w.length + 1) :=
  i.castSucc.succAbove (eraseFactorIndex w i j)

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
  (contractionAdjacentMergeData d i).tensorMap ≫
    contractionMergedFactorsTensorMap d i

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
  unfold contractionAdjacentMergeData
  rw [adjacentMergeDataOfFn_one_tensorMap]
  unfold contractionMergedFactorsTensorMap
  rw [tensorMapData_ofFn_one_tensorMap]
  unfold contractedFactorsOldIndexIso
  unfold contractedFactorAtOldIndex
  unfold contractionMergeAtOldIndex contractionMergedFactorMap mergedFactor
    contractFactorAtOldIndexIso singletonContractedSummandIsoAdjacentTarget
    singletonSummandIsoTensorAt uneraseFactorIndex erasePosition
  simp only [singleton_length, Fin.isValue, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, eraseIntermediate_singleton, Fin.eta,
    not_lt_zero, ↓dreduceIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Fin.zero_eta, Fin.cast_eq_self, eq_mpr_eq_cast, cast_eq, Category.assoc,
    lt_self_iff_false, ↓reduceDIte, Iso.inv_hom_id_assoc, eqToIso_refl,
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
