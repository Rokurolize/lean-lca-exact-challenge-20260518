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
          change Fin (k + 1) at i
          change Fin (k + 2) at j
          refine Fin.cases ?_ (fun j ↦ ?_) j
          · rfl
          · refine Fin.lastCases ?_ (fun q ↦ ?_) j
            · have hidx : i.succ.castSucc.succAbove
                    (Fin.cast (congrArg (fun n ↦ n + 1)
                      (eraseIntermediate_length
                        ({ length := k + 1, intermediate := intermediate } :
                          DrinfeldWord X Y) i)) (Fin.last k).succ) =
              Fin.last (k + 2) := by
                convert eraseVertexSuccAbove_last k i <;> apply Fin.ext <;> rfl
              rw [hidx]
              rw [show (Fin.last k).succ = Fin.last (k + 1) by
                apply Fin.ext; rfl]
              exact (vertex_last (eraseIntermediate
                  ({ length := k + 1, intermediate := intermediate } :
                    DrinfeldWord X Y) i)).trans (vertex_last _).symm
            · have hidx : i.succ.castSucc.succAbove
                    (Fin.cast (congrArg (fun n ↦ n + 1)
                      (eraseIntermediate_length
                        ({ length := k + 1, intermediate := intermediate } :
                          DrinfeldWord X Y) i)) q.castSucc.succ) =
                  (i.succAbove q).succ.castSucc := by
                convert eraseVertexSuccAbove_internal k i q <;> apply Fin.ext <;> rfl
              rw [hidx]
              simp [vertex, eraseIntermediate]
              unfold object
              rfl

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
      (factorModule (d.contract i) (erasePosition w i)) := by
  let f : Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) := by
    simp only [factorModule]
    rw [arrowTarget_castSucc_eq_arrowSource_succ]
    exact dgCochainCompTensor
      (w.arrowSource i.castSucc) (w.arrowSource i.succ) (w.arrowTarget i.succ) rfl
  exact f ≫ (contractFactorModuleAtIso d i).inv

/-- The factor list obtained by replacing the two entries adjacent to `i` by `P`. -/
def mergedFactor {k : ℕ} (M : Fin (k + 1) → ModuleCat.{0} ℤ)
    (i : Fin k) (P : ModuleCat.{0} ℤ) (j : Fin k) : ModuleCat.{0} ℤ :=
  if j < i then M j.castSucc else if j = i then P else M j.succ

/-- `AdjacentMergeData` for an arbitrary finite family, with the merge at a specified
finite position. -/
def adjacentMergeDataOfFn : {k : ℕ} → (M : Fin (k + 1) → ModuleCat.{0} ℤ) →
    (i : Fin k) → (P : ModuleCat.{0} ℤ) →
    Quiver.Hom (M i.castSucc ⊗ M i.succ) P →
    AdjacentMergeData (List.ofFn M) (List.ofFn (mergedFactor M i P))
  | 0, _, i, _, _ => Fin.elim0 i
  | k + 1, M, i, P, f => by
      cases i using Fin.cases with
      | zero =>
          simpa [List.ofFn_succ, mergedFactor] using
            (AdjacentMergeData.head
              (Ms := List.ofFn (fun q : Fin k ↦ M q.succ.succ)) f)
      | succ q =>
          let tailM : Fin (k + 1) → ModuleCat.{0} ℤ := fun j ↦ M j.succ
          have ftail : Quiver.Hom (tailM q.castSucc ⊗ tailM q.succ) P := by
            simpa [tailM] using f
          have tail := adjacentMergeDataOfFn tailM q P ftail
          have hmerged : List.ofFn (mergedFactor M q.succ P) =
              M 0 :: List.ofFn (mergedFactor tailM q P) := by
            rw [List.ofFn_succ]
            congr 1
            apply congrArg List.ofFn
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
          simpa only [List.ofFn_succ, tailM] using AdjacentMergeData.tail tail

/-- Regard an old intermediate-object position as a factor position of the erased word. -/
def uneraseFactorIndex {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i j : Fin w.length) : Fin ((eraseIntermediate w i).length + 1) :=
  Fin.cast (eraseIntermediate_length w i).symm j

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

/-- Contracted factor family, indexed by the original intermediate positions. -/
def contractedFactorAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin w.length) : ModuleCat.{0} ℤ :=
  factorModule (d.contract i) (uneraseFactorIndex w i j)

/-- The canonical adjacent merge of the old factor family.  Its target is the contracted
family indexed through the old finite ordinal, with the non-merged entries still represented
by their canonically identical old modules. -/
def contractionAdjacentMergeData
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    AdjacentMergeData (List.ofFn (factorModule d))
      (List.ofFn (mergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))) := by
  apply adjacentMergeDataOfFn (factorModule d) i (contractedFactorAtOldIndex d i i)
  simpa only [contractedFactorAtOldIndex, uneraseFactorIndex_self] using
    contractFactorComposition d i

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
        (List.ofFn (mergedFactor (factorModule d) i (contractedFactorAtOldIndex d i i))))
      (tensorModuleList (List.ofFn (contractedFactorAtOldIndex d i))) :=
  (TensorMapData.ofFn _ _ (contractionMergedFactorMap d i)).tensorMap

/-- The canonical contraction tensor map for an arbitrary word and degree profile, with the
contracted factors indexed by the old finite ordinal. -/
def contractionTensorMapAtOldIndex
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d)
      (tensorModuleList (List.ofFn (contractedFactorAtOldIndex d i))) :=
  (contractionAdjacentMergeData d i).tensorMap ≫
    contractionMergedFactorsTensorMap d i

theorem contractedFactorsOldIndex_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    List.ofFn (contractedFactorAtOldIndex d i) =
      List.ofFn (factorModule (d.contract i)) := by
  cases w with
  | mk k intermediate =>
      cases k with
      | zero => exact Fin.elim0 i
      | succ k => rfl

/-- The general contraction map between the actual word summands. -/
def contractionTensorMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (summandModule d) (summandModule (d.contract i)) :=
  contractionTensorMapAtOldIndex d i ≫
    eqToHom (congrArg tensorModuleList (contractedFactorsOldIndex_eq d i))

theorem adjacentMergeData_head_empty_tensorMap
    {M N P : ModuleCat.{0} ℤ} (f : Quiver.Hom (M ⊗ N) P) :
    (@AdjacentMergeData.head M N P [] f).tensorMap =
      (α_ M N (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
        (ρ_ (M ⊗ N)).hom ≫ f ≫ (ρ_ P).inv := by
  dsimp only [AdjacentMergeData.tensorMap, tensorModuleList]
  simp

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
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) := by
  simp only [factorModule]
  rw [arrowTarget_castSucc_eq_arrowSource_succ]
  exact dgCochainCompTensor
    ((singleton X Y A).arrowSource i.castSucc)
    ((singleton X Y A).arrowSource i.succ)
    ((singleton X Y A).arrowTarget i.succ) rfl

theorem contractFactorComposition_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractFactorComposition d i =
      singletonCompositionFactorMapAt X Y A d i ≫
        (contractFactorModuleAtIso d i).inv := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  unfold contractFactorComposition singletonCompositionFactorMapAt
  rfl

theorem singletonCompositionFactorMapAt_heq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    HEq (singletonCompositionFactorMapAt X Y A d i)
      (singletonCompositionFactorMap X Y A d) := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  unfold singletonCompositionFactorMapAt singletonCompositionFactorMap
  rfl

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
  simp [quotientTotalDifferential, Preadditive.comp_add]

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
  simp [contractionLargeMap, Category.assoc, largeModule_zsmul_comp]

@[reassoc]
theorem contractionLargeMap_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionLargeMap d i ≫ quotientContractionDifferential X Y (n + 1) =
      d.contractionSign i •
        ((ModuleCat.uliftFunctor.{1} ℤ).map (contractionTensorMap d i) ≫
          contractionDifferentialFromSummand (d.contract i)) := by
  simp [contractionLargeMap, Category.assoc, largeModule_zsmul_comp]

@[reassoc]
theorem internalDifferentialLargeMap_comp_contractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (j : Fin (w.length + 1)) :
    internalDifferentialLargeMap d j ≫
        quotientContractionDifferential X Y (n + 1) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d j) ≫
        contractionDifferentialFromSummand (d.raise j) := by
  simp [internalDifferentialLargeMap, Category.assoc]

theorem paritySign_add_one (m : ℤ) :
    (if Even (m + 1) then (1 : ℤ) else -1) =
      -(if Even m then (1 : ℤ) else -1) := by
  by_cases h : Even m <;> simp [Int.even_add_one, h]

theorem DegreeProfile.prefixTotal_raise_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : i < j) :
    (d.raise i).prefixTotal j = d.prefixTotal j + 1 := by
  simp [DegreeProfile.prefixTotal, DegreeProfile.raise, Finset.sum_add_distrib, h]
  omega

theorem DegreeProfile.prefixTotal_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : j ≤ i) :
    (d.raise i).prefixTotal j = d.prefixTotal j := by
  simp [DegreeProfile.prefixTotal, DegreeProfile.raise, Finset.sum_add_distrib,
    not_lt_of_ge h]

theorem DegreeProfile.internalSign_raise_of_lt
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : i < j) :
    (d.raise i).internalSign j = -d.internalSign j := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.prefixTotal_raise_of_lt i j h, paritySign_add_one]

theorem DegreeProfile.internalSign_raise_of_le
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) (h : j ≤ i) :
    (d.raise i).internalSign j = d.internalSign j := by
  rw [DegreeProfile.internalSign, DegreeProfile.internalSign,
    d.prefixTotal_raise_of_le i j h]

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
    simp




end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
