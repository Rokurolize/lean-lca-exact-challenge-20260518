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

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
