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

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
