import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Additive horn corrections

This file develops the explicit additive horn filler for the simplicial set underlying a
simplicial abelian group.  The two correction operations are the elementary steps in the
standard ascending/descending horn-filling algorithm.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open Simplicial

universe u

/-- The simplicial set underlying a simplicial abelian group. -/
abbrev additiveUnderlyingSSet (X : SimplicialObject (AddCommGrpCat.{u})) : SSet.{u} :=
  ((SimplicialObject.whiskering (AddCommGrpCat.{u}) (Type u)).obj
    (forget (AddCommGrpCat.{u}))).obj X

namespace AdditiveHorn

variable (X : SimplicialObject (AddCommGrpCat.{u}))

/-- An invariant preserved by each transition is preserved by an ordered left fold. -/
theorem foldl_invariant {α β : Type*} (P : β → Prop) (step : β → α → β)
    (l : List α) (init : β) (hinit : P init)
    (hstep : ∀ y a, P y → P (step y a)) : P (l.foldl step init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a l ih =>
      simp only [List.foldl_cons]
      exact ih _ (hstep init a hinit)

/-- Membership-aware fold invariance, used when preservation depends on the position of the
current correction index in an ordered suffix. -/
theorem foldl_invariant_mem {α β : Type*} (P : β → Prop) (step : β → α → β)
    (l : List α) (init : β) (hinit : P init)
    (hstep : ∀ y a, a ∈ l → P y → P (step y a)) : P (l.foldl step init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a l ih =>
      simp only [List.foldl_cons]
      apply ih _ (hstep init a (by simp) hinit)
      intro y b hb hy
      exact hstep y b (by simp [hb]) hy

/-- To prove a property after an ordered fold, it suffices to establish it at the transition
where its distinguished index is processed and preserve it along the remaining suffix. -/
theorem foldl_property_from_focus {α β : Type*} (P : β → Prop) (step : β → α → β)
    (pre post : List α) (focus : α) (init : β)
    (hfocus : ∀ y, P (step y focus))
    (hpost : ∀ y a, P y → P (step y a)) :
    P ((pre ++ focus :: post).foldl step init) := by
  rw [List.foldl_append, List.foldl_cons]
  apply foldl_invariant P step post _ (hfocus _)
  exact hpost

/-- Membership-aware focused fold principle. -/
theorem foldl_property_from_focus_mem {α β : Type*} (P : β → Prop)
    (step : β → α → β) (pre post : List α) (focus : α) (init : β)
    (hfocus : ∀ y, P (step y focus))
    (hpost : ∀ y a, a ∈ post → P y → P (step y a)) :
    P ((pre ++ focus :: post).foldl step init) := by
  rw [List.foldl_append, List.foldl_cons]
  exact foldl_invariant_mem P step post _ (hfocus _) hpost

/-- In a pairwise ordered list, the focused element precedes every member of its suffix. -/
theorem rel_focus_of_pairwise_append {α : Type*} {R : α → α → Prop}
    (pre post : List α) (focus a : α)
    (h : (pre ++ focus :: post).Pairwise R) (ha : a ∈ post) : R focus a := by
  rw [List.pairwise_append] at h
  exact (List.pairwise_cons.mp h.2.1).1 a ha

/-- Split a pairwise ordered list at a member, retaining its relation to the suffix. -/
theorem exists_focus_decomposition {α : Type*} {R : α → α → Prop}
    (l : List α) (focus : α) (hpair : l.Pairwise R) (hmem : focus ∈ l) :
    ∃ pre post, l = pre ++ focus :: post ∧ ∀ a ∈ post, R focus a := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hmem
  exact ⟨pre, post, rfl, fun a ha ↦
    rel_focus_of_pairwise_append pre post focus a hpair ha⟩

/-- Indices below the missing face, in the order required by upward correction. -/
def belowIndices {N : ℕ} (i : Fin N) : List (Fin N) :=
  (Finset.univ.filter (· < i)).sort (· ≤ ·)

/-- Indices above the missing face, in the order required by downward correction. -/
def aboveIndices {N : ℕ} (i : Fin N) : List (Fin N) :=
  ((Finset.univ.filter (i < ·)).sort (· ≤ ·)).reverse

@[simp]
theorem mem_belowIndices {N : ℕ} (i j : Fin N) : j ∈ belowIndices i ↔ j < i := by
  simp [belowIndices]

@[simp]
theorem mem_aboveIndices {N : ℕ} (i j : Fin N) : j ∈ aboveIndices i ↔ i < j := by
  simp [aboveIndices]

theorem belowIndices_sortedLT {N : ℕ} (i : Fin N) : (belowIndices i).SortedLT := by
  simpa [belowIndices] using
    Finset.sortedLT_sort (Finset.univ.filter (· < i))

theorem aboveIndices_sortedGT {N : ℕ} (i : Fin N) : (aboveIndices i).SortedGT := by
  simpa [aboveIndices] using
    (Finset.sortedLT_sort (Finset.univ.filter (i < ·))).reverse

/-- Every lower face has an ordered focus decomposition in the ascending index list. -/
theorem belowIndices_focus {N : ℕ} (i j : Fin N) (hji : j < i) :
    ∃ pre post, belowIndices i = pre ++ j :: post ∧ ∀ a ∈ post, j < a := by
  exact exists_focus_decomposition (belowIndices i) j (belowIndices_sortedLT i).pairwise
    ((mem_belowIndices i j).2 hji)

/-- Every upper face has an ordered focus decomposition in the descending index list. -/
theorem aboveIndices_focus {N : ℕ} (i j : Fin N) (hij : i < j) :
    ∃ pre post, aboveIndices i = pre ++ j :: post ∧ ∀ a ∈ post, a < j := by
  exact exists_focus_decomposition (aboveIndices i) j (aboveIndices_sortedGT i).pairwise
    ((mem_aboveIndices i j).2 hij)

/-- A face below the missing face has a degeneracy index of the required smaller size. -/
def belowDegeneracyIndex {n : ℕ} {i j : Fin (n + 2)} (hji : j < i) : Fin (n + 1) :=
  j.castPred (Fin.ne_last_of_lt hji)

/-- A face above the missing face has a predecessor degeneracy index. -/
def aboveDegeneracyIndex {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) : Fin (n + 1) :=
  j.pred (Fin.ne_zero_of_lt hij)

@[simp]
theorem belowDegeneracyIndex_castSucc {n : ℕ} {i j : Fin (n + 2)} (hji : j < i) :
    Fin.castSucc (belowDegeneracyIndex hji) = j := by
  exact Fin.castSucc_castPred j _

@[simp]
theorem aboveDegeneracyIndex_succ {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) :
    (aboveDegeneracyIndex hij).succ = j := by
  exact Fin.succ_pred j _

/-- Correct face `j` using degeneracy `j`. -/
def correctUp {n : ℕ} (j : Fin (n + 1))
    (target : X _⦋n⦌) (y : X _⦋n + 1⦌) : X _⦋n + 1⦌ :=
  y + X.σ j (target - X.δ (Fin.castSucc j) y)

/-- Correct face `j+1` using degeneracy `j`. -/
def correctDown {n : ℕ} (j : Fin (n + 1))
    (target : X _⦋n⦌) (y : X _⦋n + 1⦌) : X _⦋n + 1⦌ :=
  y + X.σ j (target - X.δ j.succ y)

/-- The degree-`n` element represented by a face of an additive horn. -/
def faceValue {n : ℕ} {i : Fin (n + 2)}
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X)
    (j : Fin (n + 2)) (hj : j ≠ i) : X _⦋n⦌ :=
  SSet.yonedaEquiv (f j hj)

theorem additiveUnderlyingSSet_δ_apply {n : ℕ} (i : Fin (n + 2))
    (x : X _⦋n + 1⦌) :
    (additiveUnderlyingSSet X).δ i x = X.δ i x := by
  rfl

def additiveUnderlyingSSetObjEquiv (n : ℕ) :
    additiveUnderlyingSSet X _⦋n⦌ ≃ X _⦋n⦌ :=
  Equiv.refl _

theorem yonedaEquiv_delta_comp {Q : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (σ : Δ[n + 1] ⟶ Q) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ σ) = Q.δ i (SSet.yonedaEquiv σ) := by
  change σ.app _ (Δ[n + 1].δ i (SSet.yonedaEquiv (𝟙 Δ[n + 1]))) =
    Q.δ i (σ.app _ (SSet.yonedaEquiv (𝟙 Δ[n + 1])))
  exact SSet.δ_naturality_apply σ i (SSet.yonedaEquiv (𝟙 Δ[n + 1]))

/-- Horn compatibility as an equality of faces of represented additive elements. -/
theorem faceValue_compat {n : ℕ} {i : Fin (n + 3)}
    (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i),
      Δ[n + 1] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (j k : Fin (n + 3))
    (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :
    X.δ (k.pred (Fin.ne_zero_of_lt hjk)) (faceValue X f j hj) =
      X.δ (j.castPred (Fin.ne_last_of_lt hjk)) (faceValue X f k hk) := by
  have h := congrArg SSet.yonedaEquiv (hf j k hj hk hjk)
  have h' := congrArg (additiveUnderlyingSSetObjEquiv X n)
    (by simpa only [faceValue, yonedaEquiv_delta_comp,
      additiveUnderlyingSSet_δ_apply] using h)
  exact h'

/-- One transition of the ascending correction fold. -/
def upTransition {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X)
    (y : X _⦋n + 1⦌) (j : Fin (n + 2)) : X _⦋n + 1⦌ :=
  if hji : j < i then
    correctUp X (belowDegeneracyIndex hji) (faceValue X f j (ne_of_lt hji)) y
  else y

/-- One transition of the descending correction fold. -/
def downTransition {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X)
    (y : X _⦋n + 1⦌) (j : Fin (n + 2)) : X _⦋n + 1⦌ :=
  if hij : i < j then
    correctDown X (aboveDegeneracyIndex hij) (faceValue X f j (ne_of_gt hij)) y
  else y

theorem upTransition_of_lt {n : ℕ} (i j : Fin (n + 2)) (hji : j < i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) (y : X _⦋n + 1⦌) :
    upTransition X i f y j =
      correctUp X (belowDegeneracyIndex hji) (faceValue X f j (ne_of_lt hji)) y := by
  simp only [upTransition, dif_pos hji]

theorem downTransition_of_lt {n : ℕ} (i j : Fin (n + 2)) (hij : i < j)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) (y : X _⦋n + 1⦌) :
    downTransition X i f y j =
      correctDown X (aboveDegeneracyIndex hij) (faceValue X f j (ne_of_gt hij)) y := by
  simp only [downTransition, dif_pos hij]

/-- The ascending half of the standard additive horn filler. -/
def upFold {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) : X _⦋n + 1⦌ :=
  (belowIndices i).foldl (upTransition X i f) 0

/-- The full two-pass additive correction state. -/
def hornFillValue {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) : X _⦋n + 1⦌ :=
  (aboveIndices i).foldl (downTransition X i f) (upFold X i f)

/-- The simplex map represented by the explicit two-pass additive correction state. -/
def hornFiller {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) :
    Δ[n + 1] ⟶ additiveUnderlyingSSet X :=
  SSet.yonedaEquiv.symm (hornFillValue X i f)

@[simp]
theorem yonedaEquiv_hornFiller {n : ℕ} (i : Fin (n + 2))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
      Δ[n] ⟶ additiveUnderlyingSSet X) :
    SSet.yonedaEquiv (hornFiller X i f) = hornFillValue X i f := by
  exact Equiv.apply_symm_apply _ _

/-- Equality of the relevant lower faces, supplied by horn compatibility and the current fold
invariant, makes the lower face of an error vanish. -/
theorem lower_error_eq_zero {m : ℕ} (k : Fin (m + 2))
    (target currentFace : X _⦋m + 1⦌)
    (h : X.δ k target = X.δ k currentFace) :
    X.δ k (target - currentFace) = 0 := by
  simp only [map_sub, h, sub_self]

/-- The analogous error-vanishing lemma used by the descending fold. -/
theorem higher_error_eq_zero {m : ℕ} (k : Fin (m + 2))
    (target currentFace : X _⦋m + 1⦌)
    (h : X.δ k target = X.δ k currentFace) :
    X.δ k (target - currentFace) = 0 :=
  lower_error_eq_zero X k target currentFace h

@[simp]
theorem face_correctUp_self {n : ℕ} (j : Fin (n + 1))
    (target : X _⦋n⦌) (y : X _⦋n + 1⦌) :
    X.δ (Fin.castSucc j) (correctUp X j target y) = target := by
  simp only [correctUp, map_add, map_sub]
  have h := congrArg (fun f : X _⦋n⦌ ⟶ X _⦋n⦌ ↦ f.hom)
    (X.δ_comp_σ_self (i := j))
  have ht : X.δ (Fin.castSucc j) (X.σ j target) = target := by
    exact DFunLike.congr_fun h target
  have hy : X.δ (Fin.castSucc j) (X.σ j (X.δ (Fin.castSucc j) y)) =
      X.δ (Fin.castSucc j) y := by
    exact DFunLike.congr_fun h (X.δ (Fin.castSucc j) y)
  rw [ht, hy]
  simp

@[simp]
theorem face_correctDown_self {n : ℕ} (j : Fin (n + 1))
    (target : X _⦋n⦌) (y : X _⦋n + 1⦌) :
    X.δ j.succ (correctDown X j target y) = target := by
  simp only [correctDown, map_add, map_sub]
  have h := congrArg (fun f : X _⦋n⦌ ⟶ X _⦋n⦌ ↦ f.hom)
    (X.δ_comp_σ_succ (i := j))
  have ht : X.δ j.succ (X.σ j target) = target := by
    exact DFunLike.congr_fun h target
  have hy : X.δ j.succ (X.σ j (X.δ j.succ y)) = X.δ j.succ y := by
    exact DFunLike.congr_fun h (X.δ j.succ y)
  rw [ht, hy]
  simp

/-- A face already known to annihilate the upward correction is preserved.  The ordered-fold
proof discharges the hypothesis using horn compatibility and `δ_comp_σ_of_le`. -/
theorem face_correctUp_eq_of_correction_eq_zero {n : ℕ} (j : Fin (n + 1))
    (k : Fin (n + 2)) (target : X _⦋n⦌) (y : X _⦋n + 1⦌)
    (hzero : X.δ k (X.σ j (target - X.δ (Fin.castSucc j) y)) = 0) :
    X.δ k (correctUp X j target y) = X.δ k y := by
  simp only [correctUp, map_add, hzero, add_zero]

/-- A face already known to annihilate the downward correction is preserved. -/
theorem face_correctDown_eq_of_correction_eq_zero {n : ℕ} (j : Fin (n + 1))
    (k : Fin (n + 2)) (target : X _⦋n⦌) (y : X _⦋n + 1⦌)
    (hzero : X.δ k (X.σ j (target - X.δ j.succ y)) = 0) :
    X.δ k (correctDown X j target y) = X.δ k y := by
  simp only [correctDown, map_add, hzero, add_zero]

/-- Adding a degenerate error at `q+1` preserves every lower face whose face of the error
vanishes.  Unlike the correction-specific wrappers, this lemma applies during the descending
pass as well and is what preserves faces established by the ascending pass. -/
theorem face_add_sigma_succ_eq_of_lower_error {m : ℕ} (q : Fin (m + 1))
    (k : Fin (m + 2)) (hkq : k ≤ Fin.castSucc q)
    (y : X _⦋m + 2⦌) (error : X _⦋m + 1⦌) (herr : X.δ k error = 0) :
    X.δ (Fin.castSucc k) (y + X.σ q.succ error) = X.δ (Fin.castSucc k) y := by
  simp only [map_add]
  have hid := X.δ_comp_σ_of_le hkq
  have happ := congrArg
    (fun f : X _⦋m + 1⦌ ⟶ X _⦋m + 1⦌ ↦ f.hom error) hid
  change X.δ (Fin.castSucc k) (X.σ q.succ error) = X.σ q (X.δ k error) at happ
  rw [happ, herr, map_zero, add_zero]

/-- An upward correction at `q+1` preserves a lower face once the corresponding lower face
of its error vanishes.  This is the ordered case of the simplicial identity
`d_k s_{q+1} = s_q d_k`. -/
theorem face_correctUp_succ_eq_of_lower_error {m : ℕ} (q : Fin (m + 1))
    (k : Fin (m + 2)) (hkq : k ≤ Fin.castSucc q)
    (target : X _⦋m + 1⦌) (y : X _⦋m + 2⦌)
    (herr : X.δ k (target - X.δ (Fin.castSucc q.succ) y) = 0) :
    X.δ (Fin.castSucc k) (correctUp X q.succ target y) =
      X.δ (Fin.castSucc k) y := by
  apply face_correctUp_eq_of_correction_eq_zero
  have hid := X.δ_comp_σ_of_le hkq
  have happ := congrArg
    (fun f : X _⦋m + 1⦌ ⟶ X _⦋m + 1⦌ ↦
      f.hom (target - X.δ (Fin.castSucc q.succ) y)) hid
  change X.δ (Fin.castSucc k) (X.σ q.succ
      (target - X.δ (Fin.castSucc q.succ) y)) =
    X.σ q (X.δ k (target - X.δ (Fin.castSucc q.succ) y)) at happ
  rw [happ, herr, map_zero]

/-- A downward correction at a nonfinal degeneracy preserves a higher face once the
corresponding higher face of its error vanishes.  This is the ordered identity
`d_{i+1} s_r = s_r d_i`. -/
theorem face_correctDown_castSucc_eq_of_higher_error {m : ℕ} (r : Fin (m + 1))
    (i : Fin (m + 2)) (hri : Fin.castSucc r < i)
    (target : X _⦋m + 1⦌) (y : X _⦋m + 2⦌)
    (herr : X.δ i (target - X.δ (Fin.castSucc r).succ y) = 0) :
    X.δ i.succ (correctDown X (Fin.castSucc r) target y) = X.δ i.succ y := by
  apply face_correctDown_eq_of_correction_eq_zero
  have hid := X.δ_comp_σ_of_gt hri
  have happ := congrArg
    (fun f : X _⦋m + 1⦌ ⟶ X _⦋m + 1⦌ ↦
      f.hom (target - X.δ (Fin.castSucc r).succ y)) hid
  change X.δ i.succ (X.σ (Fin.castSucc r)
      (target - X.δ (Fin.castSucc r).succ y)) =
    X.σ r (X.δ i (target - X.δ (Fin.castSucc r).succ y)) at happ
  rw [happ, herr, map_zero]

/-- Before correcting the lower face `a`, every already-correct lower face `j < a`
annihilates the new error.  This is the index-sensitive compatibility calculation at the
heart of the ascending fold. -/
theorem lower_face_error_eq_zero {m : ℕ} (i j a : Fin (m + 3))
    (hja : j < a) (hai : a < i)
    (f : ∀ (k : Fin (m + 3)) (_ : k ≠ i), Δ[m + 1] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋m + 2⦌)
    (hy : X.δ j y = faceValue X f j (ne_of_lt (hja.trans hai))) :
    X.δ (belowDegeneracyIndex (i := a) (j := j) hja)
      (faceValue X f a (ne_of_lt hai) - X.δ a y) = 0 := by
  apply lower_error_eq_zero
  simp only [belowDegeneracyIndex]
  rw [← faceValue_compat X f hf j a (ne_of_lt (hja.trans hai)) (ne_of_lt hai) hja]
  have hdeg : belowDegeneracyIndex (i := a) (j := j) hja ≤
      aboveDegeneracyIndex (i := j) (j := a) hja := by
    change j.val ≤ (a.pred (Fin.ne_zero_of_lt hja)).val
    simp only [Fin.val_pred]
    omega
  have hs := ((additiveUnderlyingSSet X).δ_comp_δ_apply hdeg y).symm
  have hs' := congrArg (additiveUnderlyingSSetObjEquiv X m) hs
  simp only [additiveUnderlyingSSetObjEquiv, additiveUnderlyingSSet_δ_apply,
    belowDegeneracyIndex, aboveDegeneracyIndex,
    Fin.succ_pred, Fin.castSucc_castPred, hy] at hs'
  exact hs'

theorem lower_face_error_eq_zero_of_ne {m : ℕ} (i j a : Fin (m + 3))
    (hja : j < a) (hj : j ≠ i) (ha : a ≠ i)
    (f : ∀ (k : Fin (m + 3)) (_ : k ≠ i), Δ[m + 1] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋m + 2⦌)
    (hy : X.δ j y = faceValue X f j hj) :
    X.δ (belowDegeneracyIndex (i := a) (j := j) hja)
      (faceValue X f a ha - X.δ a y) = 0 := by
  apply lower_error_eq_zero
  simp only [belowDegeneracyIndex]
  rw [← faceValue_compat X f hf j a hj ha hja]
  have hdeg : belowDegeneracyIndex (i := a) (j := j) hja ≤
      aboveDegeneracyIndex (i := j) (j := a) hja := by
    change j.val ≤ (a.pred (Fin.ne_zero_of_lt hja)).val
    simp only [Fin.val_pred]
    omega
  have hs := ((additiveUnderlyingSSet X).δ_comp_δ_apply hdeg y).symm
  have hs' := congrArg (additiveUnderlyingSSetObjEquiv X m) hs
  simp only [additiveUnderlyingSSetObjEquiv, additiveUnderlyingSSet_δ_apply,
    belowDegeneracyIndex, aboveDegeneracyIndex, Fin.succ_pred, Fin.castSucc_castPred, hy]
    at hs'
  exact hs'

/-- The descending counterpart: before correcting `a`, an already-correct higher face
`j > a` annihilates the new error. -/
theorem higher_face_error_eq_zero {m : ℕ} (i a j : Fin (m + 3))
    (hia : i < a) (haj : a < j)
    (f : ∀ (k : Fin (m + 3)) (_ : k ≠ i), Δ[m + 1] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋m + 2⦌)
    (hy : X.δ j y = faceValue X f j (ne_of_gt (hia.trans haj))) :
    X.δ (aboveDegeneracyIndex (i := a) (j := j) haj)
      (faceValue X f a (ne_of_gt hia) - X.δ a y) = 0 := by
  apply higher_error_eq_zero
  simp only [aboveDegeneracyIndex]
  rw [faceValue_compat X f hf a j (ne_of_gt hia) (ne_of_gt (hia.trans haj)) haj]
  have hdeg : belowDegeneracyIndex (i := j) (j := a) haj ≤
      aboveDegeneracyIndex (i := a) (j := j) haj := by
    change a.val ≤ (j.pred (Fin.ne_zero_of_lt haj)).val
    simp only [Fin.val_pred]
    omega
  have hs := (additiveUnderlyingSSet X).δ_comp_δ_apply hdeg y
  have hs' := congrArg (additiveUnderlyingSSetObjEquiv X m) hs
  simp only [additiveUnderlyingSSetObjEquiv, additiveUnderlyingSSet_δ_apply,
    belowDegeneracyIndex, aboveDegeneracyIndex, Fin.succ_pred, Fin.castSucc_castPred, hy]
    at hs'
  exact hs'

@[simp]
theorem face_upTransition_self {n : ℕ} (i a : Fin (n + 2)) (hai : a < i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (y : X _⦋n + 1⦌) :
    X.δ a (upTransition X i f y a) = faceValue X f a (ne_of_lt hai) := by
  rw [upTransition_of_lt X i a hai]
  simpa only [belowDegeneracyIndex_castSucc] using
    face_correctUp_self X (belowDegeneracyIndex hai) (faceValue X f a (ne_of_lt hai)) y

theorem face_upTransition_preserved {n : ℕ} (i j a : Fin (n + 2))
    (hja : j < a) (hai : a < i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋n + 1⦌)
    (hy : X.δ j y = faceValue X f j (ne_of_lt (hja.trans hai))) :
    X.δ j (upTransition X i f y a) = faceValue X f j (ne_of_lt (hja.trans hai)) := by
  cases n with
  | zero => omega
  | succ m =>
      rw [upTransition_of_lt X i a hai]
      let k : Fin (m + 2) := j.castPred (Fin.ne_last_of_lt hja)
      let r : Fin (m + 2) := belowDegeneracyIndex hai
      let q : Fin (m + 1) := r.pred (by
        apply Fin.ne_of_gt
        change 0 < r.val
        have hr : r.val = a.val := by simp [r, belowDegeneracyIndex]
        rw [hr]
        omega)
      have hk : Fin.castSucc k = j := by simp [k]
      have hq : q.succ = r := by simp [q]
      have hkr : k ≤ Fin.castSucc q := by
        change k.val ≤ q.val
        have hkval : k.val = j.val := by simp [k]
        have hrval : r.val = a.val := by simp [r, belowDegeneracyIndex]
        simp only [q, Fin.val_pred]
        rw [hkval, hrval]
        omega
      have hz := lower_face_error_eq_zero X i j a hja hai f hf y hy
      have hz' : X.δ k
          (faceValue X f a (ne_of_lt hai) - X.δ (Fin.castSucc q.succ) y) = 0 := by
        simpa only [k, belowDegeneracyIndex, Fin.castSucc_castPred, hq, r,
          belowDegeneracyIndex_castSucc] using hz
      have hp := face_correctUp_succ_eq_of_lower_error X q k hkr
        (faceValue X f a (ne_of_lt hai)) y hz'
      have hp' : X.δ j
          (correctUp X (belowDegeneracyIndex hai) (faceValue X f a (ne_of_lt hai)) y) =
          X.δ j y := by
        simpa only [hk, hq, r] using hp
      exact hp'.trans hy

/-- After the ascending pass, every face below the missing face has its prescribed horn
value. -/
theorem face_upFold {n : ℕ} (i j : Fin (n + 2)) (hji : j < i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) :
    X.δ j (upFold X i f) = faceValue X f j (ne_of_lt hji) := by
  obtain ⟨pre, post, hlist, hpost⟩ := belowIndices_focus i j hji
  unfold upFold
  rw [hlist]
  apply foldl_property_from_focus_mem
    (P := fun y ↦ X.δ j y = faceValue X f j (ne_of_lt hji))
  · intro y
    exact face_upTransition_self X i j hji f y
  · intro y a ha hy
    have hai : a < i := (mem_belowIndices i a).mp (by rw [hlist]; simp [ha])
    exact face_upTransition_preserved X i j a (hpost a ha) hai f hf y hy

@[simp]
theorem face_downTransition_self {n : ℕ} (i a : Fin (n + 2)) (hia : i < a)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (y : X _⦋n + 1⦌) :
    X.δ a (downTransition X i f y a) = faceValue X f a (ne_of_gt hia) := by
  rw [downTransition_of_lt X i a hia]
  simpa only [aboveDegeneracyIndex_succ] using
    face_correctDown_self X (aboveDegeneracyIndex hia) (faceValue X f a (ne_of_gt hia)) y

theorem face_downTransition_higher_preserved {n : ℕ} (i a j : Fin (n + 2))
    (hia : i < a) (haj : a < j)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋n + 1⦌)
    (hy : X.δ j y = faceValue X f j (ne_of_gt (hia.trans haj))) :
    X.δ j (downTransition X i f y a) = faceValue X f j (ne_of_gt (hia.trans haj)) := by
  cases n with
  | zero => omega
  | succ m =>
      rw [downTransition_of_lt X i a hia]
      let s : Fin (m + 2) := aboveDegeneracyIndex hia
      let r : Fin (m + 1) := s.castPred (by
        intro hs
        have hv := congrArg Fin.val hs
        simp only [s, aboveDegeneracyIndex, Fin.val_pred, Fin.val_last] at hv
        omega)
      let t : Fin (m + 2) := aboveDegeneracyIndex haj
      have hrs : Fin.castSucc r = s := by simp [r]
      have hsa : s.succ = a := by simp [s]
      have htj : t.succ = j := by simp [t]
      have hrt : Fin.castSucc r < t := by
        change r.val < t.val
        have hrval : r.val = a.val - 1 := by simp [r, s, aboveDegeneracyIndex]
        have htval : t.val = j.val - 1 := by simp [t, aboveDegeneracyIndex]
        rw [hrval, htval]
        omega
      have hz := higher_face_error_eq_zero X i a j hia haj f hf y hy
      have hz' : X.δ t
          (faceValue X f a (ne_of_gt hia) - X.δ (Fin.castSucc r).succ y) = 0 := by
        simpa only [t, aboveDegeneracyIndex, hrs, hsa] using hz
      have hp := face_correctDown_castSucc_eq_of_higher_error X r t hrt
        (faceValue X f a (ne_of_gt hia)) y hz'
      have hp' : X.δ j
          (correctDown X (aboveDegeneracyIndex hia) (faceValue X f a (ne_of_gt hia)) y) =
          X.δ j y := by
        simpa only [htj, hrs, s] using hp
      exact hp'.trans hy

/-- The descending pass establishes every face above the missing face. -/
theorem face_hornFillValue_of_gt {n : ℕ} (i j : Fin (n + 2)) (hij : i < j)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) :
    X.δ j (hornFillValue X i f) = faceValue X f j (ne_of_gt hij) := by
  obtain ⟨pre, post, hlist, hpost⟩ := aboveIndices_focus i j hij
  unfold hornFillValue
  rw [hlist]
  apply foldl_property_from_focus_mem
    (P := fun y ↦ X.δ j y = faceValue X f j (ne_of_gt hij))
  · intro y
    exact face_downTransition_self X i j hij f y
  · intro y a ha hy
    have hia : i < a := (mem_aboveIndices i a).mp (by rw [hlist]; simp [ha])
    exact face_downTransition_higher_preserved X i a j hia (hpost a ha) f hf y hy

theorem face_downTransition_lower_preserved {n : ℕ} (j i a : Fin (n + 2))
    (hji : j < i) (hia : i < a)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) (y : X _⦋n + 1⦌)
    (hy : X.δ j y = faceValue X f j (ne_of_lt hji)) :
    X.δ j (downTransition X i f y a) = faceValue X f j (ne_of_lt hji) := by
  cases n with
  | zero => omega
  | succ m =>
      rw [downTransition_of_lt X i a hia]
      let k : Fin (m + 2) := j.castPred (Fin.ne_last_of_lt (hji.trans hia))
      let s : Fin (m + 2) := aboveDegeneracyIndex hia
      let q : Fin (m + 1) := s.pred (by
        apply Fin.ne_of_gt
        change 0 < s.val
        have hs : s.val = a.val - 1 := by simp [s, aboveDegeneracyIndex]
        rw [hs]
        omega)
      have hk : Fin.castSucc k = j := by simp [k]
      have hqs : q.succ = s := by simp [q]
      have hsa : s.succ = a := by simp [s]
      have hkq : k ≤ Fin.castSucc q := by
        change k.val ≤ q.val
        have hkval : k.val = j.val := by simp [k]
        have hsval : s.val = a.val - 1 := by simp [s, aboveDegeneracyIndex]
        simp only [q, Fin.val_pred]
        rw [hkval, hsval]
        omega
      have hz := lower_face_error_eq_zero_of_ne X i j a (hji.trans hia)
        (ne_of_lt hji) (ne_of_gt hia) f hf y hy
      have hz' : X.δ k
          (faceValue X f a (ne_of_gt hia) - X.δ s.succ y) = 0 := by
        simpa only [k, belowDegeneracyIndex, Fin.castSucc_castPred, hsa] using hz
      unfold correctDown
      have hp := face_add_sigma_succ_eq_of_lower_error X q k hkq y
        (faceValue X f a (ne_of_gt hia) - X.δ s.succ y) hz'
      have hp' : X.δ j
          (y + X.σ s (faceValue X f a (ne_of_gt hia) - X.δ s.succ y)) = X.δ j y := by
        simpa only [hk, hqs] using hp
      exact hp'.trans hy

/-- The descending pass preserves all faces established by the ascending pass. -/
theorem face_hornFillValue_of_lt {n : ℕ} (i j : Fin (n + 2)) (hji : j < i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) :
    X.δ j (hornFillValue X i f) = faceValue X f j (ne_of_lt hji) := by
  unfold hornFillValue
  apply foldl_invariant_mem
    (P := fun y ↦ X.δ j y = faceValue X f j (ne_of_lt hji))
  · exact face_upFold X i j hji f hf
  · intro y a ha hy
    have hia : i < a := (mem_aboveIndices i a).mp ha
    exact face_downTransition_lower_preserved X j i a hji hia f hf y hy

theorem face_hornFillValue {n : ℕ} (i j : Fin (n + 2)) (hj : j ≠ i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) :
    X.δ j (hornFillValue X i f) = faceValue X f j hj := by
  rcases lt_or_gt_of_ne hj with hji | hij
  · simpa only using face_hornFillValue_of_lt X i j hji f hf
  · simpa only using face_hornFillValue_of_gt X i j hij f hf

theorem delta_hornFiller {n : ℕ} (i j : Fin (n + 2)) (hj : j ≠ i)
    (f : ∀ (k : Fin (n + 2)) (_ : k ≠ i), Δ[n] ⟶ additiveUnderlyingSSet X)
    (hf : SSet.horn.IsCompatible f) :
    SSet.stdSimplex.δ j ≫ hornFiller X i f = f j hj := by
  apply SSet.yonedaEquiv.injective
  rw [yonedaEquiv_delta_comp, yonedaEquiv_hornFiller]
  change X.δ j (hornFillValue X i f) = faceValue X f j hj
  exact face_hornFillValue X i j hj f hf

/-- The simplicial set underlying every simplicial abelian group is a Kan complex. -/
instance additiveUnderlyingSSet_kanComplex : SSet.KanComplex (additiveUnderlyingSSet X) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  exact ⟨hornFiller X i f, fun j hj ↦ delta_hornFiller X i j hj f hf⟩

end AdditiveHorn

end Infinity
end LeanLCAExactChallenge
