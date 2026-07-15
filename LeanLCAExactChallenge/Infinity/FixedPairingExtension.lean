/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex

/-! # Extensions along a ranked pairing with a fixed initial map -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SSet.Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}

/-- The inclusion between two terms of the filtration associated to a rank function. -/
def filtrationMap (ρ : P.RankFunction ℕ) {n m : ℕ} (h : n ≤ m) :
    (ρ.filtration n : SSet.{u}) ⟶ ρ.filtration m :=
  SSet.Subcomplex.homOfLE (ρ.filtration_monotone h)

@[simp]
theorem filtrationMap_refl (ρ : P.RankFunction ℕ) (n : ℕ) :
    ρ.filtrationMap (le_refl n) = 𝟙 _ := rfl

@[reassoc]
theorem filtrationMap_comp (ρ : P.RankFunction ℕ) {n m k : ℕ}
    (h₁ : n ≤ m) (h₂ : m ≤ k) :
    ρ.filtrationMap h₁ ≫ ρ.filtrationMap h₂ = ρ.filtrationMap (h₁.trans h₂) := rfl

@[reassoc]
theorem filtrationMap_ι (ρ : P.RankFunction ℕ) {n m : ℕ} (h : n ≤ m) :
    ρ.filtrationMap h ≫ (ρ.filtration m).ι = (ρ.filtration n).ι := rfl

variable (ρ : P.RankFunction ℕ) [P.IsProper]

/-- The zeroth filtration term identified with the original subcomplex. -/
noncomputable def filtrationZeroIso :
    (ρ.filtration 0 : SSet.{u}) ≅ (A : SSet.{u}) :=
  SSet.Subcomplex.eqToIso (ρ.filtration_bot)

omit [P.IsProper] in
@[reassoc]
theorem filtrationZeroIso_inv_ι :
    ρ.filtrationZeroIso.inv ≫ (ρ.filtration 0).ι = A.ι := rfl

/-- Regard a map from the original subcomplex as a map from the zeroth filtration term. -/
noncomputable def initialMap {Q : SSet.{u}} (f : (A : SSet.{u}) ⟶ Q) :
    (ρ.filtration 0 : SSet.{u}) ⟶ Q :=
  ρ.filtrationZeroIso.hom ≫ f

omit [P.IsProper] in
@[reassoc (attr := simp)]
theorem filtrationZeroIso_inv_initialMap {Q : SSet.{u}}
    (f : (A : SSet.{u}) ⟶ Q) :
    ρ.filtrationZeroIso.inv ≫ ρ.initialMap f = f := by
  simp [initialMap]

/-- Cellwise fillers that are compatible with a fixed map on the zeroth filtration term. -/
def HasFixedCellFillers {Q : SSet.{u}}
    (f₀ : (ρ.filtration 0 : SSet.{u}) ⟶ Q) : Prop :=
  ∀ (n : ℕ) (g : (ρ.filtration n : SSet.{u}) ⟶ Q),
    ρ.filtrationMap (Nat.zero_le n) ≫ g = f₀ →
      ∀ c : ρ.Cell n, ∃ b : (Δ[c.dim + 1] : SSet.{u}) ⟶ Q,
        c.horn.ι ≫ b = c.mapHorn ≫ g

/-- In a quasicategory, it suffices to fill the zero-index cells when no cell has final index. -/
theorem hasFixedCellFillers_of_zero_and_inner {Q : SSet.{u}} [SSet.Quasicategory Q]
    (f₀ : (ρ.filtration 0 : SSet.{u}) ⟶ Q)
    (hneLast : ∀ (n : ℕ) (c : ρ.Cell n), c.index ≠ Fin.last (c.dim + 1))
    (hzero : ∀ (n : ℕ) (g : (ρ.filtration n : SSet.{u}) ⟶ Q),
      ρ.filtrationMap (Nat.zero_le n) ≫ g = f₀ →
        ∀ (c : ρ.Cell n), c.index = 0 →
          ∃ b : (Δ[c.dim + 1] : SSet.{u}) ⟶ Q,
            c.horn.ι ≫ b = c.mapHorn ≫ g) :
    ρ.HasFixedCellFillers f₀ := by
  intro n g hg c
  by_cases hzeroIndex : c.index = 0
  · exact hzero n g hg c hzeroIndex
  · obtain ⟨b, hb⟩ := SSet.Quasicategory.hornFilling
      (Fin.pos_iff_ne_zero.mpr hzeroIndex)
      (Fin.lt_last_iff_ne_last.mpr (hneLast n c)) (c.mapHorn ≫ g)
    exact ⟨b, hb.symm⟩

/-- An extension of the fixed initial map to one filtration term. -/
structure FixedCellState {Q : SSet.{u}}
    (f₀ : (ρ.filtration 0 : SSet.{u}) ⟶ Q) (n : ℕ) where
  map : (ρ.filtration n : SSet.{u}) ⟶ Q
  fixed : ρ.filtrationMap (Nat.zero_le n) ≫ map = f₀

namespace FixedCellState

variable {ρ} {Q : SSet.{u}} {f₀ : (ρ.filtration 0 : SSet.{u}) ⟶ Q}

/-- The initial extension state. -/
def zero : FixedCellState ρ f₀ 0 where
  map := f₀
  fixed := by simp

/-- Attach all cells of one rank using the specified fixed cell fillers. -/
noncomputable def succ (h : ρ.HasFixedCellFillers f₀) {n : ℕ}
    (s : FixedCellState ρ f₀ n) : FixedCellState ρ f₀ (n + 1) := by
  let filler (c : ρ.Cell n) : (Δ[c.dim + 1] : SSet.{u}) ⟶ Q :=
    Classical.choose (h n s.map s.fixed c)
  let fillers : ρ.sigmaStdSimplex n ⟶ Q := Sigma.desc filler
  have hw : ρ.t n ≫ s.map = ρ.m n ≫ fillers := by
    apply Sigma.hom_ext
    intro c
    rw [c.ι_t_assoc, c.ι_m_assoc, Sigma.ι_desc]
    exact (Classical.choose_spec (h n s.map s.fixed c)).symm
  let next : (ρ.filtration (n + 1) : SSet.{u}) ⟶ Q :=
    (ρ.isPushout n).desc s.map fillers hw
  have hnext : ρ.filtrationMap (Nat.le_succ n) ≫ next = s.map :=
    (ρ.isPushout n).inl_desc s.map fillers hw
  refine { map := next, fixed := ?_ }
  calc
    ρ.filtrationMap (Nat.zero_le (n + 1)) ≫ next =
        (ρ.filtrationMap (Nat.zero_le n) ≫ ρ.filtrationMap (Nat.le_succ n)) ≫ next := rfl
    _ = ρ.filtrationMap (Nat.zero_le n) ≫
        (ρ.filtrationMap (Nat.le_succ n) ≫ next) := Category.assoc _ _ _
    _ = ρ.filtrationMap (Nat.zero_le n) ≫ s.map := by rw [hnext]
    _ = f₀ := s.fixed

/-- The compatible state at every natural-number rank. -/
noncomputable def state (h : ρ.HasFixedCellFillers f₀) :
    ∀ n : ℕ, FixedCellState ρ f₀ n
  | 0 => zero
  | n + 1 => succ h (state h n)

theorem state_step (h : ρ.HasFixedCellFillers f₀) (n : ℕ) :
    ρ.filtrationMap (Nat.le_succ n) ≫ (state h (n + 1)).map = (state h n).map := by
  rw [state]
  change ρ.filtrationMap (Nat.le_succ n) ≫
      (ρ.isPushout n).desc (state h n).map _ _ = (state h n).map
  exact (ρ.isPushout n).inl_desc _ _ _

theorem state_compat (h : ρ.HasFixedCellFillers f₀) {n m : ℕ} (hnm : n ≤ m) :
    ρ.filtrationMap hnm ≫ (state h m).map = (state h n).map := by
  induction m with
  | zero =>
      obtain rfl : n = 0 := Nat.eq_zero_of_le_zero hnm
      simp
  | succ m ih =>
      obtain hnm | rfl := Nat.lt_or_eq_of_le hnm
      · rw [show ρ.filtrationMap hnm.le =
            ρ.filtrationMap (Nat.le_of_lt_succ hnm) ≫
              ρ.filtrationMap (Nat.le_succ m) by rfl,
          Category.assoc, state_step]
        exact ih (Nat.le_of_lt_succ hnm)
      · simp

/-- The compatible filtration states as a cocone. -/
noncomputable def cocone (h : ρ.HasFixedCellFillers f₀) :
    Cocone ρ.relativeCellComplex.F :=
  Cocone.mk Q
    { app n := (state h n).map
      naturality := by
        intro n m g
        exact state_compat h (CategoryTheory.leOfHom g) }

/-- Extend the fixed map from the zeroth filtration term to the ambient simplicial set. -/
noncomputable def extension (h : ρ.HasFixedCellFillers f₀) : X ⟶ Q :=
  ρ.relativeCellComplex.isColimit.desc (cocone h)

@[reassoc]
theorem extension_restrict (h : ρ.HasFixedCellFillers f₀) :
    (ρ.filtration 0).ι ≫ extension h = f₀ := by
  calc
    _ = (state h 0).map := ρ.relativeCellComplex.isColimit.fac (cocone h) 0
    _ = f₀ := rfl

end FixedCellState

/-- Extend a map from the original subcomplex once fixed cell fillers are available. -/
noncomputable def extensionFromInitial {Q : SSet.{u}} (f : (A : SSet.{u}) ⟶ Q)
    (h : ρ.HasFixedCellFillers (ρ.initialMap f)) : X ⟶ Q :=
  FixedCellState.extension h

@[reassoc]
theorem extensionFromInitial_restrict {Q : SSet.{u}} (f : (A : SSet.{u}) ⟶ Q)
    (h : ρ.HasFixedCellFillers (ρ.initialMap f)) :
    A.ι ≫ extensionFromInitial ρ f h = f := by
  rw [← ρ.filtrationZeroIso_inv_ι, Category.assoc, extensionFromInitial,
    FixedCellState.extension_restrict, ρ.filtrationZeroIso_inv_initialMap]

end SSet.Subcomplex.Pairing.RankFunction
