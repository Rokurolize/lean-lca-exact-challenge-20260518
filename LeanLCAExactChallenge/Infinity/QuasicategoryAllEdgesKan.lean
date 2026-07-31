/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.JoyalSpecialOuterHornDuality
import LeanLCAExactChallenge.Infinity.LeftFibrationIsoLift
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! # Quasicategories whose edges are equivalences -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite Simplicial

local instance deltaZeroObjSubsingleton (U : SimplexCategoryᵒᵖ) :
    Subsingleton ((Δ[0] : SSet.{u}).obj U) where
  allEq a b := by
    apply SSet.stdSimplex.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

open SSet.modelCategoryQuillen in
instance kanComplex_toDeltaZero_leftFibration
    (X : SSet.{u}) [SSet.KanComplex X] :
    LeftFibration (SSet.stdSimplex.isTerminalObj₀.from X) := by
  let p := SSet.stdSimplex.isTerminalObj₀.from X
  have hp : Fibration p :=
    (isFibrant_iff_of_isTerminal p SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  letI : Fibration p := hp
  constructor
  intro A B i hi
  cases hi with
  | intro j hj => infer_instance

/-- Every edge of a Kan complex is an equivalence edge. -/
theorem edgeIsEquivalence_of_kan
    (X : SSet.{u}) [SSet.KanComplex X] {x y : X _⦋0⦌}
    (e : SSet.Edge x y) : EdgeIsEquivalence e := by
  let p : X ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from X
  letI : LeftFibration p := kanComplex_toDeltaZero_leftFibration X
  letI : SSet.Quasicategory (Δ[0] : SSet.{u}) := by
    apply SSet.quasicategory_of_filler
    intro n i σ h0 hn
    exact ⟨SSet.stdSimplex.objMk (OrderHom.const _ 0),
      fun j hj ↦ Subsingleton.elim _ _⟩
  apply LeftFibration.edgeIsEquivalence_of_map p e
  let eid := SSet.Edge.id (p.app (Opposite.op ⦋0⦌) x)
  have hxy : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y :=
    Subsingleton.elim _ _
  let eid' : SSet.Edge (p.app (Opposite.op ⦋0⦌) x)
      (p.app (Opposite.op ⦋0⦌) y) :=
    SSet.Edge.castEndpoints rfl hxy eid
  have heq : e.map p = eid' := by
    apply SSet.Edge.ext
    exact Subsingleton.elim _ _
  rw [heq]
  exact (edgeIsEquivalence_id _).castEndpoints rfl hxy

/-- A quasicategory in which every edge is an equivalence is a Kan complex. -/
theorem quasicategory_all_edges_equivalences_kan
    (X : SSet.{u}) [SSet.Quasicategory X]
    (hEdge : ∀ s : X _⦋1⦌, EdgeIsEquivalence (SSet.Edge.mk' s)) :
    SSet.KanComplex X := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  cases n with
  | zero =>
      fin_cases i
      · refine ⟨SSet.const (SSet.yonedaEquiv (f 1 (by decide))), ?_⟩
        intro j hj
        fin_cases j
        · simp at hj
        · rw [SSet.comp_const]
          exact (SSet.yonedaEquiv_symm_zero _).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv _)
      · refine ⟨SSet.const (SSet.yonedaEquiv (f 0 (by decide))), ?_⟩
        intro j hj
        fin_cases j
        · rw [SSet.comp_const]
          exact (SSet.yonedaEquiv_symm_zero _).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv _)
        · simp at hj
  | succ m =>
      by_cases hi0 : i = 0
      · subst i
        obtain ⟨φ, hφ⟩ := hasAllSpecialLeftHornFillers_direct X m hf.desc (hEdge _)
        refine ⟨φ, fun j hj ↦ ?_⟩
        rw [← SSet.horn.ι_ι_assoc (0 : Fin (m + 3)) j hj, hφ, hf.ι_desc]
      · by_cases hilast : i = Fin.last (m + 2)
        · subst i
          obtain ⟨φ, hφ⟩ := hasAllSpecialRightHornFillers_direct X m hf.desc (hEdge _)
          refine ⟨φ, fun j hj ↦ ?_⟩
          rw [← SSet.horn.ι_ι_assoc (Fin.last (m + 2)) j hj, hφ, hf.ι_desc]
        · obtain ⟨φ, hφ⟩ := SSet.Quasicategory.hornFilling
            (Fin.pos_iff_ne_zero.mpr hi0) (Fin.val_lt_last hilast) hf.desc
          refine ⟨φ, fun j hj ↦ ?_⟩
          rw [← SSet.horn.ι_ι_assoc i j hj, ← hφ, hf.ι_desc]

end Infinity
end LeanLCAExactChallenge
