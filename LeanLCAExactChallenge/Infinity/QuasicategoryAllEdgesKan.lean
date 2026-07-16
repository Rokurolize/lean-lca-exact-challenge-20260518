/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.JoyalSpecialOuterHornDuality
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! # Quasicategories whose edges are equivalences -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory Opposite Simplicial

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
