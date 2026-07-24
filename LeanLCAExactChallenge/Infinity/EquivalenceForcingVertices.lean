/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import LeanLCAExactChallenge.Infinity.InnerAnodyneVertices

/-! # Vertices of equivalence-forcing presentations -/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

@[simp]
theorem equivalenceIntervalInclusion_vertex_zero :
    equivalenceIntervalInclusion.{u}.app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      CategoryTheory.nerveEquiv.symm equivalenceIntervalZero := by
  unfold equivalenceIntervalInclusion
  let f : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.const _ _ 0
  have hv : SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm f := rfl
  rw [hv, SSet.yonedaEquiv_symm_app_objEquiv_symm]
  have hf : f = SimplexCategory.δ 1 := by
    apply SimplexCategory.Hom.ext_zero_left
    decide
  rw [hf]
  change (CategoryTheory.nerve EquivalenceInterval).δ 1
      (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).edge = _
  exact (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).src_eq

@[simp]
theorem equivalenceIntervalInclusion_vertex_one :
    equivalenceIntervalInclusion.{u}.app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      CategoryTheory.nerveEquiv.symm equivalenceIntervalOne := by
  unfold equivalenceIntervalInclusion
  let f : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.const _ _ 1
  have hv : SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.stdSimplex.objEquiv.symm f := rfl
  rw [hv, SSet.yonedaEquiv_symm_app_objEquiv_symm]
  have hf : f = SimplexCategory.δ 0 := by
    apply SimplexCategory.Hom.ext_zero_left
    decide
  rw [hf]
  change (CategoryTheory.nerve EquivalenceInterval).δ 0
      (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).edge = _
  exact (CategoryTheory.nerve.edgeMk equivalenceIntervalForward).tgt_eq

private theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

private def equivalenceIntervalVertexInverse
    (y : (CategoryTheory.nerve EquivalenceInterval.{u}) _⦋0⦌) :
    (Δ[1] : SSet.{u}) _⦋0⦌ :=
  match CategoryTheory.nerveEquiv y with
  | EquivalenceInterval.zero => SSet.stdSimplex.obj₀Equiv.symm 0
  | EquivalenceInterval.one => SSet.stdSimplex.obj₀Equiv.symm 1

private theorem equivalenceIntervalVertexInverse_leftInverse :
    Function.LeftInverse equivalenceIntervalVertexInverse
      (equivalenceIntervalInclusion.{u}.app (op ⦋0⦌)) := by
  intro x
  rcases fin_two_eq_zero_or_one (SSet.stdSimplex.obj₀Equiv x) with hx | hx
  · have : x = SSet.stdSimplex.obj₀Equiv.symm 0 := by
      rw [← hx]
      exact (SSet.stdSimplex.obj₀Equiv.symm_apply_apply x).symm
    subst x
    rw [equivalenceIntervalInclusion_vertex_zero]
    simp [equivalenceIntervalVertexInverse, equivalenceIntervalZero]
  · have : x = SSet.stdSimplex.obj₀Equiv.symm 1 := by
      rw [← hx]
      exact (SSet.stdSimplex.obj₀Equiv.symm_apply_apply x).symm
    subst x
    rw [equivalenceIntervalInclusion_vertex_one]
    simp [equivalenceIntervalVertexInverse, equivalenceIntervalOne]

private theorem equivalenceIntervalVertexInverse_rightInverse :
    Function.RightInverse equivalenceIntervalVertexInverse
      (equivalenceIntervalInclusion.{u}.app (op ⦋0⦌)) := by
  intro y
  let z := CategoryTheory.nerveEquiv y
  have hy : y = CategoryTheory.nerveEquiv.symm z := by
    exact (CategoryTheory.nerveEquiv.symm_apply_apply y).symm
  rcases z with (_ | _)
  · rw [hy]
    exact equivalenceIntervalInclusion_vertex_zero
  · rw [hy]
    exact equivalenceIntervalInclusion_vertex_one

/-- The standard interval and the free-living equivalence have the same vertices. -/
theorem equivalenceIntervalInclusion_vertex_bijective :
    Function.Bijective
      (equivalenceIntervalInclusion.{u}.app (op ⦋0⦌)) :=
  ⟨equivalenceIntervalVertexInverse_leftInverse.injective,
    equivalenceIntervalVertexInverse_rightInverse.surjective⟩

/-- The interval inclusion belongs to the class of maps that are isomorphisms on vertices. -/
theorem equivalenceIntervalInclusion_vertexIsomorphisms :
    vertexIsomorphisms.{u} equivalenceIntervalInclusion.{u} := by
  change IsIso (equivalenceIntervalInclusion.{u}.app (op ⦋0⦌))
  rw [isIso_iff_bijective]
  exact equivalenceIntervalInclusion_vertex_bijective

namespace RelativeCategoryData

variable {C : Type u} [Category.{v} C] (R : RelativeCategoryData C)

/-- The attaching map is the coproduct of the individual interval inclusions. -/
theorem weakIntervalsToEquivalences_eq_sigmaMap :
    weakIntervalsToEquivalences R =
      CategoryTheory.Limits.Sigma.map
        (fun _ : WeakEquivalenceArrow C R =>
          equivalenceIntervalInclusion.{max u v}) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro a
  unfold weakIntervalsToEquivalences
  rw [CategoryTheory.Limits.Sigma.ι_desc,
    CategoryTheory.Limits.Sigma.ι_map]

/-- The attaching map for free equivalences is bijective on vertices. -/
theorem weakIntervalsToEquivalences_vertex_bijective :
    Function.Bijective
      ((weakIntervalsToEquivalences R).app (op ⦋0⦌)) := by
  rw [weakIntervalsToEquivalences_eq_sigmaMap]
  have h := vertexIsomorphisms_sigmaMap
    (fun _ : WeakEquivalenceArrow C R =>
      equivalenceIntervalInclusion.{max u v})
    (fun _ => equivalenceIntervalInclusion_vertexIsomorphisms)
  change IsIso
    ((CategoryTheory.Limits.Sigma.map
      (fun _ : WeakEquivalenceArrow C R =>
        equivalenceIntervalInclusion.{max u v})).app (op ⦋0⦌)) at h
  rw [isIso_iff_bijective] at h
  exact h

/-- Adjoining free inverses does not add or identify vertices. -/
theorem toEquivalenceForcingPresentation_vertex_bijective :
    Function.Bijective
      ((toEquivalenceForcingPresentation R).app (op ⦋0⦌)) :=
  pushoutInl_vertex_bijective_of_right
    (weakIntervalsToNerve R) (weakIntervalsToEquivalences R)
    (weakIntervalsToEquivalences_vertex_bijective R)

end RelativeCategoryData

end LeanLCAExactChallenge.Infinity
