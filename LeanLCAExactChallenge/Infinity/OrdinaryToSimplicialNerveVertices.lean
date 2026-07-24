/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

/-! # Vertices of the ordinary-to-coherent nerve map -/

set_option autoImplicit false

noncomputable section

universe v u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Simplicial Opposite
open CoherentNervePathFiltration

namespace OrdinaryToSimplicialNerve

variable (C : Type u) [Category.{v} C] [CategoryTheory.SimplicialCategory C]

/-- Every coherent vertex is represented by the corresponding object in the ordinary nerve. -/
theorem ordinaryNerveToSimplicialNerve_vertex_surjective :
    Function.Surjective
      ((ordinaryNerveToSimplicialNerve C).app (op ⦋0⦌)) := by
  intro F
  change CategoryTheory.EnrichedFunctor SSet
    (CategoryTheory.SimplicialThickening (ULift (Fin (0 + 1)))) C at F
  let i₀ : CategoryTheory.SimplicialThickening (ULift (Fin (0 + 1))) :=
    thickeningVertex (0 : Fin (0 + 1))
  let X : CategoryTheory.ForgetEnrichment SSet.{v} C :=
    CategoryTheory.ForgetEnrichment.of SSet (F.obj i₀)
  let G := coherentSimplexOfChain C (CategoryTheory.ComposableArrows.mk₀ X)
  refine ⟨CategoryTheory.ComposableArrows.mk₀ X, ?_⟩
  change G = F
  have thickening_eq
      (i : CategoryTheory.SimplicialThickening (ULift (Fin (0 + 1)))) : i = i₀ := by
    rcases i with ⟨i⟩
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    apply Fin.ext
    omega
  let hobj : ∀ i, G.obj i = F.obj i := fun i ↦ by
    rw [thickening_eq i]
    rfl
  apply CategoryTheory.EnrichedFunctor.ext SSet hobj
  intro i j
  rw [thickening_eq i, thickening_eq j]
  letI : IsIso (CategoryTheory.eId SSet i₀) :=
    (Path.thickPathSelfEIdIso i₀).isIso_hom
  apply (cancel_epi (CategoryTheory.eId SSet i₀)).1
  rw [← Category.assoc, G.map_id, F.map_id]
  have h := hobj i₀
  cases h
  rfl

end OrdinaryToSimplicialNerve

end LeanLCAExactChallenge.Infinity
