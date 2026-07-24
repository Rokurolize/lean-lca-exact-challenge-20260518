/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-! # Vertices of inner anodyne extensions -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open Opposite Simplicial

/-- Evaluation of a simplicial set on vertices. -/
abbrev vertexEvaluation : SSet.{u} ⥤ Type u :=
  SSet.evaluation.obj (op ⦋0⦌)

/-- Simplicial maps whose map on vertices is an isomorphism of types. -/
def vertexIsomorphisms : MorphismProperty SSet.{u} :=
  (isomorphisms (Type u)).inverseImage vertexEvaluation

private instance vertexIsomorphisms_isStableUnderColimitsOfShape
    (J : Type u) [Category.{u} J] :
    vertexIsomorphisms.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    let E := vertexEvaluation.{u}
    let d₁ := E.mapCocone c₁
    let d₂ := E.mapCocone c₂
    let f' := Functor.whiskerRight f E
    have hd₁ : IsColimit d₁ := isColimitOfPreserves E h₁
    have hd₂ : IsColimit d₂ := isColimitOfPreserves E h₂
    have hf' : (isomorphisms (Type u)).functorCategory J f' := by
      intro j
      exact hf j
    have hφ' : ∀ j, d₁.ι.app j ≫ E.map φ = f'.app j ≫ d₂.ι.app j := by
      intro j
      change E.map (c₁.ι.app j) ≫ E.map φ =
        E.map (f.app j) ≫ E.map (c₂.ι.app j)
      rw [← E.map_comp, ← E.map_comp, hφ j]
      rfl
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := isomorphisms (Type u)) (X₁ ⋙ E) (X₂ ⋙ E) d₁ d₂ hd₁ hd₂ f' hf'
        (E.map φ) hφ'

private instance vertexIsomorphisms_isStableUnderCobaseChange :
    vertexIsomorphisms.{u}.IsStableUnderCobaseChange where
  of_isPushout {A A' B B'} {f g f' g'} sq hf := by
    let E := vertexEvaluation.{u}
    change IsIso (E.map f')
    letI : IsIso (E.map f) := hf
    exact (sq.map E).isIso_inl_of_isIso

private instance vertexIsomorphisms_isStableUnderCoproducts :
    vertexIsomorphisms.{u}.IsStableUnderCoproducts.{u} where
  isStableUnderCoproductsOfShape J :=
    vertexIsomorphisms_isStableUnderColimitsOfShape (Discrete J)

private instance vertexIsomorphisms_isStableUnderFilteredColimits :
    vertexIsomorphisms.{u}.IsStableUnderFilteredColimits.{u, u} where
  isStableUnderColimitsOfShape J :=
    vertexIsomorphisms_isStableUnderColimitsOfShape J

private instance vertexIsomorphisms_respectsIso :
    vertexIsomorphisms.{u}.RespectsIso := by
  dsimp only [vertexIsomorphisms]
  infer_instance

private instance vertexIsomorphisms_isMultiplicative :
    vertexIsomorphisms.{u}.IsMultiplicative := by
  dsimp only [vertexIsomorphisms]
  infer_instance

private instance vertexIsomorphisms_isStableUnderRetracts :
    vertexIsomorphisms.{u}.IsStableUnderRetracts := by
  dsimp only [vertexIsomorphisms]
  infer_instance

private instance vertexIsomorphisms_isStableUnderTransfiniteComposition :
    vertexIsomorphisms.{u}.IsStableUnderTransfiniteComposition.{u} := by
  infer_instance

/-- A coproduct of maps that are isomorphisms on vertices is again an isomorphism on
vertices. -/
theorem vertexIsomorphisms_sigmaMap
    {β : Type u} {X Y : β → SSet.{u}} (p : ∀ b, X b ⟶ Y b)
    (hp : ∀ b, vertexIsomorphisms.{u} (p b)) :
    vertexIsomorphisms.{u} (CategoryTheory.Limits.Sigma.map p) := by
  let q : Discrete.functor X ⟶ Discrete.functor Y :=
    Discrete.natTrans fun j => p j.as
  change vertexIsomorphisms (colimMap q)
  exact vertexIsomorphisms.colimMap q (fun j => by
    change vertexIsomorphisms (p j.as)
    exact hp j.as)

/-- In a simplicial-set pushout, the first coprojection is bijective on vertices when the
second attaching map is bijective on vertices. -/
theorem pushoutInl_vertex_bijective_of_right
    {A B C : SSet.{u}} (f : A ⟶ B) (g : A ⟶ C)
    (hg : Function.Bijective (g.app (op ⦋0⦌))) :
    Function.Bijective ((pushout.inl f g).app (op ⦋0⦌)) := by
  rw [← isIso_iff_bijective]
  let E := vertexEvaluation.{u}
  change IsIso (E.map (pushout.inl f g))
  have hgIso : IsIso (E.map g) := by
    change IsIso (g.app (op ⦋0⦌))
    rw [isIso_iff_bijective]
    exact hg
  letI : IsIso (E.map g) := hgIso
  let c := PushoutCocone.mk (pushout.inl f g) (pushout.inr f g) pushout.condition
  have hc : IsColimit c := pushoutIsPushout f g
  have sq : IsPushout f g c.inl c.inr := IsPushout.of_isColimit hc
  exact (Functor.map_isPushout E sq).isIso_inl_of_isIso

/-- Every inner horn inclusion is an isomorphism on vertices. -/
theorem innerHornInclusions_le_vertexIsomorphisms :
    SSet.innerHornInclusions.{u} ≤ vertexIsomorphisms.{u} := by
  intro X Y f hf
  obtain @⟨n, i, h0, hn⟩ := hf
  change IsIso (Λ[n + 2, i].ι.app (op ⦋0⦌))
  rw [isIso_iff_bijective]
  constructor
  · intro x y hxy
    exact Subtype.ext hxy
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [SSet.horn_obj_zero]
    trivial

/-- Inner anodyne extensions do not add or identify vertices. -/
theorem innerAnodyneExtensions_le_vertexIsomorphisms :
    SSet.innerAnodyneExtensions.{u} ≤ vertexIsomorphisms.{u} := by
  rw [SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositions]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff,
    coproducts_le_iff]
  exact innerHornInclusions_le_vertexIsomorphisms

/-- The vertex map of an inner anodyne extension is bijective. -/
theorem innerAnodyne_vertex_bijective
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : SSet.innerAnodyneExtensions f) :
    Function.Bijective (f.app (op ⦋0⦌)) := by
  rw [← isIso_iff_bijective]
  exact innerAnodyneExtensions_le_vertexIsomorphisms _ hf

end LeanLCAExactChallenge.Infinity
