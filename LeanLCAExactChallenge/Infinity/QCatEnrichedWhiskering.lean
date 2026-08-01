/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge

/-!
# Whiskering in the strict bicategory of quasicategories

This file identifies the transported `Cat`-enriched whiskering maps on quasicategories with the
homotopy-category images of precomposition and postcomposition on simplicial internal Homs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory
open Opposite Simplicial
open scoped MonoidalCategory Bicategory

/-- The simplicial enrichment and cartesian-closed enrichment of simplicial sets have the same
ordinary-Hom representative. -/
theorem sset_eHomEquiv_eq_curry'
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    @eHomEquiv SSet _ _ SSet _ _ X Y f =
      MonoidalClosed.curry' f := by
  rfl

/-- The simplicial enrichment and cartesian-closed enrichment of simplicial sets have the same
composition map. -/
theorem sset_eComp_eq_monoidalClosed_comp
    (X Y Z : SSet.{u}) :
    @eComp SSet _ _ SSet _ X Y Z =
      MonoidalClosed.comp X Y Z := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_eq]
  ext U x
  rcases x with ⟨a, b⟩
  rfl

/-- Precomposition in the simplicial enrichment is the cartesian-closed internal-Hom
precomposition map. -/
theorem sset_eHomWhiskerRight_eq_internalHomPrecomp
    {X Y : SSet.{u}} (f : X ⟶ Y) (Z : SSet.{u}) :
    @eHomWhiskerRight SSet _ _ SSet _ _ X Y f Z =
      internalHomPrecomp f Z := by
  dsimp [eHomWhiskerRight, internalHomPrecomp]
  rw [sset_eHomEquiv_eq_curry', sset_eComp_eq_monoidalClosed_comp]
  exact MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight SSet f Z

/-- Transporting enrichment carries enriched precomposition to the image of the original
precomposition. -/
theorem transportEnrichment_eHomWhiskerRight
    {V : Type v} [Category V] [MonoidalCategory V]
    {W : Type w} [Category W] [MonoidalCategory W]
    (F : V ⥤ W) [F.LaxMonoidal]
    (C : Type u) [Category C] [EnrichedOrdinaryCategory V C]
    (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
    (h : ∀ v : V, ∀ f : 𝟙_ V ⟶ v,
      e v f = Functor.LaxMonoidal.ε F ≫ F.map f)
    {X X' : C} (f : X ⟶ X') (Y : C) :
    @eHomWhiskerRight W _ _ (TransportEnrichment F C) _
      (TransportEnrichment.enrichedOrdinaryCategory (F := F) C e h)
      (show TransportEnrichment F C from X)
      (show TransportEnrichment F C from X') f Y =
      F.map (@eHomWhiskerRight V _ _ C _ _ X X' f Y) := by
  letI : EnrichedOrdinaryCategory W (TransportEnrichment F C) :=
    TransportEnrichment.enrichedOrdinaryCategory (F := F) C e h
  dsimp [eHomWhiskerRight]
  rw [TransportEnrichment.eComp_eq]
  dsimp +instances [TransportEnrichment.enrichedOrdinaryCategory]
  rw [show (@eHomEquiv W _ _ (TransportEnrichment F C) _ _
      (show TransportEnrichment F C from X)
      (show TransportEnrichment F C from X') f) =
      Functor.LaxMonoidal.ε F ≫ F.map ((eHomEquiv V) f) by
    exact h _ _]
  change (λ_ (F.obj (X' ⟶[V] Y))).inv ≫
      (Functor.LaxMonoidal.ε F ≫ F.map ((eHomEquiv V) f)) ▷
        F.obj (X' ⟶[V] Y) ≫
      Functor.LaxMonoidal.μ F (X ⟶[V] X') (X' ⟶[V] Y) ≫
        F.map (eComp V X X' Y) =
      F.map ((λ_ (X' ⟶[V] Y)).inv ≫
        (eHomEquiv V) f ▷ (X' ⟶[V] Y) ≫ eComp V X X' Y)
  rw [F.map_comp, F.map_comp]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  rw [← tensorHom_id]
  rw [← tensorHom_id]
  rw [← F.map_id]
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [tensorHom_def_assoc]
  rw [F.map_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
  rw [tensorHom_id]

set_option backward.isDefEq.respectTransparency false in
/-- In the `Cat`-enrichment of quasicategories, precomposition is the homotopy-category image of
the simplicial internal-Hom precomposition map. -/
theorem qcat_eHomWhiskerRight_eq_hoFunctor_map_internalHomPrecomp
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) (A : SSet.QCat.{u}) :
    @eHomWhiskerRight Cat _ _ SSet.QCat _ _ X Y f A =
      SSet.hoFunctor.map (internalHomPrecomp f.hom A.obj) := by
  rw [transportEnrichment_eHomWhiskerRight
    (F := SSet.hoFunctor) SSet.QCat
    (SSet.hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
    (congrArg (Functor.toCatHom) <| SSet.hoFunctor.unitHomEquiv_eq · ·)]
  change SSet.hoFunctor.map
      (@eHomWhiskerRight SSet _ _ SSet _ _ X.obj Y.obj f.hom A.obj) = _
  rw [sset_eHomWhiskerRight_eq_internalHomPrecomp]

/-- Horizontal composition with an identity `2`-cell on the left is the enriched
precomposition functor on morphisms. -/
theorem catEnriched_hComp_id_left
    {C : Type (u + 1)} [EnrichedCategory Cat.{u, u} C]
    {a b c : CategoryTheory.CatEnriched C}
    (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') :
    CategoryTheory.CatEnriched.hComp (𝟙 f) η =
      (eHomWhiskerRight Cat f c).toFunctor.map η := by
  rfl

/-- Horizontal composition with an identity `2`-cell on the right is the enriched
postcomposition functor on morphisms. -/
theorem catEnriched_hComp_id_right
    {C : Type (u + 1)} [EnrichedCategory Cat.{u, u} C]
    {a b c : CategoryTheory.CatEnriched C}
    {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    CategoryTheory.CatEnriched.hComp η (𝟙 g) =
      (eHomWhiskerLeft Cat a g).toFunctor.map η := by
  rfl

/-- The base morphism of left whiskering in the strict bicategory of quasicategories is the
homotopy-category image of simplicial internal-Hom precomposition. -/
theorem qcat_base_whiskerLeft_heq
    {A B D : SSet.QCat.{u}} (L : A ⟶ B) {f g : B ⟶ D} (η : f ⟶ g) :
    HEq (CategoryTheory.CatEnrichedOrdinary.Hom.base (L ◁ η))
      ((SSet.hoFunctor.map (internalHomPrecomp L.hom D.obj)).toFunctor.map
        (CategoryTheory.CatEnrichedOrdinary.Hom.base η)) := by
  change HEq (CategoryTheory.CatEnrichedOrdinary.Hom.base
      (CategoryTheory.CatEnrichedOrdinary.hComp (𝟙 L) η)) _
  rw [catEnrichedOrdinary_base_hComp]
  rw [CategoryTheory.CatEnrichedOrdinary.Hom.base_id]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  have hcomp := catEnriched_hComp_id_left
    (C := SSet.QCat.{u})
    (f := CategoryTheory.CatEnrichedOrdinary.homEquiv L)
    (η := CategoryTheory.CatEnrichedOrdinary.Hom.base η)
  refine (heq_of_eq hcomp).trans ?_
  change HEq ((@eHomWhiskerRight Cat _ _ SSet.QCat _ _ A B L D).toFunctor.map
    (CategoryTheory.CatEnrichedOrdinary.Hom.base η)) _
  rw! (castMode := .all)
    [qcat_eHomWhiskerRight_eq_hoFunctor_map_internalHomPrecomp L D]
  exact HEq.rfl

/-- The base morphism of right whiskering in the strict bicategory of quasicategories is the
homotopy-category image of simplicial internal-Hom postcomposition. -/
theorem qcat_base_whiskerRight_heq
    {A B D : SSet.QCat.{u}} {f g : A ⟶ B} (η : f ⟶ g) (R : B ⟶ D) :
    HEq (CategoryTheory.CatEnrichedOrdinary.Hom.base (η ▷ R))
      ((SSet.hoFunctor.map ((ihom A.obj).map R.hom)).toFunctor.map
        (CategoryTheory.CatEnrichedOrdinary.Hom.base η)) := by
  change HEq (CategoryTheory.CatEnrichedOrdinary.Hom.base
      (CategoryTheory.CatEnrichedOrdinary.hComp η (𝟙 R))) _
  rw [catEnrichedOrdinary_base_hComp]
  rw [CategoryTheory.CatEnrichedOrdinary.Hom.base_id]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  have hcomp := catEnriched_hComp_id_right
    (C := SSet.QCat.{u})
    (η := CategoryTheory.CatEnrichedOrdinary.Hom.base η)
    (g := CategoryTheory.CatEnrichedOrdinary.homEquiv R)
  refine (heq_of_eq hcomp).trans ?_
  change HEq ((@eHomWhiskerLeft Cat _ _ SSet.QCat _ _ A B D R).toFunctor.map
    (CategoryTheory.CatEnrichedOrdinary.Hom.base η)) _
  rw! (castMode := .all) [qcat_eHomWhiskerLeft_eq_hoFunctor_map_ihom A R]
  exact HEq.rfl

/-- Applying the homotopy-category functor to an edge is heterogeneously equal to the
homotopy class of the mapped edge. -/
theorem edgeHomotopyClass_map_heq
    {X Y : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) (F : X ⟶ Y) :
    HEq ((SSet.hoFunctor.map F).toFunctor.map (edgeHomotopyClass e))
      (edgeHomotopyClass (e.map F)) := by
  rfl

/-- Changing only the endpoint witnesses of an edge does not change its homotopy class. -/
theorem edgeHomotopyClass_castEndpoints_heq
    {X : SSet.{u}} {x₀ x₁ y₀ y₁ : X _⦋0⦌}
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (e : SSet.Edge y₀ y₁) :
    HEq (edgeHomotopyClass (SSet.Edge.castEndpoints h₀ h₁ e))
      (edgeHomotopyClass e) := by
  subst y₀
  subst y₁
  rfl

end LeanLCAExactChallenge.Infinity
