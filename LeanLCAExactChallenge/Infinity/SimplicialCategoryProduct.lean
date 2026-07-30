/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Products of simplicial categories

The coherent nerve construction uses enriched functors as simplices.  This file gives the
pointwise product enrichment and the resulting product comparison for coherent nerves.
-/

set_option autoImplicit false

noncomputable section

universe u v w

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Opposite Simplicial

/-- The object type of the pointwise product of two simplicially enriched categories. -/
def SimplicialEnrichedProduct (C : Type u) (D : Type u) := C × D

namespace SimplicialEnrichedProduct

variable (C D : Type u)
  [CategoryTheory.EnrichedCategory SSet.{v} C]
  [CategoryTheory.EnrichedCategory SSet.{v} D]

private def homObj (X Y : SimplicialEnrichedProduct C D) : SSet.{v} :=
  (X.1 ⟶[SSet] Y.1) ⊗ (X.2 ⟶[SSet] Y.2)

private def idMap (X : SimplicialEnrichedProduct C D) :
    𝟙_ SSet.{v} ⟶ homObj C D X X :=
  CartesianMonoidalCategory.lift
    (CategoryTheory.eId SSet X.1)
    (CategoryTheory.eId SSet X.2)

private def firstPairMap (X Y Z : SimplicialEnrichedProduct C D) :
    homObj C D X Y ⊗ homObj C D Y Z ⟶
      (X.1 ⟶[SSet] Y.1) ⊗ (Y.1 ⟶[SSet] Z.1) :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _)
    (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.fst _ _)

private def secondPairMap (X Y Z : SimplicialEnrichedProduct C D) :
    homObj C D X Y ⊗ homObj C D Y Z ⟶
      (X.2 ⟶[SSet] Y.2) ⊗ (Y.2 ⟶[SSet] Z.2) :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _)
    (CartesianMonoidalCategory.snd _ _ ≫ CartesianMonoidalCategory.snd _ _)

private def compMap (X Y Z : SimplicialEnrichedProduct C D) :
    homObj C D X Y ⊗ homObj C D Y Z ⟶ homObj C D X Z :=
  CartesianMonoidalCategory.lift
    (firstPairMap C D X Y Z ≫ CategoryTheory.eComp SSet X.1 Y.1 Z.1)
    (secondPairMap C D X Y Z ≫ CategoryTheory.eComp SSet X.2 Y.2 Z.2)

instance enrichedCategory :
    CategoryTheory.EnrichedCategory SSet.{v} (SimplicialEnrichedProduct C D) where
  Hom := homObj C D
  id := idMap C D
  comp := compMap C D
  id_comp X Y := by
    ext U x
    rcases x with ⟨xC, xD⟩
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app U xC)
        (CategoryTheory.e_id_comp SSet X.1 Y.1)
    · exact congrArg (fun f ↦ f.app U xD)
        (CategoryTheory.e_id_comp SSet X.2 Y.2)
  comp_id X Y := by
    ext U x
    rcases x with ⟨xC, xD⟩
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app U xC)
        (CategoryTheory.e_comp_id SSet X.1 Y.1)
    · exact congrArg (fun f ↦ f.app U xD)
        (CategoryTheory.e_comp_id SSet X.2 Y.2)
  assoc W X Y Z := by
    ext U x
    rcases x with ⟨⟨fC, fD⟩, ⟨⟨gC, gD⟩, ⟨hC, hD⟩⟩⟩
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app U (fC, (gC, hC)))
        (CategoryTheory.e_assoc SSet W.1 X.1 Y.1 Z.1)
    · exact congrArg (fun f ↦ f.app U (fD, (gD, hD)))
        (CategoryTheory.e_assoc SSet W.2 X.2 Y.2 Z.2)

/-- Pair two enriched functors with the same source. -/
def pair
    {A : Type w} [CategoryTheory.EnrichedCategory SSet.{v} A]
    (F : CategoryTheory.EnrichedFunctor SSet A C)
    (G : CategoryTheory.EnrichedFunctor SSet A D) :
    CategoryTheory.EnrichedFunctor SSet A (SimplicialEnrichedProduct C D) where
  obj X := (F.obj X, G.obj X)
  map X Y := CartesianMonoidalCategory.lift (F.map X Y) (G.map X Y)
  map_id X := by
    ext U x
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app U x) (F.map_id X)
    · exact congrArg (fun f ↦ f.app U x) (G.map_id X)
  map_comp X Y Z := by
    ext U x
    apply Prod.ext
    · exact congrArg (fun f ↦ f.app U x) (F.map_comp X Y Z)
    · exact congrArg (fun f ↦ f.app U x) (G.map_comp X Y Z)

/-- First projection from the pointwise enriched product. -/
def fst : CategoryTheory.EnrichedFunctor SSet (SimplicialEnrichedProduct C D) C where
  obj X := X.1
  map _ _ := CartesianMonoidalCategory.fst _ _

/-- Second projection from the pointwise enriched product. -/
def snd : CategoryTheory.EnrichedFunctor SSet (SimplicialEnrichedProduct C D) D where
  obj X := X.2
  map _ _ := CartesianMonoidalCategory.snd _ _

@[simp]
theorem pair_fst
    {A : Type w} [CategoryTheory.EnrichedCategory SSet.{v} A]
    (F : CategoryTheory.EnrichedFunctor SSet A C)
    (G : CategoryTheory.EnrichedFunctor SSet A D) :
    CategoryTheory.EnrichedFunctor.comp SSet (pair C D F G) (fst C D) = F := by
  apply CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

@[simp]
theorem pair_snd
    {A : Type w} [CategoryTheory.EnrichedCategory SSet.{v} A]
    (F : CategoryTheory.EnrichedFunctor SSet A C)
    (G : CategoryTheory.EnrichedFunctor SSet A D) :
    CategoryTheory.EnrichedFunctor.comp SSet (pair C D F G) (snd C D) = G := by
  apply CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

@[simp]
theorem pair_projections
    {A : Type w} [CategoryTheory.EnrichedCategory SSet.{v} A]
    (F : CategoryTheory.EnrichedFunctor SSet A (SimplicialEnrichedProduct C D)) :
    pair C D
        (CategoryTheory.EnrichedFunctor.comp SSet F (fst C D))
        (CategoryTheory.EnrichedFunctor.comp SSet F (snd C D)) = F := by
  letI : CategoryTheory.EnrichedCategory SSet.{v} (C × D) :=
    enrichedCategory C D
  apply CategoryTheory.EnrichedFunctor.ext SSet (fun X ↦ by
    change ((F.obj X).1, (F.obj X).2) = F.obj X
    exact Prod.eta _)
  intro X Y
  rfl

end SimplicialEnrichedProduct

/-- The ordinary simplicial category underlying the pointwise enriched product. -/
abbrev SimplicialCategoryProduct
    (C : Type u) (D : Type u)
    [CategoryTheory.EnrichedCategory SSet.{v} C]
    [CategoryTheory.EnrichedCategory SSet.{v} D] :=
  CategoryTheory.ForgetEnrichment SSet.{v} (SimplicialEnrichedProduct C D)

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [CategoryTheory.SimplicialCategory C] [CategoryTheory.SimplicialCategory D]

/-- The coherent nerve sends the pointwise enriched product to the product of coherent nerves. -/
def simplicialNerveProductHom :
    CategoryTheory.SimplicialNerve C ⊗ CategoryTheory.SimplicialNerve D ⟶
      CategoryTheory.SimplicialNerve (SimplicialCategoryProduct C D) where
  app _ := ↾fun F ↦ SimplicialEnrichedProduct.pair C D F.1 F.2
  naturality _ _ _ := rfl

/-- Project a coherent simplex in the pointwise product to its two factors. -/
def simplicialNerveProductInv :
    CategoryTheory.SimplicialNerve (SimplicialCategoryProduct C D) ⟶
      CategoryTheory.SimplicialNerve C ⊗ CategoryTheory.SimplicialNerve D where
  app _ := ↾fun F ↦
    (CategoryTheory.EnrichedFunctor.comp SSet F (SimplicialEnrichedProduct.fst C D),
      CategoryTheory.EnrichedFunctor.comp SSet F (SimplicialEnrichedProduct.snd C D))
  naturality _ _ _ := rfl

/-- The coherent nerve preserves the explicit pointwise enriched product. -/
noncomputable def simplicialNerveProductIso :
    CategoryTheory.SimplicialNerve C ⊗ CategoryTheory.SimplicialNerve D ≅
      CategoryTheory.SimplicialNerve (SimplicialCategoryProduct C D) where
  hom := simplicialNerveProductHom C D
  inv := simplicialNerveProductInv C D
  hom_inv_id := by
    apply CategoryTheory.NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro F
    apply Prod.ext
    · exact SimplicialEnrichedProduct.pair_fst C D F.1 F.2
    · exact SimplicialEnrichedProduct.pair_snd C D F.1 F.2
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro F
    exact SimplicialEnrichedProduct.pair_projections C D F

end LeanLCAExactChallenge.Infinity
