/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.SimplicialCategoryProduct

/-!
# Enriched natural transformations and coherent homotopies

This module normalizes strict unit-graded enriched naturality into equality of the corresponding
postcomposition and precomposition maps.  It also exposes coherent-nerve functoriality, the
coherent interval, and the canonical inclusion of a coherent-nerve cylinder into the nerve of the
pointwise enriched product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w x

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

/-- The canonical central tensor unit of simplicial sets. -/
noncomputable abbrev SSetCentralUnit : Center SSet.{v} :=
  Center.tensorUnit

/-- Strict unit-graded transformations between simplicially enriched functors. -/
abbrev SSetUnitGradedNatTrans
    {C D : Type*}
    [EnrichedCategory SSet.{v} C]
    [EnrichedCategory SSet.{v} D]
    (F G : EnrichedFunctor SSet C D) :=
  GradedNatTrans SSetCentralUnit F G

section Enriched

variable {C : Type u} {D : Type w}
  [EnrichedCategory SSet.{v} C]
  [EnrichedCategory SSet.{v} D]

/-- Postcompose an enriched hom-object with one component of a strict transformation. -/
def SSetUnitGradedNatTrans.postcompose
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    (F.obj X ⟶[SSet] F.obj Y) ⟶ (F.obj X ⟶[SSet] G.obj Y) :=
  (ρ_ _).inv ≫ _ ◁ α.app Y ≫ eComp SSet _ _ _

/-- Precompose an enriched hom-object with one component of a strict transformation. -/
def SSetUnitGradedNatTrans.precompose
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    (X ⟶[SSet] Y) ⟶ (F.obj X ⟶[SSet] G.obj Y) :=
  (λ_ _).inv ≫ α.app X ▷ _ ≫ _ ◁ G.map X Y ≫ eComp SSet _ _ _

@[reassoc]
theorem SSetUnitGradedNatTrans.map_postcompose_eq_precompose
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    F.map X Y ≫ α.postcompose X Y =
      α.precompose X Y := by
  have h := α.naturality X Y
  dsimp [SSetCentralUnit, Center.tensorUnit] at h
  simp only [Iso.trans_hom, Iso.symm_hom] at h
  have h' := congrArg
    (fun k ↦ (λ_ (X ⟶[SSet] Y)).inv ≫ k) h
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h'
  dsimp [SSetUnitGradedNatTrans.postcompose,
    SSetUnitGradedNatTrans.precompose]
  rw [rightUnitor_inv_naturality_assoc]
  simpa only [tensorHom_def, Category.assoc] using h'

end Enriched

namespace SSetUnitGradedNatTrans

variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
  [CategoryTheory.SimplicialCategory C] [CategoryTheory.SimplicialCategory D]
variable {F G : EnrichedFunctor SSet C D}

/-- The ordinary target morphism represented by one unit-graded component. -/
def componentHom (α : SSetUnitGradedNatTrans F G) (X : C) :
    F.obj X ⟶ G.obj X :=
  (eHomEquiv SSet).symm (α.app X)

@[simp]
theorem eHomEquiv_componentHom
    (α : SSetUnitGradedNatTrans F G) (X : C) :
    eHomEquiv SSet (α.componentHom X) = α.app X :=
  Equiv.apply_symm_apply _ _

theorem postcompose_eq_eHomWhiskerLeft
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    α.postcompose X Y =
      eHomWhiskerLeft SSet (F.obj X) (α.componentHom Y) := by
  simp [postcompose, eHomWhiskerLeft, componentHom]

theorem precompose_eq_map_eHomWhiskerRight
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    α.precompose X Y =
      G.map X Y ≫ eHomWhiskerRight SSet (α.componentHom X) (G.obj Y) := by
  dsimp [precompose, eHomWhiskerRight]
  rw [eHomEquiv_componentHom]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]

@[reassoc]
theorem map_eHomWhiskerLeft_eq_map_eHomWhiskerRight
    (α : SSetUnitGradedNatTrans F G) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (α.componentHom Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (α.componentHom X) (G.obj Y) := by
  rw [← postcompose_eq_eHomWhiskerLeft α X Y,
    map_postcompose_eq_precompose, precompose_eq_map_eHomWhiskerRight]

/-- Construct a strict unit-graded transformation from ordinary component morphisms and
the corresponding full enriched naturality equations. -/
noncomputable def ofComponentHom
    {F G : EnrichedFunctor SSet C D}
    (app : ∀ X : C, F.obj X ⟶ G.obj X)
    (naturality : ∀ X Y : C,
      F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (app Y) =
        G.map X Y ≫ eHomWhiskerRight SSet (app X) (G.obj Y)) :
    SSetUnitGradedNatTrans F G where
  app X := eHomEquiv SSet (app X)
  naturality X Y := by
    dsimp [SSetCentralUnit, Center.tensorUnit]
    simp only [Iso.trans_hom, Iso.symm_hom]
    apply (cancel_epi (λ_ (X ⟶[SSet] Y)).inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have h := naturality X Y
    dsimp [eHomWhiskerLeft, eHomWhiskerRight] at h
    rw [rightUnitor_inv_naturality_assoc] at h
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc] at h
    simpa only [tensorHom_def, Category.assoc] using h

@[simp]
theorem componentHom_ofComponentHom
    {F G : EnrichedFunctor SSet C D}
    (app : ∀ X : C, F.obj X ⟶ G.obj X)
    (naturality : ∀ X Y : C,
      F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (app Y) =
        G.map X Y ≫ eHomWhiskerRight SSet (app X) (G.obj Y))
    (X : C) :
    (ofComponentHom app naturality).componentHom X = app X := by
  apply (eHomEquiv SSet).injective
  simp [ofComponentHom]

/-- Identity strict unit-graded enriched natural transformation. -/
noncomputable def id (F : EnrichedFunctor SSet C D) :
    SSetUnitGradedNatTrans F F :=
  ofComponentHom (fun X ↦ 𝟙 (F.obj X)) (fun X Y ↦ by simp)

@[simp]
theorem componentHom_id (F : EnrichedFunctor SSet C D) (X : C) :
    (id F).componentHom X = 𝟙 (F.obj X) := by
  simp [id]

/-- Vertical composition of strict unit-graded enriched natural transformations. -/
noncomputable def comp
    {F G H : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (β : SSetUnitGradedNatTrans G H) :
    SSetUnitGradedNatTrans F H :=
  ofComponentHom
    (fun X ↦ α.componentHom X ≫ β.componentHom X)
    (fun X Y ↦ by
      calc
        _ = (F.map X Y ≫
              eHomWhiskerLeft SSet (F.obj X) (α.componentHom Y)) ≫
            eHomWhiskerLeft SSet (F.obj X) (β.componentHom Y) := by
          simp only [eHomWhiskerLeft_comp, Category.assoc]
        _ = (G.map X Y ≫
              eHomWhiskerRight SSet (α.componentHom X) (G.obj Y)) ≫
            eHomWhiskerLeft SSet (F.obj X) (β.componentHom Y) :=
          congrArg
            (fun k ↦ k ≫
              eHomWhiskerLeft SSet (F.obj X) (β.componentHom Y))
            (α.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight X Y)
        _ = G.map X Y ≫
            (eHomWhiskerLeft SSet (G.obj X) (β.componentHom Y) ≫
              eHomWhiskerRight SSet (α.componentHom X) (H.obj Y)) := by
          rw [Category.assoc, ← eHom_whisker_exchange]
        _ = (G.map X Y ≫
              eHomWhiskerLeft SSet (G.obj X) (β.componentHom Y)) ≫
            eHomWhiskerRight SSet (α.componentHom X) (H.obj Y) := by
          rw [Category.assoc]
        _ = (H.map X Y ≫
              eHomWhiskerRight SSet (β.componentHom X) (H.obj Y)) ≫
            eHomWhiskerRight SSet (α.componentHom X) (H.obj Y) :=
          congrArg
            (fun k ↦ k ≫
              eHomWhiskerRight SSet (α.componentHom X) (H.obj Y))
            (β.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight X Y)
        _ = H.map X Y ≫
            eHomWhiskerRight SSet
              (α.componentHom X ≫ β.componentHom X) (H.obj Y) := by
          rw [Category.assoc, eHomWhiskerRight_comp])

@[simp]
theorem componentHom_comp
    {F G H : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (β : SSetUnitGradedNatTrans G H) (X : C) :
    (comp α β).componentHom X =
      α.componentHom X ≫ β.componentHom X := by
  simp [comp]

/-- Left unit law for vertical composition. -/
@[simp]
theorem id_comp
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) :
    comp (id F) α = α := by
  apply GradedNatTrans.ext
  funext X
  rw [← eHomEquiv_componentHom (comp (id F) α) X,
    ← eHomEquiv_componentHom α X]
  simp

/-- Right unit law for vertical composition. -/
@[simp]
theorem comp_id
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) :
    comp α (id G) = α := by
  apply GradedNatTrans.ext
  funext X
  rw [← eHomEquiv_componentHom (comp α (id G)) X,
    ← eHomEquiv_componentHom α X]
  simp

/-- Associativity law for vertical composition. -/
@[simp]
theorem assoc
    {F G H K : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (β : SSetUnitGradedNatTrans G H)
    (γ : SSetUnitGradedNatTrans H K) :
    comp (comp α β) γ = comp α (comp β γ) := by
  apply GradedNatTrans.ext
  funext X
  rw [← eHomEquiv_componentHom (comp (comp α β) γ) X,
    ← eHomEquiv_componentHom (comp α (comp β γ)) X]
  simp [Category.assoc]

/-- Precomposition of a strict enriched transformation by an enriched functor. -/
noncomputable def whiskerLeft
    {B : Type x} [Category.{v} B] [CategoryTheory.SimplicialCategory B]
    (L : EnrichedFunctor SSet B C)
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) :
    SSetUnitGradedNatTrans
      (EnrichedFunctor.comp SSet L F) (EnrichedFunctor.comp SSet L G) :=
  ofComponentHom
    (fun X ↦ α.componentHom (L.obj X))
    (fun X Y ↦ by
      change L.map X Y ≫
          (F.map (L.obj X) (L.obj Y) ≫
            eHomWhiskerLeft SSet (F.obj (L.obj X))
              (α.componentHom (L.obj Y))) =
        L.map X Y ≫
          (G.map (L.obj X) (L.obj Y) ≫
            eHomWhiskerRight SSet (α.componentHom (L.obj X))
              (G.obj (L.obj Y)))
      exact congrArg (fun k ↦ L.map X Y ≫ k)
        (α.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight (L.obj X) (L.obj Y)))

@[simp]
theorem componentHom_whiskerLeft
    {B : Type x} [Category.{v} B] [CategoryTheory.SimplicialCategory B]
    (L : EnrichedFunctor SSet B C)
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G) (X : B) :
    (whiskerLeft L α).componentHom X = α.componentHom (L.obj X) := by
  simp [whiskerLeft]

/-- Postcomposition of a strict enriched transformation by an enriched functor. -/
noncomputable def whiskerRight
    {E : Type x} [Category.{v} E] [CategoryTheory.SimplicialCategory E]
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    SSetUnitGradedNatTrans
      (EnrichedFunctor.comp SSet F R) (EnrichedFunctor.comp SSet G R) where
  app X := α.app X ≫ R.map (F.obj X) (G.obj X)
  naturality X Y := by
    change (SSetCentralUnit.2.β (X ⟶[SSet] Y)).hom ≫
        ((F.map X Y ≫ R.map (F.obj X) (F.obj Y)) ⊗ₘ
          (α.app Y ≫ R.map (F.obj Y) (G.obj Y))) ≫
          eComp SSet (R.obj (F.obj X)) (R.obj (F.obj Y)) (R.obj (G.obj Y)) =
      ((α.app X ≫ R.map (F.obj X) (G.obj X)) ⊗ₘ
        (G.map X Y ≫ R.map (G.obj X) (G.obj Y))) ≫
          eComp SSet (R.obj (F.obj X)) (R.obj (G.obj X)) (R.obj (G.obj Y))
    have h := congrArg
      (fun k ↦ k ≫ R.map (F.obj X) (G.obj Y)) (α.naturality X Y)
    simpa only [EnrichedFunctor.comp_map, Category.assoc,
      ← tensorHom_comp_tensorHom, R.map_comp] using h

end SSetUnitGradedNatTrans

variable {E H : Type v} [Category.{v} E] [Category.{v} H]
  [CategoryTheory.SimplicialCategory E] [CategoryTheory.SimplicialCategory H]

/-- An enriched functor induces a map of homotopy coherent nerves by postcomposition. -/
def simplicialNerveMap (F : EnrichedFunctor SSet E H) :
    CategoryTheory.SimplicialNerve E ⟶ CategoryTheory.SimplicialNerve H where
  app _ := ↾fun σ ↦ CategoryTheory.EnrichedFunctor.comp SSet σ F
  naturality _ _ _ := rfl

/-- The two-object simplicial thickening used as the coherent interval. -/
abbrev CoherentInterval : Type v :=
  CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 2))

/-- The identity functor of the coherent interval, regarded as its distinguished `1`-simplex. -/
def coherentIntervalSimplex :
    (CategoryTheory.SimplicialNerve CoherentInterval).obj
      (op (SimplexCategory.mk 1)) :=
  CategoryTheory.EnrichedFunctor.id SSet CoherentInterval

/-- The canonical simplex map from the standard `1`-simplex to the coherent interval nerve. -/
def coherentIntervalEdge :
    (Δ[1] : SSet.{v}) ⟶ CategoryTheory.SimplicialNerve CoherentInterval :=
  SSet.yonedaEquiv.symm coherentIntervalSimplex

variable (E : Type v) [Category.{v} E] [CategoryTheory.SimplicialCategory E]

/-- Insert the coherent interval into the nerve of the pointwise enriched product. -/
def simplicialNerveCylinderInclusion :
    CategoryTheory.SimplicialNerve E ⊗ (Δ[1] : SSet.{v}) ⟶
      CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct E CoherentInterval) :=
  (𝟙 _ ⊗ₘ coherentIntervalEdge) ≫
    simplicialNerveProductHom E CoherentInterval

end LeanLCAExactChallenge.Infinity
