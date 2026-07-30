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

universe u v

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

variable {C D : Type u}
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
