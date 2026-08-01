/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedMappingCylinder

/-! # Functoriality of enriched mapping cylinders

This module constructs the coherent triangle associated to two composable strict
unit-graded enriched natural transformations. Its three all-dimensional faces are the
mapping cylinders of the two transformations and their vertical composite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.tacticCheckInstances false

noncomputable section

universe v

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

variable {C D : Type v} [Category.{v} C] [Category.{v} D]
  [CategoryTheory.SimplicialCategory C] [CategoryTheory.SimplicialCategory D]

namespace EnrichedMappingCylinder

/-- The coherent three-vertex simplex used to witness vertical composition. -/
abbrev CoherentTriangle : Type v :=
  CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))

/-- The source of a coherent mapping triangle. -/
abbrev CoherentTriangleSource :=
  SimplicialEnrichedProduct C CoherentTriangle

abbrev triangleZero : CoherentTriangle.{v} :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

abbrev triangleOne : CoherentTriangle.{v} :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 1)

abbrev triangleTwo : CoherentTriangle.{v} :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 2)

/-- The row functor on a coherent mapping triangle. -/
def triangleRowFunctor (F : EnrichedFunctor SSet C D) :
    EnrichedFunctor SSet (CoherentTriangleSource (C := C)) D :=
  EnrichedFunctor.comp SSet
    (SimplicialEnrichedProduct.fst C CoherentTriangle) F

/-- The cross-row Hom map associated to one strict enriched transformation. -/
def triangleCrossMap
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (X Y : CoherentTriangleSource (C := C)) :
    (X ⟶[SSet] Y) ⟶ (F.obj X.1 ⟶[SSet] G.obj Y.1) :=
  (triangleRowFunctor F).map X Y ≫
    eHomWhiskerLeft SSet (F.obj X.1) (α.componentHom Y.1)

/-- Naturality rewrites a triangle cross map into its upper-row form. -/
theorem triangleCrossMap_eq_upper
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (X Y : CoherentTriangleSource (C := C)) :
    triangleCrossMap α X Y =
      (triangleRowFunctor G).map X Y ≫
        eHomWhiskerRight SSet (α.componentHom X.1) (G.obj Y.1) := by
  dsimp [triangleCrossMap, triangleRowFunctor]
  rw [EnrichedFunctor.comp_map, EnrichedFunctor.comp_map]
  change
    (SimplicialEnrichedProduct.fst C CoherentTriangle).map X Y ≫
        (F.map X.1 Y.1 ≫
          eHomWhiskerLeft SSet (F.obj X.1) (α.componentHom Y.1)) =
      (SimplicialEnrichedProduct.fst C CoherentTriangle).map X Y ≫
        (G.map X.1 Y.1 ≫
          eHomWhiskerRight SSet (α.componentHom X.1) (G.obj Y.1))
  exact congrArg
    (fun k ↦ (SimplicialEnrichedProduct.fst C CoherentTriangle).map X Y ≫ k)
    (α.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight X.1 Y.1)

/-- The impossible decreasing-row Hom map. -/
def triangleReversedMap
    {F G : EnrichedFunctor SSet C D}
    (X Y : CoherentTriangleSource (C := C))
    (h : ¬ X.2.as ≤ Y.2.as) :
    (X ⟶[SSet] Y) ⟶ (G.obj X.1 ⟶[SSet] F.obj Y.1) :=
  CartesianMonoidalCategory.snd _ _ ≫
    CoherentNervePathFiltration.Path.mapFromNerveThickPathOfNotLE h _

variable {F G H : EnrichedFunctor SSet C D}
  (α : SSetUnitGradedNatTrans F G)
  (β : SSetUnitGradedNatTrans G H)

/-- Objects of the coherent mapping triangle are selected by its three rows. -/
def triangleObj
    (F G H : EnrichedFunctor SSet C D)
    (X : CoherentTriangleSource (C := C)) : D :=
  Fin.cases (F.obj X.1)
    (fun i ↦ Fin.cases (G.obj X.1) (fun _ ↦ H.obj X.1) i) X.2.as.down

/-- The Hom map of the coherent mapping triangle in all nine row patterns. -/
def triangleMap (X Y : CoherentTriangleSource (C := C)) :
    (X ⟶[SSet] Y) ⟶
      (triangleObj F G H X ⟶[SSet] triangleObj F G H Y) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · exact (triangleRowFunctor F).map (X, triangleZero) (Y, triangleZero)
    · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
      · exact triangleCrossMap α (X, triangleZero) (Y, triangleOne)
      · have hj : j'' = 0 := Subsingleton.elim _ _
        subst j''
        exact triangleCrossMap (SSetUnitGradedNatTrans.comp α β)
          (X, triangleZero) (Y, triangleTwo)
  · refine Fin.cases ?_ (fun i'' ↦ ?_) i'
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · exact triangleReversedMap (F := F) (G := G)
          (X, triangleOne) (Y, triangleZero) (by
            change ¬ (1 : Fin 3) ≤ 0
            omega)
      · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
        · exact (triangleRowFunctor G).map (X, triangleOne) (Y, triangleOne)
        · have hj : j'' = 0 := Subsingleton.elim _ _
          subst j''
          exact triangleCrossMap β (X, triangleOne) (Y, triangleTwo)
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · have hi : i'' = 0 := Subsingleton.elim _ _
        subst i''
        exact triangleReversedMap (F := F) (G := H)
          (X, triangleTwo) (Y, triangleZero) (by
            change ¬ (2 : Fin 3) ≤ 0
            omega)
      · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
        · have hi : i'' = 0 := Subsingleton.elim _ _
          subst i''
          exact triangleReversedMap (F := G) (G := H)
            (X, triangleTwo) (Y, triangleOne) (by
              change ¬ (2 : Fin 3) ≤ 1
              omega)
        · have hi : i'' = 0 := Subsingleton.elim _ _
          have hj : j'' = 0 := Subsingleton.elim _ _
          subst i''
          subst j''
          exact (triangleRowFunctor H).map (X, triangleTwo) (Y, triangleTwo)

/-- Embed an object in the bottom row of a coherent mapping triangle. -/
def triangleAtZero (X : C) : CoherentTriangleSource (C := C) := (X, triangleZero)

/-- Embed an object in the middle row of a coherent mapping triangle. -/
def triangleAtOne (X : C) : CoherentTriangleSource (C := C) := (X, triangleOne)

/-- Embed an object in the top row of a coherent mapping triangle. -/
def triangleAtTwo (X : C) : CoherentTriangleSource (C := C) := (X, triangleTwo)

@[simp]
theorem triangleMap_zero_zero (X Y : C) :
    triangleMap α β (triangleAtZero X) (triangleAtZero Y) =
      (triangleRowFunctor F).map (triangleAtZero X) (triangleAtZero Y) := rfl

@[simp]
theorem triangleMap_zero_one (X Y : C) :
    triangleMap α β (triangleAtZero X) (triangleAtOne Y) =
      triangleCrossMap α (triangleAtZero X) (triangleAtOne Y) := rfl

@[simp]
theorem triangleMap_zero_two (X Y : C) :
    triangleMap α β (triangleAtZero X) (triangleAtTwo Y) =
      triangleCrossMap (SSetUnitGradedNatTrans.comp α β)
        (triangleAtZero X) (triangleAtTwo Y) := rfl

@[simp]
theorem triangleMap_one_one (X Y : C) :
    triangleMap α β (triangleAtOne X) (triangleAtOne Y) =
      (triangleRowFunctor G).map (triangleAtOne X) (triangleAtOne Y) := rfl

@[simp]
theorem triangleMap_one_two (X Y : C) :
    triangleMap α β (triangleAtOne X) (triangleAtTwo Y) =
      triangleCrossMap β (triangleAtOne X) (triangleAtTwo Y) := rfl

@[simp]
theorem triangleMap_two_two (X Y : C) :
    triangleMap α β (triangleAtTwo X) (triangleAtTwo Y) =
      (triangleRowFunctor H).map (triangleAtTwo X) (triangleAtTwo Y) := rfl

/-- The coherent mapping-triangle Hom map preserves enriched identities. -/
theorem triangleMap_id (X : CoherentTriangleSource (C := C)) :
    eId SSet X ≫ triangleMap α β X X =
      eId SSet (triangleObj F G H X) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · exact (triangleRowFunctor F).map_id (X, triangleZero)
  · refine Fin.cases ?_ (fun i'' ↦ ?_) i'
    · exact (triangleRowFunctor G).map_id (X, triangleOne)
    · have hi : i'' = 0 := Subsingleton.elim _ _
      subst i''
      exact (triangleRowFunctor H).map_id (X, triangleTwo)

/-- Composition inside the lower row followed by a cross-row map. -/
theorem triangleCrossMap_comp_left
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (X Y Z : CoherentTriangleSource (C := C)) :
    eComp SSet X Y Z ≫ triangleCrossMap α X Z =
      ((triangleRowFunctor F).map X Y ⊗ₘ triangleCrossMap α Y Z) ≫
        eComp SSet (F.obj X.1) (F.obj Y.1) (G.obj Z.1) := by
  rcases X with ⟨X, i⟩
  rcases Y with ⟨Y, j⟩
  rcases Z with ⟨Z, k⟩
  dsimp [triangleCrossMap]
  rw [(triangleRowFunctor F).map_comp_assoc]
  change
    (((triangleRowFunctor F).map (X, i) (Y, j) ⊗ₘ
        (triangleRowFunctor F).map (Y, j) (Z, k)) ≫
        eComp SSet (F.obj X) (F.obj Y) (F.obj Z)) ≫
          eHomWhiskerLeft SSet (F.obj X) (α.componentHom Z) =
      ((triangleRowFunctor F).map (X, i) (Y, j) ⊗ₘ
          ((triangleRowFunctor F).map (Y, j) (Z, k) ≫
            eHomWhiskerLeft SSet (F.obj Y) (α.componentHom Z))) ≫
        eComp SSet (F.obj X) (F.obj Y) (G.obj Z)
  have h := congrArg
    (fun q ↦
      ((triangleRowFunctor F).map (X, i) (Y, j) ⊗ₘ
        (triangleRowFunctor F).map (Y, j) (Z, k)) ≫ q)
    (eComp_eHomWhiskerLeft SSet
      (F.obj X) (F.obj Y) (α.componentHom Z))
  simpa only [triangleRowFunctor, EnrichedFunctor.comp, SimplicialEnrichedProduct.fst,
    Category.assoc, tensorHom_def, Category.comp_id,
    MonoidalCategory.whiskerLeft_comp] using h

/-- A cross-row map followed by composition inside the upper row. -/
theorem triangleCrossMap_comp_right
    {F G : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (X Y Z : CoherentTriangleSource (C := C)) :
    eComp SSet X Y Z ≫ triangleCrossMap α X Z =
      (triangleCrossMap α X Y ⊗ₘ (triangleRowFunctor G).map Y Z) ≫
        eComp SSet (F.obj X.1) (G.obj Y.1) (G.obj Z.1) := by
  rcases X with ⟨X, i⟩
  rcases Y with ⟨Y, j⟩
  rcases Z with ⟨Z, k⟩
  rw [triangleCrossMap_eq_upper]
  rw [triangleCrossMap_eq_upper]
  dsimp [triangleCrossMap, triangleRowFunctor]
  rw [(EnrichedFunctor.comp SSet
    (SimplicialEnrichedProduct.fst C CoherentTriangle) G).map_comp_assoc]
  change
    (((triangleRowFunctor G).map (X, i) (Y, j) ⊗ₘ
        (triangleRowFunctor G).map (Y, j) (Z, k)) ≫
        eComp SSet (G.obj X) (G.obj Y) (G.obj Z)) ≫
          eHomWhiskerRight SSet (α.componentHom X) (G.obj Z) =
      (((triangleRowFunctor G).map (X, i) (Y, j) ≫
          eHomWhiskerRight SSet (α.componentHom X) (G.obj Y)) ⊗ₘ
        (triangleRowFunctor G).map (Y, j) (Z, k)) ≫
        eComp SSet (F.obj X) (G.obj Y) (G.obj Z)
  have h := congrArg
    (fun q ↦
      ((triangleRowFunctor G).map (X, i) (Y, j) ⊗ₘ
        (triangleRowFunctor G).map (Y, j) (Z, k)) ≫ q)
    (eComp_eHomWhiskerRight SSet
      (α.componentHom X) (G.obj Y) (G.obj Z))
  simpa only [triangleRowFunctor, EnrichedFunctor.comp, SimplicialEnrichedProduct.fst,
    Category.assoc, tensorHom_def', Category.comp_id,
    MonoidalCategory.comp_whiskerRight] using h

/-- The all-dimensional cross-row maps compose to the cross-row map of the vertical
composite transformation. -/
theorem triangleCrossMap_comp
    {F G H : EnrichedFunctor SSet C D}
    (α : SSetUnitGradedNatTrans F G)
    (β : SSetUnitGradedNatTrans G H)
    (X Y Z : CoherentTriangleSource (C := C)) :
    eComp SSet X Y Z ≫
        triangleCrossMap (SSetUnitGradedNatTrans.comp α β) X Z =
      (triangleCrossMap α X Y ⊗ₘ triangleCrossMap β Y Z) ≫
        eComp SSet (F.obj X.1) (G.obj Y.1) (H.obj Z.1) := by
  calc
    eComp SSet X Y Z ≫
        triangleCrossMap (SSetUnitGradedNatTrans.comp α β) X Z =
      (eComp SSet X Y Z ≫ triangleCrossMap α X Z) ≫
        eHomWhiskerLeft SSet (F.obj X.1) (β.componentHom Z.1) := by
          have hw := eHomWhiskerLeft_comp SSet (F.obj X.1)
            (α.componentHom Z.1) (β.componentHom Z.1)
          have hp := congrArg
            (fun q ↦
              (eComp SSet X Y Z ≫ (triangleRowFunctor F).map X Z) ≫ q)
            hw
          have hc := congrArg
            (fun q ↦ eComp SSet X Y Z ≫
              (triangleRowFunctor F).map X Z ≫
                eHomWhiskerLeft SSet (F.obj X.1) q)
            (SSetUnitGradedNatTrans.componentHom_comp α β Z.1)
          exact hc.trans ((Category.assoc
              (eComp SSet X Y Z) ((triangleRowFunctor F).map X Z)
              (eHomWhiskerLeft SSet (F.obj X.1)
                (α.componentHom Z.1 ≫ β.componentHom Z.1))).symm.trans
            (hp.trans (congrArg
              (fun q ↦ q ≫
                eHomWhiskerLeft SSet (F.obj X.1) (β.componentHom Z.1))
              (Category.assoc (eComp SSet X Y Z)
                ((triangleRowFunctor F).map X Z)
                (eHomWhiskerLeft SSet (F.obj X.1)
                  (α.componentHom Z.1))))))
    _ = ((triangleCrossMap α X Y ⊗ₘ
            (triangleRowFunctor G).map Y Z) ≫
          eComp SSet (F.obj X.1) (G.obj Y.1) (G.obj Z.1)) ≫
        eHomWhiskerLeft SSet (F.obj X.1) (β.componentHom Z.1) := by
          rw [triangleCrossMap_comp_right α]
    _ = (triangleCrossMap α X Y ⊗ₘ
          triangleCrossMap β Y Z) ≫
        eComp SSet (F.obj X.1) (G.obj Y.1) (H.obj Z.1) := by
          let t :=
            triangleCrossMap α X Y ⊗ₘ (triangleRowFunctor G).map Y Z
          let w :=
            eHomWhiskerLeft SSet (G.obj Y.1) (β.componentHom Z.1)
          let c :=
            eComp SSet (F.obj X.1) (G.obj Y.1) (G.obj Z.1)
          let c' :=
            eComp SSet (F.obj X.1) (G.obj Y.1) (H.obj Z.1)
          have hβ := congrArg (fun q ↦ t ≫ q)
            (eComp_eHomWhiskerLeft SSet
              (F.obj X.1) (G.obj Y.1) (β.componentHom Z.1))
          have ht :
              t ≫ ((F.obj X.1 ⟶[SSet] G.obj Y.1) ◁ w) =
                triangleCrossMap α X Y ⊗ₘ triangleCrossMap β Y Z := by
            calc
              t ≫ ((F.obj X.1 ⟶[SSet] G.obj Y.1) ◁ w) =
                  t ≫ (𝟙 (F.obj X.1 ⟶[SSet] G.obj Y.1) ⊗ₘ w) :=
                congrArg (fun q ↦ t ≫ q)
                  (id_tensorHom (F.obj X.1 ⟶[SSet] G.obj Y.1) w).symm
              _ = (triangleCrossMap α X Y ≫
                    𝟙 (F.obj X.1 ⟶[SSet] G.obj Y.1)) ⊗ₘ
                  ((triangleRowFunctor G).map Y Z ≫ w) :=
                tensorHom_comp_tensorHom _ _ _ _
              _ = triangleCrossMap α X Y ⊗ₘ triangleCrossMap β Y Z := by
                dsimp [w, triangleCrossMap]
                rw [Category.comp_id]
          exact (Category.assoc t c
              (eHomWhiskerLeft SSet (F.obj X.1) (β.componentHom Z.1))).trans
            (hβ.trans ((Category.assoc t
              ((F.obj X.1 ⟶[SSet] G.obj Y.1) ◁ w) c').symm.trans
                (congrArg (fun q ↦ q ≫ c') ht)))

/-- A simplex in a coherent-triangle Hom object forces its row to increase. -/
theorem triangleFalseOfHomNotLE
    {X Y : CoherentTriangleSource (C := C)}
    (h : ¬ X.2.as ≤ Y.2.as) {U : SimplexCategoryᵒᵖ}
    (x : (X ⟶[SSet] Y).obj U) : False :=
  h (CategoryTheory.SimplicialThickening.Path.le (x.2.obj 0))

/-- A composable pair is empty when its first triangle-row step decreases. -/
theorem triangleFalseOfComposableHomNotLELeft
    {X Y Z : CoherentTriangleSource (C := C)}
    (h : ¬ X.2.as ≤ Y.2.as) {U : SimplexCategoryᵒᵖ}
    (x : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj U) : False :=
  triangleFalseOfHomNotLE h x.1

/-- A composable pair is empty when its second triangle-row step decreases. -/
theorem triangleFalseOfComposableHomNotLERight
    {X Y Z : CoherentTriangleSource (C := C)}
    (h : ¬ Y.2.as ≤ Z.2.as) {U : SimplexCategoryᵒᵖ}
    (x : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj U) : False :=
  triangleFalseOfHomNotLE h x.2

/-- The coherent mapping-triangle Hom map preserves composition in every row pattern. -/
theorem triangleMap_comp (X Y Z : CoherentTriangleSource (C := C)) :
    eComp SSet X Y Z ≫ triangleMap α β X Z =
      (triangleMap α β X Y ⊗ₘ triangleMap α β Y Z) ≫
        eComp SSet (triangleObj F G H X)
          (triangleObj F G H Y) (triangleObj F G H Z) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
  rcases Z with ⟨Z, ⟨⟨k⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · refine Fin.cases ?_ (fun k' ↦ ?_) k
      · exact (triangleRowFunctor F).map_comp
          (triangleAtZero X) (triangleAtZero Y) (triangleAtZero Z)
      · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
        · exact triangleCrossMap_comp_left α
            (triangleAtZero X) (triangleAtZero Y) (triangleAtOne Z)
        · have hk : k'' = 0 := Subsingleton.elim _ _
          subst k''
          exact triangleCrossMap_comp_left
            (SSetUnitGradedNatTrans.comp α β)
            (triangleAtZero X) (triangleAtZero Y) (triangleAtTwo Z)
    · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
      · refine Fin.cases ?_ (fun k' ↦ ?_) k
        · ext U x
          exact (triangleFalseOfComposableHomNotLERight
            (X := triangleAtZero X) (Y := triangleAtOne Y)
            (Z := triangleAtZero Z) (by
              change ¬ (1 : Fin 3) ≤ 0
              omega) x).elim
        · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
          · exact triangleCrossMap_comp_right α
              (triangleAtZero X) (triangleAtOne Y) (triangleAtOne Z)
          · have hk : k'' = 0 := Subsingleton.elim _ _
            subst k''
            exact triangleCrossMap_comp α β
              (triangleAtZero X) (triangleAtOne Y) (triangleAtTwo Z)
      · have hj : j'' = 0 := Subsingleton.elim _ _
        subst j''
        refine Fin.cases ?_ (fun k' ↦ ?_) k
        · ext U x
          exact (triangleFalseOfComposableHomNotLERight
            (X := triangleAtZero X) (Y := triangleAtTwo Y)
            (Z := triangleAtZero Z) (by
              change ¬ (2 : Fin 3) ≤ 0
              omega) x).elim
        · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
          · ext U x
            exact (triangleFalseOfComposableHomNotLERight
              (X := triangleAtZero X) (Y := triangleAtTwo Y)
              (Z := triangleAtOne Z) (by
                change ¬ (2 : Fin 3) ≤ 1
                omega) x).elim
          · have hk : k'' = 0 := Subsingleton.elim _ _
            subst k''
            exact triangleCrossMap_comp_right
              (SSetUnitGradedNatTrans.comp α β)
              (triangleAtZero X) (triangleAtTwo Y) (triangleAtTwo Z)
  · refine Fin.cases ?_ (fun i'' ↦ ?_) i'
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · ext U x
        exact (triangleFalseOfComposableHomNotLELeft
          (X := triangleAtOne X) (Y := triangleAtZero Y)
          (Z := (Z, CategoryTheory.SimplicialThickening.mk (ULift.up k))) (by
            change ¬ (1 : Fin 3) ≤ 0
            omega) x).elim
      · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
        · refine Fin.cases ?_ (fun k' ↦ ?_) k
          · ext U x
            exact (triangleFalseOfComposableHomNotLERight
              (X := triangleAtOne X) (Y := triangleAtOne Y)
              (Z := triangleAtZero Z) (by
                change ¬ (1 : Fin 3) ≤ 0
                omega) x).elim
          · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
            · exact (triangleRowFunctor G).map_comp
                (triangleAtOne X) (triangleAtOne Y) (triangleAtOne Z)
            · have hk : k'' = 0 := Subsingleton.elim _ _
              subst k''
              exact triangleCrossMap_comp_left β
                (triangleAtOne X) (triangleAtOne Y) (triangleAtTwo Z)
        · have hj : j'' = 0 := Subsingleton.elim _ _
          subst j''
          refine Fin.cases ?_ (fun k' ↦ ?_) k
          · ext U x
            exact (triangleFalseOfComposableHomNotLERight
              (X := triangleAtOne X) (Y := triangleAtTwo Y)
              (Z := triangleAtZero Z) (by
                change ¬ (2 : Fin 3) ≤ 0
                omega) x).elim
          · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
            · ext U x
              exact (triangleFalseOfComposableHomNotLERight
                (X := triangleAtOne X) (Y := triangleAtTwo Y)
                (Z := triangleAtOne Z) (by
                  change ¬ (2 : Fin 3) ≤ 1
                  omega) x).elim
            · have hk : k'' = 0 := Subsingleton.elim _ _
              subst k''
              exact triangleCrossMap_comp_right β
                (triangleAtOne X) (triangleAtTwo Y) (triangleAtTwo Z)
    · have hi : i'' = 0 := Subsingleton.elim _ _
      subst i''
      refine Fin.cases ?_ (fun j' ↦ ?_) j
      · ext U x
        exact (triangleFalseOfComposableHomNotLELeft
          (X := triangleAtTwo X) (Y := triangleAtZero Y)
          (Z := (Z, CategoryTheory.SimplicialThickening.mk (ULift.up k))) (by
            change ¬ (2 : Fin 3) ≤ 0
            omega) x).elim
      · refine Fin.cases ?_ (fun j'' ↦ ?_) j'
        · ext U x
          exact (triangleFalseOfComposableHomNotLELeft
            (X := triangleAtTwo X) (Y := triangleAtOne Y)
            (Z := (Z, CategoryTheory.SimplicialThickening.mk (ULift.up k))) (by
              change ¬ (2 : Fin 3) ≤ 1
              omega) x).elim
        · have hj : j'' = 0 := Subsingleton.elim _ _
          subst j''
          refine Fin.cases ?_ (fun k' ↦ ?_) k
          · ext U x
            exact (triangleFalseOfComposableHomNotLERight
              (X := triangleAtTwo X) (Y := triangleAtTwo Y)
              (Z := triangleAtZero Z) (by
                change ¬ (2 : Fin 3) ≤ 0
                omega) x).elim
          · refine Fin.cases ?_ (fun k'' ↦ ?_) k'
            · ext U x
              exact (triangleFalseOfComposableHomNotLERight
                (X := triangleAtTwo X) (Y := triangleAtTwo Y)
                (Z := triangleAtOne Z) (by
                  change ¬ (2 : Fin 3) ≤ 1
                  omega) x).elim
            · have hk : k'' = 0 := Subsingleton.elim _ _
              subst k''
              exact (triangleRowFunctor H).map_comp
                (triangleAtTwo X) (triangleAtTwo Y) (triangleAtTwo Z)

/-- The enriched functor whose coherent nerve is the all-dimensional vertical-composition
triangle. -/
noncomputable def triangleFunctor :
    EnrichedFunctor SSet (CoherentTriangleSource (C := C)) D where
  obj := triangleObj F G H
  map := triangleMap α β
  map_id := triangleMap_id α β
  map_comp := triangleMap_comp α β

/-- A face inclusion of the coherent interval into the coherent triangle. -/
def triangleFaceFunctor (i : Fin 3) :
    EnrichedFunctor SSet CoherentInterval CoherentTriangle :=
  CategoryTheory.SimplicialThickening.functor
    (SimplexCategory.δ i).toOrderHom.uliftMap

/-- Apply a coherent-triangle face inclusion in the second product factor. -/
def triangleFaceProductFunctor (i : Fin 3) :
    EnrichedFunctor SSet
      (CoherentCylinderSource (C := C)) (CoherentTriangleSource (C := C)) :=
  SimplicialEnrichedProduct.pair C CoherentTriangle
    (SimplicialEnrichedProduct.fst C CoherentInterval)
    (EnrichedFunctor.comp SSet
      (SimplicialEnrichedProduct.snd C CoherentInterval)
      (triangleFaceFunctor i))

/-- The coherent-nerve map induced by a triangle product face. -/
def simplicialNerveTriangleFaceMap (i : Fin 3) :
    CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct C CoherentInterval) ⟶
      CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct C CoherentTriangle) where
  app _ := ↾fun σ ↦
    EnrichedFunctor.comp SSet σ (triangleFaceProductFunctor (C := C) i)
  naturality _ _ _ := rfl

/-- Restriction to the face opposite vertex `2` is the mapping cylinder of `α`. -/
theorem triangleFunctor_delta_two :
    EnrichedFunctor.comp SSet (triangleFaceProductFunctor (C := C) 2)
        (triangleFunctor α β) =
      functor F G α := by
  apply EnrichedFunctor.ext SSet (fun X ↦ by
    rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    fin_cases i <;> rfl
  )
  rintro ⟨X, ⟨⟨i⟩⟩⟩ ⟨Y, ⟨⟨j⟩⟩⟩
  fin_cases i <;> fin_cases j
  all_goals rfl

/-- Restriction to the face opposite vertex `0` is the mapping cylinder of `β`. -/
theorem triangleFunctor_delta_zero :
    EnrichedFunctor.comp SSet (triangleFaceProductFunctor (C := C) 0)
        (triangleFunctor α β) =
      functor G H β := by
  apply EnrichedFunctor.ext SSet (fun X ↦ by
    rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    fin_cases i <;> rfl
  )
  rintro ⟨X, ⟨⟨i⟩⟩⟩ ⟨Y, ⟨⟨j⟩⟩⟩
  fin_cases i <;> fin_cases j
  all_goals rfl

/-- Restriction to the face opposite vertex `1` is the mapping cylinder of the
vertical composite. -/
theorem triangleFunctor_delta_one :
    EnrichedFunctor.comp SSet (triangleFaceProductFunctor (C := C) 1)
        (triangleFunctor α β) =
      functor F H (SSetUnitGradedNatTrans.comp α β) := by
  apply EnrichedFunctor.ext SSet (fun X ↦ by
    rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    fin_cases i <;> rfl
  )
  rintro ⟨X, ⟨⟨i⟩⟩⟩ ⟨Y, ⟨⟨j⟩⟩⟩
  fin_cases i <;> fin_cases j
  all_goals rfl

/-- The identity functor of the coherent triangle, regarded as its distinguished
`2`-simplex. -/
def coherentTriangleSimplex :
    (CategoryTheory.SimplicialNerve CoherentTriangle).obj
      (op (SimplexCategory.mk 2)) :=
  CategoryTheory.EnrichedFunctor.id SSet CoherentTriangle

/-- The standard `2`-simplex mapped to the nerve of the coherent triangle. -/
def coherentTriangleMap :
    (Δ[2] : SSet.{v}) ⟶ CategoryTheory.SimplicialNerve CoherentTriangle :=
  SSet.yonedaEquiv.symm coherentTriangleSimplex

/-- Each standard face of the coherent triangle is the coherent interval followed by
the corresponding enriched face functor. -/
theorem coherentTriangleMap_face (i : Fin 3) :
    SSet.stdSimplex.δ i ≫ coherentTriangleMap =
      coherentIntervalEdge ≫ simplicialNerveMap (triangleFaceFunctor i) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  dsimp [coherentTriangleMap, coherentIntervalEdge, coherentTriangleSimplex,
    coherentIntervalSimplex, simplicialNerveMap]
  rw [show SSet.stdSimplex.δ i =
      SSet.stdSimplex.map (SimplexCategory.δ i) by rfl,
    SSet.yonedaEquiv_map,
    SSet.yonedaEquiv_symm_app_objEquiv_symm]
  rw [Equiv.apply_symm_apply]
  change EnrichedFunctor.comp SSet (triangleFaceFunctor i)
      (EnrichedFunctor.id SSet CoherentTriangle) =
    EnrichedFunctor.comp SSet (EnrichedFunctor.id SSet CoherentInterval)
      (triangleFaceFunctor i)
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [triangleFaceFunctor]

/-- Insert the coherent triangle into the nerve of the pointwise enriched product. -/
def simplicialNerveTriangleInclusion (C : Type v)
    [Category.{v} C] [CategoryTheory.SimplicialCategory C] :
    CategoryTheory.SimplicialNerve C ⊗ (Δ[2] : SSet.{v}) ⟶
      CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct C CoherentTriangle) :=
  (𝟙 _ ⊗ₘ coherentTriangleMap) ≫
    simplicialNerveProductHom C CoherentTriangle

/-- Restricting the triangle product inclusion to a face gives the cylinder product
inclusion followed by the corresponding product face functor. -/
theorem simplicialNerveTriangleInclusion_face (i : Fin 3) :
    (CategoryTheory.SimplicialNerve C ◁ SSet.stdSimplex.δ i) ≫
        simplicialNerveTriangleInclusion C =
      simplicialNerveCylinderInclusion C ≫
        simplicialNerveTriangleFaceMap (C := C) i := by
  rw [simplicialNerveTriangleInclusion, simplicialNerveCylinderInclusion]
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  have hs0 := congrArg
    (fun t : (Δ[1] : SSet.{v}) ⟶
        CategoryTheory.SimplicialNerve CoherentTriangle ↦ t.app U)
    (coherentTriangleMap_face i)
  have hs := ConcreteCategory.congr_hom hs0 s
  have hs' :
      coherentTriangleMap.app U ((SSet.stdSimplex.δ i).app U s) =
        (simplicialNerveMap (triangleFaceFunctor i)).app U
          (coherentIntervalEdge.app U s) := by
    change coherentTriangleMap.app U ((SSet.stdSimplex.δ i).app U s) =
      (simplicialNerveMap (triangleFaceFunctor i)).app U
        (coherentIntervalEdge.app U s) at hs
    exact hs
  change
    SimplicialEnrichedProduct.pair C CoherentTriangle σ
        (coherentTriangleMap.app U
          ((SSet.stdSimplex.δ i).app U s)) =
      EnrichedFunctor.comp SSet
        (SimplicialEnrichedProduct.pair C CoherentInterval σ
          (coherentIntervalEdge.app U s))
        (triangleFaceProductFunctor (C := C) i)
  rw [hs']
  exact (SimplicialEnrichedProduct.pair_projections C CoherentTriangle _).symm

/-- The all-dimensional coherent-nerve triangle for two vertically composable strict
enriched transformations. -/
def coherentNerveTriangle :
    CategoryTheory.SimplicialNerve C ⊗ (Δ[2] : SSet.{v}) ⟶
      CategoryTheory.SimplicialNerve D :=
  simplicialNerveTriangleInclusion C ≫
    simplicialNerveMap (triangleFunctor α β)

/-- The face opposite vertex `2` of the all-dimensional nerve triangle is the
homotopy represented by `α`. -/
theorem coherentNerveTriangle_delta_two :
    (CategoryTheory.SimplicialNerve C ◁
        SSet.stdSimplex.δ (2 : Fin 3)) ≫ coherentNerveTriangle α β =
      coherentNerveHomotopy F G α := by
  rw [coherentNerveTriangle, coherentNerveHomotopy, ← Category.assoc,
    simplicialNerveTriangleInclusion_face, Category.assoc]
  change simplicialNerveCylinderInclusion C ≫
      simplicialNerveMap
        (EnrichedFunctor.comp SSet
          (triangleFaceProductFunctor (C := C) 2) (triangleFunctor α β)) =
    _
  rw [triangleFunctor_delta_two]

/-- The face opposite vertex `0` is the homotopy represented by `β`. -/
theorem coherentNerveTriangle_delta_zero :
    (CategoryTheory.SimplicialNerve C ◁
        SSet.stdSimplex.δ (0 : Fin 3)) ≫ coherentNerveTriangle α β =
      coherentNerveHomotopy G H β := by
  rw [coherentNerveTriangle, coherentNerveHomotopy, ← Category.assoc,
    simplicialNerveTriangleInclusion_face, Category.assoc]
  change simplicialNerveCylinderInclusion C ≫
      simplicialNerveMap
        (EnrichedFunctor.comp SSet
          (triangleFaceProductFunctor (C := C) 0) (triangleFunctor α β)) =
    _
  rw [triangleFunctor_delta_zero]

/-- The face opposite vertex `1` is the homotopy represented by the vertical
composite. -/
theorem coherentNerveTriangle_delta_one :
    (CategoryTheory.SimplicialNerve C ◁
        SSet.stdSimplex.δ (1 : Fin 3)) ≫ coherentNerveTriangle α β =
      coherentNerveHomotopy F H (SSetUnitGradedNatTrans.comp α β) := by
  rw [coherentNerveTriangle, coherentNerveHomotopy, ← Category.assoc,
    simplicialNerveTriangleInclusion_face, Category.assoc]
  change simplicialNerveCylinderInclusion C ≫
      simplicialNerveMap
        (EnrichedFunctor.comp SSet
          (triangleFaceProductFunctor (C := C) 1) (triangleFunctor α β)) =
    _
  rw [triangleFunctor_delta_one]

/-- The coherent-nerve triangle transposed into the functor internal Hom. -/
def coherentNerveTriangleAdjoint :
    (Δ[2] : SSet.{v}) ⟶
      (ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D) :=
  CategoryTheory.MonoidalClosed.curry (coherentNerveTriangle α β)

/-- The internal-Hom `2`-simplex witnessing vertical composition. -/
def coherentNerveTriangleSimplex :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
      (CategoryTheory.SimplicialNerve D)) _⦋2⦌ :=
  SSet.yonedaEquiv (coherentNerveTriangleAdjoint α β)

theorem coherentNerveTriangleSimplex_delta_two :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D)).δ 2
        (coherentNerveTriangleSimplex α β) =
      coherentNerveHomotopySimplex F G α := by
  apply SSet.yonedaEquiv.symm.injective
  change SSet.stdSimplex.δ (2 : Fin 3) ≫
      coherentNerveTriangleAdjoint α β =
    coherentNerveHomotopyAdjoint F G α
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  rw [CategoryTheory.MonoidalClosed.uncurry_natural_left]
  dsimp only [coherentNerveTriangleAdjoint, coherentNerveHomotopyAdjoint]
  rw [CategoryTheory.MonoidalClosed.uncurry_curry,
    CategoryTheory.MonoidalClosed.uncurry_curry]
  exact coherentNerveTriangle_delta_two α β

theorem coherentNerveTriangleSimplex_delta_zero :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D)).δ 0
        (coherentNerveTriangleSimplex α β) =
      coherentNerveHomotopySimplex G H β := by
  apply SSet.yonedaEquiv.symm.injective
  change SSet.stdSimplex.δ (0 : Fin 3) ≫
      coherentNerveTriangleAdjoint α β =
    coherentNerveHomotopyAdjoint G H β
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  rw [CategoryTheory.MonoidalClosed.uncurry_natural_left]
  dsimp only [coherentNerveTriangleAdjoint, coherentNerveHomotopyAdjoint]
  rw [CategoryTheory.MonoidalClosed.uncurry_curry,
    CategoryTheory.MonoidalClosed.uncurry_curry]
  exact coherentNerveTriangle_delta_zero α β

theorem coherentNerveTriangleSimplex_delta_one :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D)).δ 1
        (coherentNerveTriangleSimplex α β) =
      coherentNerveHomotopySimplex F H
        (SSetUnitGradedNatTrans.comp α β) := by
  apply SSet.yonedaEquiv.symm.injective
  change SSet.stdSimplex.δ (1 : Fin 3) ≫
      coherentNerveTriangleAdjoint α β =
    coherentNerveHomotopyAdjoint F H
      (SSetUnitGradedNatTrans.comp α β)
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  rw [CategoryTheory.MonoidalClosed.uncurry_natural_left]
  dsimp only [coherentNerveTriangleAdjoint, coherentNerveHomotopyAdjoint]
  rw [CategoryTheory.MonoidalClosed.uncurry_curry,
    CategoryTheory.MonoidalClosed.uncurry_curry]
  exact coherentNerveTriangle_delta_one α β

/-- The coherent triangle records vertical composition of the three internal-Hom edges. -/
def coherentNerveTriangleCompStruct :
    SSet.Edge.CompStruct
      (coherentNerveHomotopyEdge F G α)
      (coherentNerveHomotopyEdge G H β)
      (coherentNerveHomotopyEdge F H
        (SSetUnitGradedNatTrans.comp α β)) :=
  SSet.Edge.CompStruct.mk (coherentNerveTriangleSimplex α β)
    (coherentNerveTriangleSimplex_delta_two α β)
    (coherentNerveTriangleSimplex_delta_zero α β)
    (coherentNerveTriangleSimplex_delta_one α β)

/-- The all-dimensional QCat `2`-cell construction preserves vertical composition. -/
theorem coherentNerveTwoCell_comp
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D)) :
    coherentNerveTwoCell F G α hC hD ≫
        coherentNerveTwoCell G H β hC hD =
      coherentNerveTwoCell F H
        (SSetUnitGradedNatTrans.comp α β) hC hD := by
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  exact SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (coherentNerveTriangleCompStruct α β).toTruncated

/-- The cross-row map of the identity transformation is the underlying row map. -/
theorem crossMap_id (F : EnrichedFunctor SSet C D)
    (X Y : CoherentCylinderSource (C := C)) :
    crossMap F F (SSetUnitGradedNatTrans.id F) X Y =
      (lowerFunctor F).map X Y := by
  dsimp [crossMap]
  rw [SSetUnitGradedNatTrans.componentHom_id]
  change (lowerFunctor F).map X Y ≫
      eHomWhiskerLeft SSet ((lowerFunctor F).obj X)
        (𝟙 ((lowerFunctor F).obj Y)) =
    (lowerFunctor F).map X Y
  rw [eHomWhiskerLeft_id, Category.comp_id]

/-- The mapping cylinder of the identity transformation forgets the interval factor. -/
theorem functor_id (F : EnrichedFunctor SSet C D) :
    functor F F (SSetUnitGradedNatTrans.id F) = lowerFunctor F := by
  refine EnrichedFunctor.ext SSet (fun X ↦ ?_) (fun X Y ↦ ?_)
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · rfl
    · have hi : i' = 0 := Subsingleton.elim _ _
      subst i'
      rfl
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · rfl
      · have hj : j' = 0 := Subsingleton.elim _ _
        subst j'
        change crossMap F F (SSetUnitGradedNatTrans.id F)
            (atZero X) (atOne Y) ≫ eqToHom _ =
          (lowerFunctor F).map (atZero X) (atOne Y)
        rw [crossMap_id]
        simp
    · have hi : i' = 0 := Subsingleton.elim _ _
      subst i'
      refine Fin.cases ?_ (fun j' ↦ ?_) j
      · ext U x
        exact (false_of_hom_not_le
          (X := atOne X) (Y := atZero Y)
          intervalOne_not_le_intervalZero.{v} x).elim
      · have hj : j' = 0 := Subsingleton.elim _ _
        subst j'
        rfl

/-- The all-dimensional homotopy of the identity transformation is constant in the interval. -/
theorem coherentNerveHomotopy_id (F : EnrichedFunctor SSet C D) :
    coherentNerveHomotopy F F (SSetUnitGradedNatTrans.id F) =
      CartesianMonoidalCategory.fst
          (CategoryTheory.SimplicialNerve C) (Δ[1] : SSet.{v}) ≫
        simplicialNerveMap F := by
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  change EnrichedFunctor.comp SSet
      (SimplicialEnrichedProduct.pair C CoherentInterval σ
        (coherentIntervalEdge.app U s))
      (functor F F (SSetUnitGradedNatTrans.id F)) =
    EnrichedFunctor.comp SSet σ F
  rw [functor_id]
  change EnrichedFunctor.comp SSet
      (EnrichedFunctor.comp SSet
        (SimplicialEnrichedProduct.pair C CoherentInterval σ
          (coherentIntervalEdge.app U s))
        (SimplicialEnrichedProduct.fst C CoherentInterval)) F =
    EnrichedFunctor.comp SSet σ F
  rw [SimplicialEnrichedProduct.pair_fst]

/-- The transposed identity homotopy is the constant internal-Hom simplex. -/
theorem coherentNerveHomotopyAdjoint_id (F : EnrichedFunctor SSet C D) :
    coherentNerveHomotopyAdjoint F F (SSetUnitGradedNatTrans.id F) =
      SSet.const (coherentNerveMapVertex F) := by
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  dsimp only [coherentNerveHomotopyAdjoint]
  rw [CategoryTheory.MonoidalClosed.uncurry_curry]
  rw [coherentNerveHomotopy_id]
  unfold coherentNerveMapVertex
  rw [CategoryTheory.MonoidalClosed.uncurry_eq]
  ext U x
  rfl

private theorem yonedaEquiv_const_one {Q : SSet.{v}} (z : Q _⦋0⦌) :
    SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{v}) ⟶ Q) =
      (SSet.Edge.id z).edge := by
  change Q.map (⦋1⦌.const ⦋0⦌ 0).op z = Q.map (SimplexCategory.σ 0).op z
  have h : ⦋1⦌.const ⦋0⦌ 0 = SimplexCategory.σ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl
  rw [h]

/-- The internal-Hom simplex of the identity transformation is degenerate. -/
theorem coherentNerveHomotopySimplex_id (F : EnrichedFunctor SSet C D) :
    coherentNerveHomotopySimplex F F (SSetUnitGradedNatTrans.id F) =
      (SSet.Edge.id (coherentNerveMapVertex F)).edge := by
  unfold coherentNerveHomotopySimplex
  rw [coherentNerveHomotopyAdjoint_id, yonedaEquiv_const_one]

/-- The internal-Hom edge of the identity transformation is the identity edge. -/
theorem coherentNerveHomotopyEdge_id (F : EnrichedFunctor SSet C D) :
    coherentNerveHomotopyEdge F F (SSetUnitGradedNatTrans.id F) =
      SSet.Edge.id (coherentNerveMapVertex F) := by
  apply SSet.Edge.ext
  exact coherentNerveHomotopySimplex_id F

/-- The all-dimensional QCat `2`-cell construction preserves identities. -/
theorem coherentNerveTwoCell_id
    (F : EnrichedFunctor SSet C D)
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D)) :
    coherentNerveTwoCell F F (SSetUnitGradedNatTrans.id F) hC hD =
      𝟙 (coherentNerveQCatMap hC hD F) := by
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  change edgeHomotopyClass
      (coherentNerveHomotopyEdge F F (SSetUnitGradedNatTrans.id F)) =
    𝟙 (homotopyObject (coherentNerveMapVertex F))
  rw [coherentNerveHomotopyEdge_id]
  exact SSet.Truncated.HomotopyCategory.homMk_id _

end EnrichedMappingCylinder

end LeanLCAExactChallenge.Infinity
