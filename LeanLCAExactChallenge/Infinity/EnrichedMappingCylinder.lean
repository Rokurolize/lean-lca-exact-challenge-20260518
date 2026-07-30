/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedNaturalTransformationHomotopy
import LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
import LeanLCAExactChallenge.Infinity.Localization

/-! # Mapping cylinders for enriched natural transformations

A strict unit-graded natural transformation between simplicially enriched functors determines
an enriched functor on the product with the coherent interval. Its coherent nerve is an
all-dimensional simplicial homotopy, and transposition gives the corresponding QCat `2`-cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

variable {C D : Type v} [Category.{v} C] [Category.{v} D]
  [CategoryTheory.SimplicialCategory C] [CategoryTheory.SimplicialCategory D]

namespace SSetUnitGradedNatTrans

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

end SSetUnitGradedNatTrans

/-- The object type of a coherent mapping cylinder over `C`. -/
abbrev CoherentCylinderSource :=
  SimplicialEnrichedProduct C CoherentInterval

namespace EnrichedMappingCylinder

abbrev intervalZero : CoherentInterval.{v} :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

abbrev intervalOne : CoherentInterval.{v} :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 1)

theorem intervalOne_not_le_intervalZero :
    ¬ intervalOne.as ≤ intervalZero.as := by decide

/-- Embed an object at the lower endpoint of the coherent cylinder. -/
def atZero (X : C) : CoherentCylinderSource (C := C) :=
  (X, intervalZero)

/-- Embed an object at the upper endpoint of the coherent cylinder. -/
def atOne (X : C) : CoherentCylinderSource (C := C) :=
  (X, intervalOne)

omit [Category.{v} C] [CategoryTheory.SimplicialCategory C] in
@[simp]
theorem atZero_fst (X : C) : (atZero X).1 = X := rfl

omit [Category.{v} C] [CategoryTheory.SimplicialCategory C] in
@[simp]
theorem atOne_fst (X : C) : (atOne X).1 = X := rfl

variable (F G : EnrichedFunctor SSet C D)

/-- The lower endpoint functor on the pointwise enriched product. -/
def lowerFunctor : EnrichedFunctor SSet (CoherentCylinderSource (C := C)) D :=
  EnrichedFunctor.comp SSet
    (SimplicialEnrichedProduct.fst C CoherentInterval) F

/-- The upper endpoint functor on the pointwise enriched product. -/
def upperFunctor : EnrichedFunctor SSet (CoherentCylinderSource (C := C)) D :=
  EnrichedFunctor.comp SSet
    (SimplicialEnrichedProduct.fst C CoherentInterval) G

variable (α : SSetUnitGradedNatTrans F G)

/-- Objects of the mapping cylinder are selected by the interval endpoint. -/
def obj (X : CoherentCylinderSource (C := C)) : D :=
  Fin.cases (F.obj X.1) (fun _ ↦ G.obj X.1) X.2.as.down

/-- The cross-endpoint hom map of the mapping cylinder. -/
def crossMap (X Y : CoherentCylinderSource (C := C)) :
    (X ⟶[SSet] Y) ⟶ (F.obj X.1 ⟶[SSet] G.obj Y.1) :=
  (lowerFunctor F).map X Y ≫
    eHomWhiskerLeft SSet (F.obj X.1) (α.componentHom Y.1)

/-- Naturality rewrites the cross map into its upper-endpoint form. -/
theorem crossMap_eq_upper (X Y : CoherentCylinderSource (C := C)) :
    crossMap F G α X Y =
      (upperFunctor G).map X Y ≫
        eHomWhiskerRight SSet (α.componentHom X.1) (G.obj Y.1) := by
  dsimp [crossMap, lowerFunctor, upperFunctor]
  rw [EnrichedFunctor.comp_map, EnrichedFunctor.comp_map]
  change
    (SimplicialEnrichedProduct.fst C CoherentInterval).map X Y ≫
        (F.map X.1 Y.1 ≫
          eHomWhiskerLeft SSet (F.obj X.1) (α.componentHom Y.1)) =
      (SimplicialEnrichedProduct.fst C CoherentInterval).map X Y ≫
        (G.map X.1 Y.1 ≫
          eHomWhiskerRight SSet (α.componentHom X.1) (G.obj Y.1))
  exact congrArg
    (fun k ↦ (SimplicialEnrichedProduct.fst C CoherentInterval).map X Y ≫ k)
    (α.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight X.1 Y.1)

/-- The impossible reversed-endpoint hom map. -/
def reversedMap (X Y : CoherentCylinderSource (C := C))
    (h : ¬ X.2.as ≤ Y.2.as) :
    (X ⟶[SSet] Y) ⟶ (G.obj X.1 ⟶[SSet] F.obj Y.1) :=
  CartesianMonoidalCategory.snd _ _ ≫
    CoherentNervePathFiltration.Path.mapFromNerveThickPathOfNotLE h _

/-- The hom-object map in the four endpoint cases. -/
def map (X Y : CoherentCylinderSource (C := C)) :
    (X ⟶[SSet] Y) ⟶ (obj F G X ⟶[SSet] obj F G Y) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · exact (lowerFunctor F).map
        (X, CategoryTheory.SimplicialThickening.mk (ULift.up 0))
        (Y, CategoryTheory.SimplicialThickening.mk (ULift.up 0))
    · exact crossMap F G α
        (X, CategoryTheory.SimplicialThickening.mk (ULift.up 0))
        (Y, CategoryTheory.SimplicialThickening.mk (ULift.up j'.succ))
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · exact reversedMap F G
        (X, CategoryTheory.SimplicialThickening.mk (ULift.up i'.succ))
        (Y, CategoryTheory.SimplicialThickening.mk (ULift.up 0)) (by
          change ¬ i'.succ ≤ (0 : Fin 2)
          intro h
          exact Fin.succ_ne_zero i' (le_antisymm h (Fin.zero_le _)))
    · exact (upperFunctor G).map
        (X, CategoryTheory.SimplicialThickening.mk (ULift.up i'.succ))
        (Y, CategoryTheory.SimplicialThickening.mk (ULift.up j'.succ))

@[simp]
theorem map_zero_zero (X Y : C) :
    map F G α (atZero X) (atZero Y) =
      (lowerFunctor F).map (atZero X) (atZero Y) := rfl

@[simp]
theorem map_zero_one (X Y : C) :
    map F G α (atZero X) (atOne Y) =
      crossMap F G α (atZero X) (atOne Y) := rfl

@[simp]
theorem map_one_one (X Y : C) :
    map F G α (atOne X) (atOne Y) =
      (upperFunctor G).map (atOne X) (atOne Y) := rfl

/-- A simplex in an interval hom-object witnesses the endpoint order. -/
theorem false_of_hom_not_le
    {X Y : CoherentCylinderSource (C := C)}
    (h : ¬ X.2.as ≤ Y.2.as) {U : SimplexCategoryᵒᵖ}
    (x : (X ⟶[SSet] Y).obj U) : False := by
  exact h (CategoryTheory.SimplicialThickening.Path.le (x.2.obj 0))

/-- A tensor of two consecutive hom-objects is empty if its first interval step decreases. -/
theorem false_of_composable_hom_not_le_left
    {X Y Z : CoherentCylinderSource (C := C)}
    (h : ¬ X.2.as ≤ Y.2.as) {U : SimplexCategoryᵒᵖ}
    (x : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj U) : False :=
  false_of_hom_not_le h x.1

/-- A tensor of two consecutive hom-objects is empty if its second interval step decreases. -/
theorem false_of_composable_hom_not_le_right
    {X Y Z : CoherentCylinderSource (C := C)}
    (h : ¬ Y.2.as ≤ Z.2.as) {U : SimplexCategoryᵒᵖ}
    (x : ((X ⟶[SSet] Y) ⊗ (Y ⟶[SSet] Z)).obj U) : False :=
  false_of_hom_not_le h x.2

/-- The mapping-cylinder hom map preserves enriched identities. -/
theorem map_id (X : CoherentCylinderSource (C := C)) :
    eId SSet X ≫ map F G α X X = eId SSet (obj F G X) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · exact (lowerFunctor F).map_id
      (X, CategoryTheory.SimplicialThickening.mk (ULift.up 0))
  · exact (upperFunctor G).map_id
      (X, CategoryTheory.SimplicialThickening.mk (ULift.up i'.succ))

theorem map_comp_zero_zero_zero (X Y Z : C) :
    eComp (C := CoherentCylinderSource (C := C)) SSet
        (atZero X) (atZero Y) (atZero Z) ≫
        map F G α (atZero X) (atZero Z) =
      (map F G α (atZero X) (atZero Y) ⊗ₘ
          map F G α (atZero Y) (atZero Z)) ≫
        eComp SSet (obj F G (atZero X))
          (obj F G (atZero Y)) (obj F G (atZero Z)) := by
  exact (lowerFunctor F).map_comp
    (atZero X) (atZero Y) (atZero Z)

theorem map_comp_one_one_one (X Y Z : C) :
    eComp (C := CoherentCylinderSource (C := C)) SSet
        (atOne X) (atOne Y) (atOne Z) ≫
        map F G α (atOne X) (atOne Z) =
      (map F G α (atOne X) (atOne Y) ⊗ₘ
          map F G α (atOne Y) (atOne Z)) ≫
        eComp SSet (obj F G (atOne X))
          (obj F G (atOne Y)) (obj F G (atOne Z)) := by
  exact (upperFunctor G).map_comp
    (atOne X) (atOne Y) (atOne Z)

theorem map_comp_zero_zero_one (X Y Z : C) :
    eComp (C := CoherentCylinderSource (C := C)) SSet
        (atZero X) (atZero Y) (atOne Z) ≫
        map F G α (atZero X) (atOne Z) =
      (map F G α (atZero X) (atZero Y) ⊗ₘ
          map F G α (atZero Y) (atOne Z)) ≫
        eComp SSet (obj F G (atZero X))
          (obj F G (atZero Y)) (obj F G (atOne Z)) := by
  rw [map_zero_one, map_zero_zero, map_zero_one]
  dsimp [crossMap]
  rw [(lowerFunctor F).map_comp_assoc]
  change
    ((lowerFunctor F).map (atZero X) (atZero Y) ⊗ₘ
        (lowerFunctor F).map (atZero Y) (atOne Z)) ≫
        eComp SSet (F.obj X) (F.obj Y) (F.obj Z) ≫
          eHomWhiskerLeft SSet (F.obj X) (α.componentHom Z) =
      ((lowerFunctor F).map (atZero X) (atZero Y) ⊗ₘ
          (lowerFunctor F).map (atZero Y) (atOne Z) ≫
            eHomWhiskerLeft SSet (F.obj Y) (α.componentHom Z)) ≫
        eComp SSet (F.obj X) (F.obj Y) (G.obj Z)
  rw [eComp_eHomWhiskerLeft]
  rw [← Category.assoc]
  congr 1

theorem map_comp_zero_one_one (X Y Z : C) :
    eComp (C := CoherentCylinderSource (C := C)) SSet
        (atZero X) (atOne Y) (atOne Z) ≫
        map F G α (atZero X) (atOne Z) =
      (map F G α (atZero X) (atOne Y) ⊗ₘ
          map F G α (atOne Y) (atOne Z)) ≫
        eComp SSet (obj F G (atZero X))
          (obj F G (atOne Y)) (obj F G (atOne Z)) := by
  rw [map_zero_one, map_zero_one, map_one_one]
  rw [crossMap_eq_upper, crossMap_eq_upper]
  rw [(upperFunctor G).map_comp_assoc]
  change
    ((upperFunctor G).map (atZero X) (atOne Y) ⊗ₘ
        (upperFunctor G).map (atOne Y) (atOne Z)) ≫
        eComp SSet (G.obj X) (G.obj Y) (G.obj Z) ≫
          eHomWhiskerRight SSet (α.componentHom X) (G.obj Z) =
      ((upperFunctor G).map (atZero X) (atOne Y) ≫
          eHomWhiskerRight SSet (α.componentHom X) (G.obj Y) ⊗ₘ
        (upperFunctor G).map (atOne Y) (atOne Z)) ≫
        eComp SSet (F.obj X) (G.obj Y) (G.obj Z)
  rw [eComp_eHomWhiskerRight]
  rw [← Category.assoc]
  congr 1

/-- The mapping-cylinder hom map preserves enriched composition in all endpoint cases. -/
theorem map_comp (X Y Z : CoherentCylinderSource (C := C)) :
    eComp SSet X Y Z ≫ map F G α X Z =
      (map F G α X Y ⊗ₘ map F G α Y Z) ≫
        eComp SSet (obj F G X) (obj F G Y) (obj F G Z) := by
  rcases X with ⟨X, ⟨⟨i⟩⟩⟩
  rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
  rcases Z with ⟨Z, ⟨⟨k⟩⟩⟩
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · refine Fin.cases ?_ (fun k' ↦ ?_) k
      · simpa [atZero] using map_comp_zero_zero_zero F G α X Y Z
      · have hk : k' = 0 := Subsingleton.elim _ _
        subst k'
        simpa [atZero, atOne] using map_comp_zero_zero_one F G α X Y Z
    · have hj : j' = 0 := Subsingleton.elim _ _
      subst j'
      refine Fin.cases ?_ (fun k' ↦ ?_) k
      · ext U x
        exact (false_of_composable_hom_not_le_right
          (X := atZero X) (Y := atOne Y) (Z := atZero Z)
          intervalOne_not_le_intervalZero.{v} x).elim
      · have hk : k' = 0 := Subsingleton.elim _ _
        subst k'
        simpa [atZero, atOne] using map_comp_zero_one_one F G α X Y Z
  · have hi : i' = 0 := Subsingleton.elim _ _
    subst i'
    refine Fin.cases ?_ (fun j' ↦ ?_) j
    · refine Fin.cases ?_ (fun k' ↦ ?_) k
      · ext U x
        exact (false_of_composable_hom_not_le_left
          (X := atOne X) (Y := atZero Y) (Z := atZero Z)
          intervalOne_not_le_intervalZero.{v} x).elim
      · have hk : k' = 0 := Subsingleton.elim _ _
        subst k'
        ext U x
        exact (false_of_composable_hom_not_le_left
          (X := atOne X) (Y := atZero Y) (Z := atOne Z)
          intervalOne_not_le_intervalZero.{v} x).elim
    · have hj : j' = 0 := Subsingleton.elim _ _
      subst j'
      refine Fin.cases ?_ (fun k' ↦ ?_) k
      · ext U x
        exact (false_of_composable_hom_not_le_right
          (X := atOne X) (Y := atOne Y) (Z := atZero Z)
          intervalOne_not_le_intervalZero.{v} x).elim
      · have hk : k' = 0 := Subsingleton.elim _ _
        subst k'
        simpa [atOne] using map_comp_one_one_one F G α X Y Z

/-- The enriched mapping-cylinder functor associated to a strict unit-graded transformation. -/
noncomputable def functor :
    EnrichedFunctor SSet (CoherentCylinderSource (C := C)) D where
  obj := EnrichedMappingCylinder.obj F G
  map := EnrichedMappingCylinder.map F G α
  map_id := EnrichedMappingCylinder.map_id F G α
  map_comp := EnrichedMappingCylinder.map_comp F G α

/-- The all-dimensional coherent-nerve homotopy represented by the mapping cylinder. -/
def coherentNerveHomotopy :
    CategoryTheory.SimplicialNerve C ⊗ (Δ[1] : SSet.{v}) ⟶
      CategoryTheory.SimplicialNerve D :=
  simplicialNerveCylinderInclusion C ≫
    simplicialNerveMap (functor F G α)

/-- The lower vertex of the standard interval, with the tensor unit as source. -/
def standardIntervalZero :
    𝟙_ SSet.{v} ⟶ (Δ[1] : SSet.{v}) :=
  SSet.const (SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2)))

/-- The upper vertex of the standard interval, with the tensor unit as source. -/
def standardIntervalOne :
    𝟙_ SSet.{v} ⟶ (Δ[1] : SSet.{v}) :=
  SSet.const (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2)))

/-- The lower endpoint of the coherent homotopy is the coherent-nerve map induced by `F`. -/
theorem coherentNerveHomotopy_zero :
    (ρ_ (CategoryTheory.SimplicialNerve C)).inv ≫
        (CategoryTheory.SimplicialNerve C ◁
          standardIntervalZero) ≫
        coherentNerveHomotopy F G α =
      simplicialNerveMap F := by
  rfl

/-- The upper endpoint of the coherent homotopy is the coherent-nerve map induced by `G`. -/
theorem coherentNerveHomotopy_one :
    (ρ_ (CategoryTheory.SimplicialNerve C)).inv ≫
        (CategoryTheory.SimplicialNerve C ◁
          standardIntervalOne) ≫
        coherentNerveHomotopy F G α =
      simplicialNerveMap G := by
  rfl

/-- The coherent homotopy transposed to the internal Hom of coherent nerves. -/
def coherentNerveHomotopyAdjoint :
    (Δ[1] : SSet.{v}) ⟶
      (ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D) :=
  CategoryTheory.MonoidalClosed.curry (coherentNerveHomotopy F G α)

/-- The internal-Hom vertex represented by an enriched functor on coherent nerves. -/
def coherentNerveMapVertex (H : EnrichedFunctor SSet C D) :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
      (CategoryTheory.SimplicialNerve D)) _⦋0⦌ :=
  SSet.unitHomEquiv _
    (CategoryTheory.MonoidalClosed.curry' (simplicialNerveMap H))

theorem internalHomVertexMap_injective
    (X Y : SSet.{v}) : Function.Injective (internalHomVertexMap X Y) := by
  intro a b h
  apply (SSet.unitHomEquiv ((ihom X).obj Y)).symm.injective
  apply CategoryTheory.MonoidalClosed.uncurry'_injective
  exact h

/-- The `1`-simplex in the coherent-nerve functor internal Hom represented by `α`. -/
def coherentNerveHomotopySimplex :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
      (CategoryTheory.SimplicialNerve D)) _⦋1⦌ :=
  SSet.yonedaEquiv (coherentNerveHomotopyAdjoint F G α)

theorem coherentNerveHomotopySimplex_delta_one :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D)).δ 1
        (coherentNerveHomotopySimplex F G α) =
      coherentNerveMapVertex F := by
  apply internalHomVertexMap_injective
  exact coherentNerveHomotopy_zero F G α

theorem coherentNerveHomotopySimplex_delta_zero :
    ((ihom (CategoryTheory.SimplicialNerve C)).obj
        (CategoryTheory.SimplicialNerve D)).δ 0
        (coherentNerveHomotopySimplex F G α) =
      coherentNerveMapVertex G := by
  apply internalHomVertexMap_injective
  exact coherentNerveHomotopy_one F G α

/-- The coherent-nerve internal-Hom edge represented by `α`. -/
def coherentNerveHomotopyEdge :
    SSet.Edge (coherentNerveMapVertex F) (coherentNerveMapVertex G) :=
  SSet.Edge.mk (coherentNerveHomotopySimplex F G α)
    (coherentNerveHomotopySimplex_delta_one F G α)
    (coherentNerveHomotopySimplex_delta_zero F G α)

/-- A homotopy coherent nerve bundled with a supplied quasicategory proof. -/
def coherentNerveQCat
    (E : Type v) [Category.{v} E] [CategoryTheory.SimplicialCategory E]
    (hE : SSet.Quasicategory (CategoryTheory.SimplicialNerve E)) :
    SSet.QCat.{v} :=
  ⟨CategoryTheory.SimplicialNerve E, hE⟩

/-- An enriched functor bundled as a map of coherent-nerve quasicategories. -/
def coherentNerveQCatMap
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D))
    (H : EnrichedFunctor SSet C D) :
    coherentNerveQCat C hC ⟶ coherentNerveQCat D hD :=
  ObjectProperty.homMk (simplicialNerveMap H)

/-- A strict unit-graded enriched transformation determines a QCat `2`-cell. -/
noncomputable def coherentNerveTwoCell
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D)) :
    @Quiver.Hom
      (coherentNerveQCat C hC ⟶ coherentNerveQCat D hD)
      (SSet.QCat.bicategory.homCategory
        (coherentNerveQCat C hC) (coherentNerveQCat D hD)).toQuiver
      (coherentNerveQCatMap hC hD F)
      (coherentNerveQCatMap hC hD G) :=
  CategoryTheory.CatEnrichedOrdinary.Hom.mk
    (edgeHomotopyClass (coherentNerveHomotopyEdge F G α))

end EnrichedMappingCylinder

end LeanLCAExactChallenge.Infinity
