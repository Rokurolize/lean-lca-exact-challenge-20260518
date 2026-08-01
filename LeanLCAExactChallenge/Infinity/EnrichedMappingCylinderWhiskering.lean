/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedMappingCylinderFunctoriality
import LeanLCAExactChallenge.Infinity.QCatEnrichedWhiskering

/-! # Whiskering coherent-nerve mapping cylinders

Strict enriched whiskering is compatible with the all-dimensional coherent-nerve homotopies and
their internal-Hom edges.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open Opposite Simplicial
open scoped MonoidalCategory Simplicial Bicategory

variable {C D : Type v} [Category.{v} C] [Category.{v} D]
  [CategoryTheory.SimplicialCategory C] [CategoryTheory.SimplicialCategory D]

namespace EnrichedMappingCylinder

theorem simplicialNerveMap_comp
    {A B E : Type v} [Category.{v} A] [Category.{v} B] [Category.{v} E]
    [CategoryTheory.SimplicialCategory A]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory E]
    (F : EnrichedFunctor SSet A B) (G : EnrichedFunctor SSet B E) :
    simplicialNerveMap (EnrichedFunctor.comp SSet F G) =
      simplicialNerveMap F ≫ simplicialNerveMap G := by
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro σ
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [simplicialNerveMap, EnrichedFunctor.comp]

/-- Composition of enriched functors is carried to composition of the induced coherent-nerve
maps of quasicategories. -/
theorem coherentNerveQCatMap_comp
    {A B E : Type v} [Category.{v} A] [Category.{v} B] [Category.{v} E]
    [CategoryTheory.SimplicialCategory A]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory E]
    (hA : SSet.Quasicategory (CategoryTheory.SimplicialNerve A))
    (hB : SSet.Quasicategory (CategoryTheory.SimplicialNerve B))
    (hE : SSet.Quasicategory (CategoryTheory.SimplicialNerve E))
    (F : EnrichedFunctor SSet A B) (G : EnrichedFunctor SSet B E) :
    coherentNerveQCatMap hA hE (EnrichedFunctor.comp SSet F G) =
      coherentNerveQCatMap hA hB F ≫ coherentNerveQCatMap hB hE G := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact simplicialNerveMap_comp F G

def cylinderWhiskerLeftFunctor
    {B C : Type v} [Category.{v} B] [Category.{v} C]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    (L : EnrichedFunctor SSet B C) :
    EnrichedFunctor SSet
      (CoherentCylinderSource (C := B)) (CoherentCylinderSource (C := C)) :=
  SimplicialEnrichedProduct.pair C CoherentInterval
    (EnrichedFunctor.comp SSet
      (SimplicialEnrichedProduct.fst B CoherentInterval) L)
    (SimplicialEnrichedProduct.snd B CoherentInterval)

theorem functor_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    functor (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) =
      EnrichedFunctor.comp SSet (cylinderWhiskerLeftFunctor L)
        (functor F G α) := by
  refine EnrichedFunctor.ext SSet (fun X ↦ ?_) (fun X Y ↦ ?_)
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    fin_cases i <;> rfl
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
    fin_cases i <;> fin_cases j
    · rfl
    · ext U x
      rcases x with ⟨xB, xI⟩
      dsimp [functor, map, crossMap, lowerFunctor,
        cylinderWhiskerLeftFunctor,
        SSetUnitGradedNatTrans.whiskerLeft,
        SSetUnitGradedNatTrans.ofComponentHom,
        SSetUnitGradedNatTrans.componentHom,
        SimplicialEnrichedProduct.pair,
        SimplicialEnrichedProduct.fst,
        SimplicialEnrichedProduct.snd]
      simp only [Fin.isValue, EnrichedFunctor.comp_map,
        Equiv.symm_apply_apply, Category.assoc, NatTrans.comp_app,
        comp_apply]
      rfl
    · ext U x
      exact (false_of_hom_not_le
        (X := atOne X) (Y := atZero Y)
        intervalOne_not_le_intervalZero.{v} x).elim
    · rfl

/-- The coherent-nerve map induced by changing the first cylinder factor. -/
def simplicialNerveCylinderWhiskerLeftMap
    {B C : Type v} [Category.{v} B] [Category.{v} C]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    (L : EnrichedFunctor SSet B C) :
    CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct B CoherentInterval) ⟶
      CategoryTheory.SimplicialNerve
        (SimplicialCategoryProduct C CoherentInterval) where
  app _ := ↾fun σ ↦
    EnrichedFunctor.comp SSet σ (cylinderWhiskerLeftFunctor L)
  naturality _ _ _ := rfl

theorem simplicialNerveCylinderWhiskerLeftMap_comp
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    simplicialNerveCylinderWhiskerLeftMap L ≫
        simplicialNerveMap (functor F G α) =
      simplicialNerveMap
        (EnrichedFunctor.comp SSet (cylinderWhiskerLeftFunctor L)
          (functor F G α)) := by
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro σ
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

theorem simplicialNerveCylinderInclusion_naturality
    {B C : Type v} [Category.{v} B] [Category.{v} C]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    (L : EnrichedFunctor SSet B C) :
    (simplicialNerveMap L ▷ (Δ[1] : SSet.{v})) ≫
        simplicialNerveCylinderInclusion C =
      simplicialNerveCylinderInclusion B ≫
        simplicialNerveCylinderWhiskerLeftMap L := by
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, s⟩
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  rfl

theorem coherentNerveHomotopy_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    coherentNerveHomotopy
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) =
      (simplicialNerveMap L ▷ (Δ[1] : SSet.{v})) ≫
        coherentNerveHomotopy F G α := by
  rw [coherentNerveHomotopy, coherentNerveHomotopy,
    functor_whiskerLeft,
    ← simplicialNerveCylinderWhiskerLeftMap_comp]
  rw [← Category.assoc, ← Category.assoc,
    simplicialNerveCylinderInclusion_naturality]

theorem coherentNerveHomotopyAdjoint_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    coherentNerveHomotopyAdjoint
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) =
      coherentNerveHomotopyAdjoint F G α ≫
        internalHomPrecomp (simplicialNerveMap L)
          (CategoryTheory.SimplicialNerve D) := by
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  unfold internalHomPrecomp
  rw [CategoryTheory.MonoidalClosed.uncurry_pre_app]
  dsimp only [coherentNerveHomotopyAdjoint]
  rw [CategoryTheory.MonoidalClosed.uncurry_curry,
    CategoryTheory.MonoidalClosed.uncurry_curry]
  exact coherentNerveHomotopy_whiskerLeft L F G α

theorem coherentNerveMapVertex_comp
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F : EnrichedFunctor SSet C D) :
    (internalHomPrecomp (simplicialNerveMap L)
        (CategoryTheory.SimplicialNerve D)).app _
        (coherentNerveMapVertex F) =
      coherentNerveMapVertex (EnrichedFunctor.comp SSet L F) := by
  apply internalHomVertexMap_injective
  rw [internalHomVertexMap_precomp]
  unfold coherentNerveMapVertex internalHomVertexMap
  simp only [Equiv.symm_apply_apply,
    CategoryTheory.MonoidalClosed.uncurry'_curry']
  exact (simplicialNerveMap_comp L F).symm

theorem coherentNerveHomotopySimplex_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    coherentNerveHomotopySimplex
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) =
      (internalHomPrecomp (simplicialNerveMap L)
        (CategoryTheory.SimplicialNerve D)).app _
          (coherentNerveHomotopySimplex F G α) := by
  unfold coherentNerveHomotopySimplex
  rw [coherentNerveHomotopyAdjoint_whiskerLeft,
    SSet.yonedaEquiv_comp]

theorem coherentNerveHomotopyEdge_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    coherentNerveHomotopyEdge
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) =
      SSet.Edge.castEndpoints
        (coherentNerveMapVertex_comp L F).symm
        (coherentNerveMapVertex_comp L G).symm
        ((coherentNerveHomotopyEdge F G α).map
          (internalHomPrecomp (simplicialNerveMap L)
            (CategoryTheory.SimplicialNerve D))) := by
  apply SSet.Edge.ext
  simp only [SSet.Edge.castEndpoints_edge, SSet.Edge.map_edge]
  exact coherentNerveHomotopySimplex_whiskerLeft L F G α

/-- The QCat `2`-cell associated to a strict enriched transformation preserves left
whiskering. The heterogeneous equality accounts only for the proved equality between the
coherent-nerve map of a composite enriched functor and the composite coherent-nerve map. -/
theorem coherentNerveTwoCell_whiskerLeft
    {B C D : Type v} [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [CategoryTheory.SimplicialCategory B]
    [CategoryTheory.SimplicialCategory C]
    [CategoryTheory.SimplicialCategory D]
    (hB : SSet.Quasicategory (CategoryTheory.SimplicialNerve B))
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D))
    (L : EnrichedFunctor SSet B C)
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G) :
    HEq (coherentNerveQCatMap hB hC L ◁ coherentNerveTwoCell F G α hC hD)
      (coherentNerveTwoCell
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α) hB hD) := by
  have hF := coherentNerveQCatMap_comp hB hC hD L F
  have hG := coherentNerveQCatMap_comp hB hC hD L G
  cases hF
  cases hG
  apply heq_of_eq
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  apply eq_of_heq
  refine (qcat_base_whiskerLeft_heq
    (coherentNerveQCatMap hB hC L)
    (coherentNerveTwoCell F G α hC hD)).trans ?_
  change HEq
    ((SSet.hoFunctor.map
      (internalHomPrecomp (simplicialNerveMap L)
        (CategoryTheory.SimplicialNerve D))).toFunctor.map
      (edgeHomotopyClass (coherentNerveHomotopyEdge F G α)))
    (edgeHomotopyClass
      (coherentNerveHomotopyEdge
        (EnrichedFunctor.comp SSet L F)
        (EnrichedFunctor.comp SSet L G)
        (SSetUnitGradedNatTrans.whiskerLeft L α)))
  rw [coherentNerveHomotopyEdge_whiskerLeft]
  refine (edgeHomotopyClass_map_heq
    (coherentNerveHomotopyEdge F G α)
    (internalHomPrecomp (simplicialNerveMap L)
      (CategoryTheory.SimplicialNerve D))).trans ?_
  exact (edgeHomotopyClass_castEndpoints_heq
    (coherentNerveMapVertex_comp L F).symm
    (coherentNerveMapVertex_comp L G).symm
    ((coherentNerveHomotopyEdge F G α).map
      (internalHomPrecomp (simplicialNerveMap L)
        (CategoryTheory.SimplicialNerve D)))).symm


section TargetWhiskering

variable {E : Type v} [Category.{v} E] [CategoryTheory.SimplicialCategory E]
variable {F G : EnrichedFunctor SSet C D}

/-- The ordinary morphism represented by applying an enriched functor to a morphism. -/
def targetMapHom (R : EnrichedFunctor SSet D E) {X Y : D} (f : X ⟶ Y) :
    R.obj X ⟶ R.obj Y :=
  (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ R.map X Y)

@[simp]
theorem eHomEquiv_targetMapHom
    (R : EnrichedFunctor SSet D E) {X Y : D} (f : X ⟶ Y) :
    eHomEquiv SSet (targetMapHom R f) = eHomEquiv SSet f ≫ R.map X Y := by
  exact Equiv.apply_symm_apply _ _

@[simp]
theorem componentHom_whiskerRight
    (α : SSetUnitGradedNatTrans F G) (R : EnrichedFunctor SSet D E) (X : C) :
    (SSetUnitGradedNatTrans.whiskerRight α R).componentHom X =
      targetMapHom R (α.componentHom X) := by
  unfold SSetUnitGradedNatTrans.componentHom
  unfold SSetUnitGradedNatTrans.whiskerRight targetMapHom
  simp
  rfl

@[reassoc]
theorem map_eHomWhiskerLeft_targetMapHom
    (R : EnrichedFunctor SSet D E) (X : D) {Y Y' : D} (f : Y ⟶ Y') :
    R.map X Y ≫ eHomWhiskerLeft SSet (R.obj X) (targetMapHom R f) =
      eHomWhiskerLeft SSet X f ≫ R.map X Y' := by
  dsimp [eHomWhiskerLeft]
  rw [eHomEquiv_targetMapHom]
  rw [rightUnitor_inv_naturality_assoc]
  simp only [Category.assoc]
  rw [R.map_comp]
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

theorem crossMap_whiskerRight
    (α : SSetUnitGradedNatTrans F G) (R : EnrichedFunctor SSet D E)
    (X Y : CoherentCylinderSource (C := C)) :
    crossMap (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) X Y =
      crossMap F G α X Y ≫ R.map (F.obj X.1) (G.obj Y.1) := by
  dsimp [crossMap, lowerFunctor]
  rw [componentHom_whiskerRight]
  simp only [EnrichedFunctor.comp_map, Category.assoc]
  change (SimplicialEnrichedProduct.fst C CoherentInterval).map X Y ≫
      F.map X.1 Y.1 ≫ R.map (F.obj X.1) (F.obj Y.1) ≫
        eHomWhiskerLeft SSet (R.obj (F.obj X.1))
          (targetMapHom R (α.componentHom Y.1)) =
    (SimplicialEnrichedProduct.fst C CoherentInterval).map X Y ≫
      F.map X.1 Y.1 ≫ eHomWhiskerLeft SSet (F.obj X.1)
        (α.componentHom Y.1) ≫ R.map (F.obj X.1) (G.obj Y.1)
  rw [map_eHomWhiskerLeft_targetMapHom]


/-- Postcomposition of a mapping cylinder is the cylinder of the postcomposed transformation. -/
theorem functor_whiskerRight
    (F G : EnrichedFunctor SSet C D) (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    functor (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) =
      EnrichedFunctor.comp SSet (functor F G α) R := by
  refine EnrichedFunctor.ext SSet (fun X ↦ ?_) (fun X Y ↦ ?_)
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    fin_cases i <;> rfl
  · rcases X with ⟨X, ⟨⟨i⟩⟩⟩
    rcases Y with ⟨Y, ⟨⟨j⟩⟩⟩
    fin_cases i <;> fin_cases j
    · rfl
    · change crossMap (EnrichedFunctor.comp SSet F R)
          (EnrichedFunctor.comp SSet G R)
          (SSetUnitGradedNatTrans.whiskerRight α R)
          (atZero X) (atOne Y) ≫ eqToHom _ =
        crossMap F G α (atZero X) (atOne Y) ≫
          R.map (F.obj X) (G.obj Y)
      rw [crossMap_whiskerRight]
      simp
    · ext U x
      exact (false_of_hom_not_le
        (X := atOne X) (Y := atZero Y)
        intervalOne_not_le_intervalZero.{v} x).elim
    · rfl


/-- Postcomposition of the all-dimensional homotopy is the homotopy of the postcomposed
transformation. -/
theorem coherentNerveHomotopy_whiskerRight
    (F G : EnrichedFunctor SSet C D) (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    coherentNerveHomotopy (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) =
      coherentNerveHomotopy F G α ≫ simplicialNerveMap R := by
  rw [coherentNerveHomotopy, coherentNerveHomotopy, functor_whiskerRight]
  rw [simplicialNerveMap_comp]
  simp only [Category.assoc]

/-- Transposition turns target whiskering into internal-Hom postcomposition. -/
theorem coherentNerveHomotopyAdjoint_whiskerRight
    (F G : EnrichedFunctor SSet C D) (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    coherentNerveHomotopyAdjoint (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) =
      coherentNerveHomotopyAdjoint F G α ≫
        (ihom (CategoryTheory.SimplicialNerve C)).map (simplicialNerveMap R) := by
  dsimp only [coherentNerveHomotopyAdjoint]
  rw [← CategoryTheory.MonoidalClosed.curry_natural_right]
  exact congrArg CategoryTheory.MonoidalClosed.curry
    (coherentNerveHomotopy_whiskerRight F G α R)

/-- Postcomposition sends the coherent-nerve vertex of a functor to the vertex of its
postcomposition. -/
theorem coherentNerveMapVertex_postcomp
    (F : EnrichedFunctor SSet C D) (R : EnrichedFunctor SSet D E) :
    ((ihom (CategoryTheory.SimplicialNerve C)).map
        (simplicialNerveMap R)).app _ (coherentNerveMapVertex F) =
      coherentNerveMapVertex (EnrichedFunctor.comp SSet F R) := by
  apply internalHomVertexMap_injective
  unfold coherentNerveMapVertex internalHomVertexMap
  simp only [Equiv.symm_apply_apply,
    CategoryTheory.MonoidalClosed.uncurry'_curry']
  exact (simplicialNerveMap_comp F R).symm

/-- The internal-Hom simplex of target whiskering is the postcomposition image of the
original simplex. -/
theorem coherentNerveHomotopySimplex_whiskerRight
    (F G : EnrichedFunctor SSet C D) (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    coherentNerveHomotopySimplex (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) =
      ((ihom (CategoryTheory.SimplicialNerve C)).map
        (simplicialNerveMap R)).app _ (coherentNerveHomotopySimplex F G α) := by
  unfold coherentNerveHomotopySimplex
  rw [coherentNerveHomotopyAdjoint_whiskerRight,
    SSet.yonedaEquiv_comp]

/-- The coherent-nerve edge of target whiskering is the postcomposition image of the
original edge. -/
theorem coherentNerveHomotopyEdge_whiskerRight
    (F G : EnrichedFunctor SSet C D) (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    coherentNerveHomotopyEdge (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) =
      SSet.Edge.castEndpoints
        (coherentNerveMapVertex_postcomp F R).symm
        (coherentNerveMapVertex_postcomp G R).symm
        ((coherentNerveHomotopyEdge F G α).map
          ((ihom (CategoryTheory.SimplicialNerve C)).map
            (simplicialNerveMap R))) := by
  apply SSet.Edge.ext
  simp only [SSet.Edge.castEndpoints_edge, SSet.Edge.map_edge]
  exact coherentNerveHomotopySimplex_whiskerRight F G α R

/-- The QCat `2`-cell associated to a strict enriched transformation preserves right
whiskering. The heterogeneous equality accounts only for the proved equality between the
coherent-nerve map of a composite enriched functor and the composite coherent-nerve map. -/
theorem coherentNerveTwoCell_whiskerRight
    (hC : SSet.Quasicategory (CategoryTheory.SimplicialNerve C))
    (hD : SSet.Quasicategory (CategoryTheory.SimplicialNerve D))
    (hE : SSet.Quasicategory (CategoryTheory.SimplicialNerve E))
    (F G : EnrichedFunctor SSet C D)
    (α : SSetUnitGradedNatTrans F G)
    (R : EnrichedFunctor SSet D E) :
    HEq (coherentNerveTwoCell F G α hC hD ▷ coherentNerveQCatMap hD hE R)
      (coherentNerveTwoCell
        (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R) hC hE) := by
  have hF := coherentNerveQCatMap_comp hC hD hE F R
  have hG := coherentNerveQCatMap_comp hC hD hE G R
  cases hF
  cases hG
  apply heq_of_eq
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  apply eq_of_heq
  refine (qcat_base_whiskerRight_heq
    (coherentNerveTwoCell F G α hC hD)
    (coherentNerveQCatMap hD hE R)).trans ?_
  change HEq
    ((SSet.hoFunctor.map
      ((ihom (CategoryTheory.SimplicialNerve C)).map
        (simplicialNerveMap R))).toFunctor.map
      (edgeHomotopyClass (coherentNerveHomotopyEdge F G α)))
    (edgeHomotopyClass
      (coherentNerveHomotopyEdge
        (EnrichedFunctor.comp SSet F R)
        (EnrichedFunctor.comp SSet G R)
        (SSetUnitGradedNatTrans.whiskerRight α R)))
  rw [coherentNerveHomotopyEdge_whiskerRight]
  refine (edgeHomotopyClass_map_heq
    (coherentNerveHomotopyEdge F G α)
    ((ihom (CategoryTheory.SimplicialNerve C)).map
      (simplicialNerveMap R))).trans ?_
  exact (edgeHomotopyClass_castEndpoints_heq
    (coherentNerveMapVertex_postcomp F R).symm
    (coherentNerveMapVertex_postcomp G R).symm
    ((coherentNerveHomotopyEdge F G α).map
      ((ihom (CategoryTheory.SimplicialNerve C)).map
        (simplicialNerveMap R)))).symm


end TargetWhiskering

end EnrichedMappingCylinder

end LeanLCAExactChallenge.Infinity
