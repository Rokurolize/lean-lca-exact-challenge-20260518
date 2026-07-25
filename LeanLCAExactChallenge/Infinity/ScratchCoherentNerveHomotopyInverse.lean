/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDoldKanHomotopy
import LeanLCAExactChallenge.Infinity.Relative

/-!
# Homotopy inverses in homotopy coherent nerves

A path in one enriched mapping simplicial set from a proposed long edge to the composite of two
adjacent edges determines a coherent triangle. Two such triangles exhibit an edge as an
equivalence in the homotopy coherent nerve.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

namespace LeanLCAExactChallenge.Infinity
namespace CoherentNerveHomotopyInverse

open CategoryTheory
open CategoryTheory.EnrichedCategory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial
open scoped Simplicial

/-- The path category from vertex `0` to vertex `2` in the thickening of `Fin 3`. -/
abbrev TrianglePath : Type v :=
  CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{v, 0} (Fin 3))
    (ULift.up (2 : Fin 3) : ULift.{v, 0} (Fin 3))

/-- The unique possible interior vertex of a path from `0` to `2`. -/
abbrev TriangleInterior : Type v :=
  Set.Ioo
    (ULift.up (0 : Fin 3) : ULift.{v, 0} (Fin 3))
    (ULift.up (2 : Fin 3) : ULift.{v, 0} (Fin 3))

/-- The middle vertex as an element of the open interval from `0` to `2`. -/
def triangleInteriorOne : TriangleInterior.{v} := ⟨ULift.up 1, by decide⟩

instance triangleInteriorSubsingleton : Subsingleton TriangleInterior.{v} :=
  ⟨by
    intro x y
    apply Subtype.ext
    apply ULift.ext
    apply Fin.ext
    have hx := x.property
    have hy := y.property
    change 0 < x.val.down.val ∧ x.val.down.val < 2 at hx
    change 0 < y.val.down.val ∧ y.val.down.val < 2 at hy
    omega⟩

/-- Evaluation at the unique interior vertex identifies its bitvectors with `Fin 2`. -/
def triangleInteriorEvaluationOrderIso :
    (TriangleInterior.{v} → Fin 2) ≃o Fin 2 where
  toFun b := b triangleInteriorOne
  invFun n := fun _ ↦ n
  left_inv b := by
    funext x
    exact congrArg b (Subsingleton.elim triangleInteriorOne x)
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h x
      cases Subsingleton.elim x triangleInteriorOne
      exact h
    · intro h
      exact h triangleInteriorOne

/-- A path from `0` to `2` is determined by whether it contains vertex `1`. -/
noncomputable def trianglePathOrderIso : TrianglePath.{v} ≃o Fin 2 :=
  (CoherentNervePathFiltration.Path.thickPathBitvectorOrderIso
    (i := (ULift.up (0 : Fin 3) : ULift.{v, 0} (Fin 3)))
    (j := (ULift.up (2 : Fin 3) : ULift.{v, 0} (Fin 3))) (by decide)).trans
      triangleInteriorEvaluationOrderIso

/-- The categorical forward map from thick paths to the lifted ordered interval. -/
def trianglePathToFinFunctor : CategoryTheory.Functor TrianglePath.{v} (ULift.{v, 0} (Fin 2)) where
  obj P := ULift.up (trianglePathOrderIso P)
  map {_ _} f := homOfLE (trianglePathOrderIso.monotone f.1.1.1)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The categorical inverse map from the lifted interval to thick paths. -/
def finToTrianglePathFunctor : CategoryTheory.Functor (ULift.{v, 0} (Fin 2)) TrianglePath.{v} where
  obj n := trianglePathOrderIso.symm n.down
  map {x y} f := by
    have hxy : x.down ≤ y.down := by
      change x ≤ y
      exact leOfHom f
    exact ⟨⟨⟨trianglePathOrderIso.symm.monotone hxy⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The two path/interval functors compose to the identity on paths. -/
theorem trianglePathFunctors_comp :
    trianglePathToFinFunctor.{v} ⋙ finToTrianglePathFunctor.{v} =
      CategoryTheory.Functor.id TrianglePath.{v} := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun P ↦ trianglePathOrderIso.left_inv P)
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The two path/interval functors compose to the identity on the lifted interval. -/
theorem finTrianglePathFunctors_comp :
    finToTrianglePathFunctor.{v} ⋙ trianglePathToFinFunctor.{v} =
      CategoryTheory.Functor.id (ULift.{v, 0} (Fin 2)) := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun n ↦ congrArg ULift.up (trianglePathOrderIso.right_inv n.down))
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The nerve of the `0`-to-`2` path category is the nerve of the lifted ordered interval. -/
def trianglePathNerveFinIso :
    CategoryTheory.nerve TrianglePath.{v} ≅
      CategoryTheory.nerve (ULift.{v, 0} (Fin 2)) where
  hom := CategoryTheory.nerveMap trianglePathToFinFunctor
  inv := CategoryTheory.nerveMap finToTrianglePathFunctor
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map trianglePathToFinFunctor.toCatHom ≫
      CategoryTheory.nerveFunctor.map finToTrianglePathFunctor.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have h : trianglePathToFinFunctor.toCatHom ≫ finToTrianglePathFunctor.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact trianglePathFunctors_comp
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map finToTrianglePathFunctor.toCatHom ≫
      CategoryTheory.nerveFunctor.map trianglePathToFinFunctor.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have h : finToTrianglePathFunctor.toCatHom ≫ trianglePathToFinFunctor.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact finTrianglePathFunctors_comp
    rw [h, CategoryTheory.Functor.map_id]
    rfl

/-- The `0`-to-`2` mapping object in the thickening of `Fin 3` is `Δ[1]`. -/
def trianglePathNerveIso :
    (Δ[1] : SSet.{v}) ≅ CategoryTheory.nerve TrianglePath.{v} :=
  (SSet.stdSimplex.isoNerve 1).trans trianglePathNerveFinIso.symm

abbrev triangleZero : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

abbrev triangleOne : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 1)

abbrev triangleTwo : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 2)

abbrev edgeZero : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 2)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

abbrev edgeOne : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 2)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 1)

@[simp]
theorem deltaTwoFunctor_obj_zero :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).obj edgeZero =
      triangleZero := rfl

@[simp]
theorem deltaTwoFunctor_obj_one :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).obj edgeOne =
      triangleOne := rfl

@[simp]
theorem deltaZeroFunctor_obj_zero :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).obj edgeZero =
      triangleOne := rfl

@[simp]
theorem deltaZeroFunctor_obj_one :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).obj edgeOne =
      triangleTwo := rfl

@[simp]
theorem deltaOneFunctor_obj_zero :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap).obj edgeZero =
      triangleZero := rfl

@[simp]
theorem deltaOneFunctor_obj_one :
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap).obj edgeOne =
      triangleTwo := rfl

/-- The path containing all three triangle vertices. -/
def triangleFullPath : triangleZero.{v} ⟶ triangleTwo.{v} where
  I := Set.Icc (ULift.up 0) (ULift.up 2)
  left := by simp
  right := by simp
  left_le _ h := h.1
  le_right _ h := h.2

/-- The full path as a vertex of its ordinary nerve. -/
def triangleFullPathVertex :
    (CategoryTheory.nerve TrianglePath.{v}).obj (op (SimplexCategory.mk 0)) :=
  (CategoryTheory.Functor.const (Fin 1)).obj triangleFullPath

@[simp]
theorem trianglePathOrderIso_fullPath :
    trianglePathOrderIso.{v} triangleFullPath.{v} = 1 := by
  classical
  change (if triangleInteriorOne.{v}.val ∈ (triangleFullPath.{v}).I then 1 else 0) = 1
  rw [if_pos]
  exact ⟨by decide, by decide⟩

/-- The full thick path is the terminal vertex of `Δ[1]`. -/
theorem trianglePathNerveIso_inv_fullVertex :
    trianglePathNerveIso.inv.app (op (SimplexCategory.mk 0))
        triangleFullPathVertex =
      SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2)) := by
  apply (ConcreteCategory.bijective_of_isIso
    (trianglePathNerveIso.hom.app (op (SimplexCategory.mk 0)))).1
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
    ConcreteCategory.id_apply]
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ by
      fin_cases a
      change triangleFullPath = trianglePathOrderIso.symm 1
      apply trianglePathOrderIso.injective
      rw [trianglePathOrderIso_fullPath, trianglePathOrderIso.apply_symm_apply])
    (h_map := by intros; rfl)

/-- Adjacent paths concatenate to the full path. -/
theorem triangleAdjacentComp_eq_full
    (P : triangleZero.{v} ⟶ triangleOne.{v})
    (Q : triangleOne.{v} ⟶ triangleTwo.{v}) :
    P ≫ Q = triangleFullPath := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext t
  constructor
  · intro _
    obtain ⟨t⟩ := t
    fin_cases t <;> change _ ∈ Set.Icc _ _ <;> decide
  · intro ht
    obtain ⟨t⟩ := t
    fin_cases t
    · exact Or.inl P.left
    · exact Or.inl P.right
    · exact Or.inr Q.right

/-- Enriched composition of adjacent path nerves is the degeneracy of the full path. -/
theorem triangle_eComp_apply_eq_full_degeneracy
    (U : SimplexCategoryᵒᵖ)
    (x : ((CategoryTheory.nerve (triangleZero.{v} ⟶ triangleOne.{v})) ⊗
      CategoryTheory.nerve (triangleOne.{v} ⟶ triangleTwo.{v})).obj U) :
    (CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo).app U x =
      (CategoryTheory.nerve TrianglePath.{v}).map
        (SimplexCategory.const U.unop (SimplexCategory.mk 0) 0).op
        triangleFullPathVertex := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ triangleAdjacentComp_eq_full (x.1.obj a) (x.2.obj a))
    (h_map := by intros; rfl)

/-- Two maps out of the full path nerve agree after adjacent composition when they agree at the
full path vertex. -/
theorem triangle_eComp_ext_of_fullVertex {X : SSet.{v}}
    (a b : CategoryTheory.nerve TrianglePath.{v} ⟶ X)
    (h : a.app (op (SimplexCategory.mk 0)) triangleFullPathVertex =
      b.app (op (SimplexCategory.mk 0)) triangleFullPathVertex) :
    CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫ a =
      CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫ b := by
  ext U x
  change a.app U ((CategoryTheory.eComp SSet _ _ _).app U x) =
    b.app U ((CategoryTheory.eComp SSet _ _ _).app U x)
  rw [triangle_eComp_apply_eq_full_degeneracy]
  let c := (SimplexCategory.const U.unop (SimplexCategory.mk 0) 0).op
  have ha := ConcreteCategory.congr_hom (a.naturality c) triangleFullPathVertex
  have hb := ConcreteCategory.congr_hom (b.naturality c) triangleFullPathVertex
  calc
    _ = X.map c (a.app (op (SimplexCategory.mk 0)) triangleFullPathVertex) := by
      simpa only [ConcreteCategory.comp_apply] using ha
    _ = X.map c (b.app (op (SimplexCategory.mk 0)) triangleFullPathVertex) := congrArg _ h
    _ = _ := by
      simpa only [ConcreteCategory.comp_apply] using hb.symm

variable (C : Type u) [Category.{v} C] [CategoryTheory.SimplicialCategory C]

/-- Data of two adjacent arrows, a proposed long arrow, and a mapping-space path from the long
arrow to the enriched composite. -/
structure TriangleData where
  X₀ : C
  X₁ : C
  X₂ : C
  f₀₁ : X₀ ⟶ X₁
  f₁₂ : X₁ ⟶ X₂
  f₀₂ : X₀ ⟶ X₂
  path : SSet.Edge
    (CategoryTheory.SimplicialCategory.homEquiv' X₀ X₂ f₀₂)
    ((CategoryTheory.SimplicialCategory.sHomComp X₀ X₁ X₂).app (op ⦋0⦌)
      (CategoryTheory.SimplicialCategory.homEquiv' X₀ X₁ f₀₁,
        CategoryTheory.SimplicialCategory.homEquiv' X₁ X₂ f₁₂))

namespace TriangleData

/-- The adjacent arrows as an ordinary composable chain in the forgotten enrichment. -/
def ordinaryChain (d : TriangleData C) :
    CategoryTheory.ComposableArrows (CategoryTheory.ForgetEnrichment SSet.{v} C) 2 :=
  CategoryTheory.ComposableArrows.mk₂
    (CategoryTheory.ForgetEnrichment.homOf SSet (CategoryTheory.eHomEquiv SSet d.f₀₁))
    (CategoryTheory.ForgetEnrichment.homOf SSet (CategoryTheory.eHomEquiv SSet d.f₁₂))

/-- The locally constant coherent simplex associated to the adjacent chain. -/
def locallyConstantSimplex (d : TriangleData C) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))) C :=
  OrdinaryToSimplicialNerve.coherentSimplexOfChain C d.ordinaryChain

/-- One ordinary arrow as a chain in the forgotten enrichment. -/
def edgeChain {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.ComposableArrows (CategoryTheory.ForgetEnrichment SSet.{v} C) 1 :=
  CategoryTheory.ComposableArrows.mk₁
    (CategoryTheory.ForgetEnrichment.homOf SSet (CategoryTheory.eHomEquiv SSet f))

/-- The coherent-nerve `1`-simplex represented by an ordinary arrow. -/
def coherentEdgeSimplex {X Y : C} (f : X ⟶ Y) :
    (CategoryTheory.SimplicialNerve C).obj (op (SimplexCategory.mk 1)) :=
  OrdinaryToSimplicialNerve.coherentSimplexOfChain C (edgeChain C f)

/-- The coherent-nerve vertex represented by an ordinary object. -/
def coherentVertex (X : C) :
    (CategoryTheory.SimplicialNerve C).obj (op (SimplexCategory.mk 0)) :=
  (OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve C).app
    (op (SimplexCategory.mk 0))
    (CategoryTheory.ComposableArrows.mk₀
      (CategoryTheory.ForgetEnrichment.of SSet X))

/-- The edge of the coherent nerve represented by an ordinary arrow. -/
def coherentEdge {X Y : C} (f : X ⟶ Y) :
    SSet.Edge (coherentVertex C X) (coherentVertex C Y) :=
  (CategoryTheory.nerve.edgeMk
    (CategoryTheory.ForgetEnrichment.homOf SSet
      (CategoryTheory.eHomEquiv SSet f))).map
    (OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve C)

@[simp]
theorem coherentEdge_edge {X Y : C} (f : X ⟶ Y) :
    (coherentEdge C f).edge = coherentEdgeSimplex C f := by
  rfl

@[simp]
theorem coherentEdge_id (X : C) :
    coherentEdge C (𝟙 X) = SSet.Edge.id (coherentVertex C X) := by
  have hid : CategoryTheory.ForgetEnrichment.homOf SSet
        (CategoryTheory.eHomEquiv SSet (𝟙 X)) =
      𝟙 (CategoryTheory.ForgetEnrichment.of SSet X) := by
    change CategoryTheory.eHomEquiv SSet (𝟙 X) = CategoryTheory.eId SSet X
    exact CategoryTheory.eHomEquiv_id SSet X
  unfold coherentEdge
  rw [hid, CategoryTheory.nerve.edgeMk_id]
  exact SSet.Edge.map_id _ _

/-- The ordinary morphism induced by an enriched functor. -/
def mapOrdinary {D : Type u} [Category.{v} D] [CategoryTheory.SimplicialCategory D]
    (F : CategoryTheory.EnrichedFunctor SSet C D) {X Y : C} (f : X ⟶ Y) :
    F.obj X ⟶ F.obj Y :=
  (CategoryTheory.SimplicialCategory.homEquiv' (F.obj X) (F.obj Y)).symm
    ((F.map X Y).app (op ⦋0⦌)
      (CategoryTheory.SimplicialCategory.homEquiv' X Y f))

/-- The enriched Hom map sends the source unit-Hom representative to the representative of the
induced ordinary morphism. -/
theorem eHomEquiv_mapOrdinary {D : Type u} [Category.{v} D]
    [CategoryTheory.SimplicialCategory D]
    (F : CategoryTheory.EnrichedFunctor SSet C D) {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.eHomEquiv SSet (mapOrdinary C F f) =
      CategoryTheory.eHomEquiv SSet f ≫ F.map X Y := by
  apply (SSet.unitHomEquiv (F.obj X ⟶[SSet] F.obj Y)).injective
  change CategoryTheory.SimplicialCategory.homEquiv'
      (F.obj X) (F.obj Y) (mapOrdinary C F f) =
    (F.map X Y).app (op ⦋0⦌)
      (CategoryTheory.SimplicialCategory.homEquiv' X Y f)
  exact Equiv.apply_symm_apply _ _

/-- Postcomposition by an enriched functor on coherent nerves. -/
def coherentNerveMap {D : Type u} [Category.{v} D] [CategoryTheory.SimplicialCategory D]
    (F : CategoryTheory.EnrichedFunctor SSet C D) :
    CategoryTheory.SimplicialNerve C ⟶ CategoryTheory.SimplicialNerve D where
  app _ := ↾fun G ↦ CategoryTheory.EnrichedFunctor.comp SSet G F
  naturality _ _ _ := rfl

/-- Postcomposition sends the coherent vertex of `X` to the coherent vertex of `F X`. -/
theorem coherentNerveMap_vertex {D : Type u} [Category.{v} D]
    [CategoryTheory.SimplicialCategory D]
    (F : CategoryTheory.EnrichedFunctor SSet C D) (X : C) :
    (coherentNerveMap C F).app (op ⦋0⦌) (coherentVertex C X) =
      coherentVertex D (F.obj X) := by
  let G := CategoryTheory.EnrichedFunctor.comp SSet (coherentVertex C X) F
  let H := coherentVertex D (F.obj X)
  change G = H
  let i₀ : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 1)) :=
    CategoryTheory.SimplicialThickening.mk (ULift.up 0)
  have thickening_eq
      (i : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 1))) : i = i₀ := by
    rcases i with ⟨i⟩
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    apply Fin.ext
    omega
  let hobj : ∀ i, G.obj i = H.obj i := fun i ↦ by
    rw [thickening_eq i]
    rfl
  apply CategoryTheory.EnrichedFunctor.ext SSet hobj
  intro i j
  rw [thickening_eq i, thickening_eq j]
  letI : IsIso (CategoryTheory.eId SSet i₀) :=
    (CoherentNervePathFiltration.Path.thickPathSelfEIdIso i₀).isIso_hom
  apply (cancel_epi (CategoryTheory.eId SSet i₀)).1
  rw [← Category.assoc, G.map_id, H.map_id]
  have h := hobj i₀
  cases h
  rfl

/-- Postcomposition carries an ordinary coherent edge to the coherent edge of the induced
ordinary morphism. -/
theorem coherentEdge_map {D : Type u} [Category.{v} D]
    [CategoryTheory.SimplicialCategory D]
    (F : CategoryTheory.EnrichedFunctor SSet C D) {X Y : C} (f : X ⟶ Y) :
    (coherentEdge C f).map (coherentNerveMap C F) =
      SSet.Edge.castEndpoints
        (coherentNerveMap_vertex C F X)
        (coherentNerveMap_vertex C F Y)
        (coherentEdge D (mapOrdinary C F f)) := by
  apply SSet.Edge.ext
  simp only [SSet.Edge.map_edge, SSet.Edge.castEndpoints_edge, coherentEdge_edge]
  let G : CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 2))) D :=
    CategoryTheory.EnrichedFunctor.comp SSet (coherentEdgeSimplex C f) F
  let H : CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 2))) D :=
    coherentEdgeSimplex D (mapOrdinary C F f)
  change G = H
  let hobj : ∀ i, G.obj i = H.obj i := fun i ↦ by
    rcases i with ⟨⟨i⟩⟩
    fin_cases i <;> rfl
  apply CategoryTheory.EnrichedFunctor.ext SSet hobj
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  fin_cases i <;> fin_cases j
  · simp only [eqToHom_refl, Category.comp_id]
    change G.map edgeZero edgeZero = H.map edgeZero edgeZero
    letI : IsIso (CategoryTheory.eId SSet edgeZero) :=
      (CoherentNervePathFiltration.Path.thickPathSelfEIdIso edgeZero).isIso_hom
    apply (cancel_epi (CategoryTheory.eId SSet edgeZero)).1
    rw [G.map_id, H.map_id]
    cases hobj edgeZero
    rfl
  · dsimp [G, H, coherentEdgeSimplex, edgeChain,
      OrdinaryToSimplicialNerve.coherentSimplexOfChain,
      OrdinaryToSimplicialNerve.coherentMapOfChain]
    simp only [eqToHom_refl, Category.comp_id]
    rw [eHomEquiv_mapOrdinary C F f]
    simp only [Category.assoc]
  · ext U x
    exact ((by decide : ¬ (ULift.up (1 : Fin 2) : ULift.{v, 0} (Fin 2)) ≤ ULift.up 0)
      (CategoryTheory.SimplicialThickening.Path.le (x.obj 0))).elim
  · simp only [eqToHom_refl, Category.comp_id]
    change G.map edgeOne edgeOne = H.map edgeOne edgeOne
    letI : IsIso (CategoryTheory.eId SSet edgeOne) :=
      (CoherentNervePathFiltration.Path.thickPathSelfEIdIso edgeOne).isIso_hom
    apply (cancel_epi (CategoryTheory.eId SSet edgeOne)).1
    rw [G.map_id, H.map_id]
    cases hobj edgeOne
    rfl

/-- The mapping-space path, reindexed by the `0→2` thick-path nerve. -/
def pathMap (d : TriangleData C) :
    CategoryTheory.nerve TrianglePath.{v} ⟶
      CategoryTheory.SimplicialCategory.sHom d.X₀ d.X₂ :=
  trianglePathNerveIso.inv ≫ SSet.yonedaEquiv.symm d.path.edge

/-- The full path is sent to the composite endpoint of the supplied mapping-space edge. -/
theorem pathMap_fullVertex (d : TriangleData C) :
    d.pathMap.app (op (SimplexCategory.mk 0)) triangleFullPathVertex =
      (CategoryTheory.SimplicialCategory.sHomComp d.X₀ d.X₁ d.X₂).app (op ⦋0⦌)
        (CategoryTheory.SimplicialCategory.homEquiv' d.X₀ d.X₁ d.f₀₁,
          CategoryTheory.SimplicialCategory.homEquiv' d.X₁ d.X₂ d.f₁₂) := by
  rw [show d.pathMap.app (op (SimplexCategory.mk 0)) triangleFullPathVertex =
      (SSet.yonedaEquiv.symm d.path.edge).app (op (SimplexCategory.mk 0))
        (trianglePathNerveIso.inv.app (op (SimplexCategory.mk 0))
          triangleFullPathVertex) by rfl]
  rw [trianglePathNerveIso_inv_fullVertex]
  exact d.path.tgt_eq

/-- The locally constant `0→2` map sends the full path to the enriched composite vertex. -/
theorem locallyConstantMap_fullVertex (d : TriangleData C) :
    (d.locallyConstantSimplex.map triangleZero triangleTwo).app
        (op (SimplexCategory.mk 0)) triangleFullPathVertex =
      (CategoryTheory.SimplicialCategory.sHomComp d.X₀ d.X₁ d.X₂).app (op ⦋0⦌)
        (CategoryTheory.SimplicialCategory.homEquiv' d.X₀ d.X₁ d.f₀₁,
          CategoryTheory.SimplicialCategory.homEquiv' d.X₁ d.X₂ d.f₁₂) := by
  rfl

/-- The special path map agrees with the locally constant simplex after adjacent composition. -/
theorem eComp_pathMap_eq_locallyConstant (d : TriangleData C) :
    CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫ d.pathMap =
      CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫
        d.locallyConstantSimplex.map triangleZero triangleTwo :=
  triangle_eComp_ext_of_fullVertex _ _
    ((d.pathMap_fullVertex).trans d.locallyConstantMap_fullVertex.symm)

/-- The special `0→2` map of the coherent triangle. -/
def specialMap (d : TriangleData C)
    (i j : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)))
    (h : i = triangleZero ∧ j = triangleTwo) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      (d.locallyConstantSimplex.obj i ⟶[SSet] d.locallyConstantSimplex.obj j) := by
  rcases h with ⟨rfl, rfl⟩
  exact d.pathMap

/-- Use the supplied mapping path only on the long `0→2` Hom. -/
def triangleMap (d : TriangleData C)
    (i j : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      (d.locallyConstantSimplex.obj i ⟶[SSet] d.locallyConstantSimplex.obj j) := by
  classical
  exact if h : i = triangleZero ∧ j = triangleTwo then specialMap C d i j h
    else d.locallyConstantSimplex.map i j

@[simp]
theorem specialMap_zero_two (d : TriangleData C)
    (h : triangleZero = triangleZero ∧ triangleTwo = triangleTwo) :
    specialMap C d triangleZero triangleTwo h = d.pathMap := by
  have hh : h = ⟨rfl, rfl⟩ := Subsingleton.elim _ _
  rw [hh]
  rfl

/-- Away from the long `0→2` Hom, the modified map is the locally constant map. -/
theorem triangleMap_eq_locallyConstant_of_not_special (d : TriangleData C)
    (i j : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)))
    (h : ¬ (i = triangleZero ∧ j = triangleTwo)) :
    triangleMap C d i j = d.locallyConstantSimplex.map i j := by
  simp [triangleMap, h]

/-- The modified maps preserve enriched identities. -/
theorem triangleMap_id (d : TriangleData C) :
    ∀ i : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)),
      CategoryTheory.eId SSet i ≫ triangleMap C d i i =
        CategoryTheory.eId SSet (d.locallyConstantSimplex.obj i) := by
  intro i
  classical
  have hspecial : ¬ (i = triangleZero ∧ i = triangleTwo) := by
    rintro ⟨rfl, h⟩
    simp at h
  simp only [triangleMap, dif_neg hspecial]
  exact d.locallyConstantSimplex.map_id i

/-- Every self path in a linear thickening is the identity. -/
theorem selfPath_eq_id
    (i : ULift.{v, 0} (Fin 3))
    (P : CategoryTheory.SimplicialThickening.Path i i) :
    P = 𝟙 (CategoryTheory.SimplicialThickening.mk i) := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext t
  change t ∈ P.I ↔ t = i
  constructor
  · intro ht
    exact le_antisymm (P.le_right t ht) (P.left_le t ht)
  · rintro rfl
    exact P.left

/-- The path map satisfies the left identity case of enriched composition. -/
theorem pathMap_left_identity (d : TriangleData C) :
    CategoryTheory.eComp SSet triangleZero triangleZero triangleTwo ≫ d.pathMap =
      (d.locallyConstantSimplex.map triangleZero triangleZero ⊗ₘ d.pathMap) ≫
        CategoryTheory.eComp SSet
          (d.locallyConstantSimplex.obj triangleZero)
          (d.locallyConstantSimplex.obj triangleZero)
          (d.locallyConstantSimplex.obj triangleTwo) := by
  ext U x
  change ((triangleZero ⟶[SSet] triangleZero).obj U ×
    (triangleZero ⟶[SSet] triangleTwo).obj U) at x
  change d.pathMap.app U ((CategoryTheory.eComp SSet _ _ _).app U x) = _
  have hs : (CategoryTheory.eComp SSet triangleZero triangleZero triangleTwo).app U x =
      x.2 := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        change (x.1).obj a ≫ (x.2).obj a = (x.2).obj a
        rw [selfPath_eq_id _ ((x.1).obj a), Category.id_comp])
      (h_map := by intros; rfl)
  rw [hs]
  simp only [locallyConstantSimplex, OrdinaryToSimplicialNerve.coherentSimplexOfChain,
    OrdinaryToSimplicialNerve.coherentMapOfChain, dif_pos le_rfl,
    CategoryTheory.homOfLE_refl, CategoryTheory.Functor.map_id,
    CategoryTheory.ForgetEnrichment.homTo_id]
  have ht := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.app U) (CategoryTheory.e_id_comp SSet
      (d.locallyConstantSimplex.obj triangleZero)
      (d.locallyConstantSimplex.obj triangleTwo))) (d.pathMap.app U x.2)
  have hin :
      (((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleZero ⟶ triangleZero))).app U ≫
          (CategoryTheory.eId SSet
            (d.locallyConstantSimplex.obj triangleZero)).app U) ⊗ₘ
        d.pathMap.app U) x =
      ((CategoryTheory.eId SSet
          (d.locallyConstantSimplex.obj triangleZero) ▷
          (d.locallyConstantSimplex.obj triangleZero ⟶[SSet]
            d.locallyConstantSimplex.obj triangleTwo)).app U)
        (((λ_ (d.locallyConstantSimplex.obj triangleZero ⟶[SSet]
            d.locallyConstantSimplex.obj triangleTwo)).inv.app U)
          (d.pathMap.app U x.2)) := by
    rfl
  change d.pathMap.app U x.2 =
    (CategoryTheory.eComp SSet
      (d.locallyConstantSimplex.obj triangleZero)
      (d.locallyConstantSimplex.obj triangleZero)
      (d.locallyConstantSimplex.obj triangleTwo)).app U
      ((((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleZero ⟶ triangleZero))).app U ≫
          (CategoryTheory.eId SSet
            (d.locallyConstantSimplex.obj triangleZero)).app U) ⊗ₘ
        d.pathMap.app U) x)
  rw [hin]
  simpa only [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app,
    ConcreteCategory.comp_apply, CategoryTheory.id_apply] using ht.symm

/-- The path map satisfies the right identity case of enriched composition. -/
theorem pathMap_right_identity (d : TriangleData C) :
    CategoryTheory.eComp SSet triangleZero triangleTwo triangleTwo ≫ d.pathMap =
      (d.pathMap ⊗ₘ d.locallyConstantSimplex.map triangleTwo triangleTwo) ≫
        CategoryTheory.eComp SSet
          (d.locallyConstantSimplex.obj triangleZero)
          (d.locallyConstantSimplex.obj triangleTwo)
          (d.locallyConstantSimplex.obj triangleTwo) := by
  ext U x
  change ((triangleZero ⟶[SSet] triangleTwo).obj U ×
    (triangleTwo ⟶[SSet] triangleTwo).obj U) at x
  change d.pathMap.app U ((CategoryTheory.eComp SSet _ _ _).app U x) = _
  have hs : (CategoryTheory.eComp SSet triangleZero triangleTwo triangleTwo).app U x =
      x.1 := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        change (x.1).obj a ≫ (x.2).obj a = (x.1).obj a
        rw [selfPath_eq_id _ ((x.2).obj a), Category.comp_id])
      (h_map := by intros; rfl)
  rw [hs]
  simp only [locallyConstantSimplex, OrdinaryToSimplicialNerve.coherentSimplexOfChain,
    OrdinaryToSimplicialNerve.coherentMapOfChain, dif_pos le_rfl,
    CategoryTheory.homOfLE_refl, CategoryTheory.Functor.map_id,
    CategoryTheory.ForgetEnrichment.homTo_id]
  have ht := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.app U) (CategoryTheory.e_comp_id SSet
      (d.locallyConstantSimplex.obj triangleZero)
      (d.locallyConstantSimplex.obj triangleTwo))) (d.pathMap.app U x.1)
  have hin :
      (d.pathMap.app U ⊗ₘ
        ((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleTwo ⟶ triangleTwo))).app U ≫
          (CategoryTheory.eId SSet
            (d.locallyConstantSimplex.obj triangleTwo)).app U)) x =
      (((d.locallyConstantSimplex.obj triangleZero ⟶[SSet]
            d.locallyConstantSimplex.obj triangleTwo) ◁
          CategoryTheory.eId SSet
            (d.locallyConstantSimplex.obj triangleTwo)).app U)
        (((ρ_ (d.locallyConstantSimplex.obj triangleZero ⟶[SSet]
            d.locallyConstantSimplex.obj triangleTwo)).inv.app U)
          (d.pathMap.app U x.1)) := by
    rfl
  change d.pathMap.app U x.1 =
    (CategoryTheory.eComp SSet
      (d.locallyConstantSimplex.obj triangleZero)
      (d.locallyConstantSimplex.obj triangleTwo)
      (d.locallyConstantSimplex.obj triangleTwo)).app U
      ((d.pathMap.app U ⊗ₘ
        ((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleTwo ⟶ triangleTwo))).app U ≫
          (CategoryTheory.eId SSet
            (d.locallyConstantSimplex.obj triangleTwo)).app U)) x)
  rw [hin]
  simpa only [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app,
    ConcreteCategory.comp_apply, CategoryTheory.id_apply] using ht.symm

/-- A path object is empty when its endpoints are not ordered. -/
theorem trianglePath_empty_of_not_le
    {i j : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))}
    {U : SimplexCategoryᵒᵖ} (hij : ¬ i.as ≤ j.as)
    (x : (i ⟶[SSet] j).obj U) : False :=
  hij (CategoryTheory.SimplicialThickening.Path.le (x.obj 0))

/-- A product of path nerves is empty when either adjacent path is impossible. -/
theorem triangleComposedPath_empty
    {i j k : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))}
    {U : SimplexCategoryᵒᵖ}
    (h : ¬ i.as ≤ j.as ∨ ¬ j.as ≤ k.as)
    (x : ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)).obj U) : False := by
  rcases h with hij | hjk
  · exact trianglePath_empty_of_not_le hij x.1
  · exact trianglePath_empty_of_not_le hjk x.2

/-- The modified maps preserve enriched composition. -/
theorem triangleMap_comp (d : TriangleData C) :
    ∀ i j k : CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3)),
      CategoryTheory.eComp SSet i j k ≫ triangleMap C d i k =
        (triangleMap C d i j ⊗ₘ triangleMap C d j k) ≫
          CategoryTheory.eComp SSet
            (d.locallyConstantSimplex.obj i)
            (d.locallyConstantSimplex.obj j)
            (d.locallyConstantSimplex.obj k) := by
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      triangleMap, CategoryTheory.SimplicialThickening.mk.injEq,
      ULift.up.injEq, Fin.reduceEq, one_ne_zero, and_self, and_false, and_true,
      ↓reduceDIte, CategoryTheory.EnrichedFunctor.map_comp,
      specialMap_zero_two]
  all_goals first
    | exact (eComp_pathMap_eq_locallyConstant C d).trans
        (d.locallyConstantSimplex.map_comp _ _ _)
    | exact pathMap_left_identity C d
    | exact pathMap_right_identity C d
    | (ext U x; exact (triangleComposedPath_empty (by decide) x).elim)

/-- The coherent `2`-simplex determined by the supplied mapping-space path. -/
def coherentSimplex (d : TriangleData C) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{v, 0} (Fin 3))) C where
  obj := d.locallyConstantSimplex.obj
  map := triangleMap C d
  map_id := triangleMap_id C d
  map_comp := triangleMap_comp C d

/-- The unique path from `0` to `1` in the two-vertex thickening. -/
def edgeFullPath : edgeZero.{v} ⟶ edgeOne.{v} where
  I := Set.Icc (ULift.up 0) (ULift.up 1)
  left := by simp
  right := by simp
  left_le _ h := h.1
  le_right _ h := h.2

/-- Every path between the two edge vertices is the full edge path. -/
theorem edgePath_eq_full (P : edgeZero.{v} ⟶ edgeOne.{v}) : P = edgeFullPath := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext t
  constructor
  · intro _
    obtain ⟨t⟩ := t
    fin_cases t <;> change _ ∈ Set.Icc _ _ <;> decide
  · intro ht
    obtain ⟨t⟩ := t
    fin_cases t
    · exact P.left
    · exact P.right

instance edgePathHom_subsingleton
    (P Q : edgeZero.{v} ⟶ edgeOne.{v}) : Subsingleton (P ⟶ Q) :=
  ⟨by
    intro f g
    apply CategoryTheory.InducedCategory.hom_ext
    exact Subsingleton.elim f.hom g.hom⟩

/-- The unique edge path as a vertex of its ordinary nerve. -/
def edgeFullPathVertex :
    (CategoryTheory.nerve (edgeZero.{v} ⟶ edgeOne.{v})).obj
      (op (SimplexCategory.mk 0)) :=
  (CategoryTheory.Functor.const (Fin 1)).obj edgeFullPath

/-- Reinserting the omitted middle vertex sends the edge path to the direct triangle path. -/
def triangleDirectPath : TrianglePath.{v} :=
  (CategoryTheory.SimplicialThickening.functorMap
    (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap edgeZero edgeOne).obj
      edgeFullPath

/-- The direct path as a vertex of the triangle path nerve. -/
def triangleDirectPathVertex :
    (CategoryTheory.nerve TrianglePath.{v}).obj (op (SimplexCategory.mk 0)) :=
  (CategoryTheory.Functor.const (Fin 1)).obj triangleDirectPath

@[simp]
theorem trianglePathOrderIso_directPath :
    trianglePathOrderIso.{v} triangleDirectPath.{v} = 0 := by
  classical
  change (if triangleInteriorOne.{v}.val ∈ triangleDirectPath.I then 1 else 0) = 0
  rw [if_neg]
  intro h
  rcases h with ⟨t, ht, heq⟩
  obtain ⟨t⟩ := t
  fin_cases t
  · have hdown := congrArg ULift.down heq
    change (0 : Fin 3) = 1 at hdown
    omega
  · have hdown := congrArg ULift.down heq
    change (2 : Fin 3) = 1 at hdown
    omega

/-- The direct triangle path is the initial vertex of `Δ[1]`. -/
theorem trianglePathNerveIso_inv_directVertex :
    trianglePathNerveIso.inv.app (op (SimplexCategory.mk 0))
        triangleDirectPathVertex =
      SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2)) := by
  apply (ConcreteCategory.bijective_of_isIso
    (trianglePathNerveIso.hom.app (op (SimplexCategory.mk 0)))).1
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
    ConcreteCategory.id_apply]
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ by
      fin_cases a
      change triangleDirectPath = trianglePathOrderIso.symm 0
      apply trianglePathOrderIso.injective
      rw [trianglePathOrderIso_directPath, trianglePathOrderIso.apply_symm_apply])
    (h_map := by intros; rfl)

/-- The supplied path map sends the direct path to its long-edge source. -/
theorem pathMap_directVertex (d : TriangleData C) :
    d.pathMap.app (op (SimplexCategory.mk 0)) triangleDirectPathVertex =
      CategoryTheory.SimplicialCategory.homEquiv' d.X₀ d.X₂ d.f₀₂ := by
  rw [show d.pathMap.app (op (SimplexCategory.mk 0)) triangleDirectPathVertex =
      (SSet.yonedaEquiv.symm d.path.edge).app (op (SimplexCategory.mk 0))
        (trianglePathNerveIso.inv.app (op (SimplexCategory.mk 0))
          triangleDirectPathVertex) by rfl]
  rw [trianglePathNerveIso_inv_directVertex]
  exact d.path.src_eq

/-- Maps out of the unique edge-path nerve are determined by its vertex. -/
theorem edgePathNerve_ext_of_vertex {X : SSet.{v}}
    (a b : CategoryTheory.nerve (edgeZero.{v} ⟶ edgeOne.{v}) ⟶ X)
    (h : a.app (op (SimplexCategory.mk 0)) edgeFullPathVertex =
      b.app (op (SimplexCategory.mk 0)) edgeFullPathVertex) : a = b := by
  ext U x
  let c := (SimplexCategory.const U.unop (SimplexCategory.mk 0) 0).op
  have hx :
      (CategoryTheory.nerve (edgeZero.{v} ⟶ edgeOne.{v})).map c
          edgeFullPathVertex = x := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun q ↦ (edgePath_eq_full (x.obj q)).symm)
      (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
  have ha := ConcreteCategory.congr_hom (a.naturality c) edgeFullPathVertex
  have hb := ConcreteCategory.congr_hom (b.naturality c) edgeFullPathVertex
  calc
    a.app U x = a.app U
        ((CategoryTheory.nerve (edgeZero.{v} ⟶ edgeOne.{v})).map c
          edgeFullPathVertex) := congrArg (a.app U) hx.symm
    _ = X.map c (a.app (op (SimplexCategory.mk 0)) edgeFullPathVertex) := by
      simpa only [ConcreteCategory.comp_apply] using ha
    _ = X.map c (b.app (op (SimplexCategory.mk 0)) edgeFullPathVertex) := congrArg _ h
    _ = b.app U
        ((CategoryTheory.nerve (edgeZero.{v} ⟶ edgeOne.{v})).map c
          edgeFullPathVertex) := by
      simpa only [ConcreteCategory.comp_apply] using hb.symm
    _ = b.app U x := congrArg (b.app U) hx

/-- The `δ₁` face of the long map is the locally constant map represented by `f₀₂`. -/
theorem deltaOnePathMap_eq_coherentEdgeMap (d : TriangleData C) :
    CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap edgeZero edgeOne) ≫
      d.pathMap =
    (coherentEdgeSimplex C d.f₀₂).map edgeZero edgeOne := by
  apply edgePathNerve_ext_of_vertex
  change d.pathMap.app (op (SimplexCategory.mk 0)) triangleDirectPathVertex = _
  rw [pathMap_directVertex]
  rfl

/-- The first adjacent face is unaffected by the modified long-path map. -/
theorem coherentSimplex_delta_two_eq_locallyConstant (d : TriangleData C) :
    (CategoryTheory.SimplicialNerve C).δ (2 : Fin 3) (coherentSimplex C d) =
      (CategoryTheory.SimplicialNerve C).δ (2 : Fin 3) d.locallyConstantSimplex := by
  classical
  change (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp
        (E := C) SSet (coherentSimplex C d) =
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp
        (E := C) SSet d.locallyConstantSimplex
  refine CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  fin_cases i <;> fin_cases j <;>
    simp only [CategoryTheory.EnrichedFunctor.comp_map, coherentSimplex,
      eqToHom_refl, Category.comp_id]
  all_goals
    rw [triangleMap_eq_locallyConstant_of_not_special C d] <;> simp

/-- The ordinary first adjacent face is the one-arrow chain represented by `f₀₁`. -/
theorem ordinaryChain_delta_two (d : TriangleData C) :
    (CategoryTheory.nerve (CategoryTheory.ForgetEnrichment SSet.{v} C)).δ
        (2 : Fin 3) d.ordinaryChain = edgeChain C d.f₀₁ := by
  let F := (SimplexCategory.toCat.map
    (SimplexCategory.δ (2 : Fin 3))).toFunctor
  have hF : F = Fin.castSuccFunctor 2 := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun i ↦ by
        dsimp [F]
        change (Fin.last 2).succAbove i = i.castSucc
        exact Fin.succAbove_last_apply i)
      (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
  change d.ordinaryChain.whiskerLeft F = edgeChain C d.f₀₁
  rw [hF]
  calc
    d.ordinaryChain.whiskerLeft (Fin.castSuccFunctor 2) =
        CategoryTheory.ComposableArrows.mk₁
          (d.ordinaryChain.whiskerLeft (Fin.castSuccFunctor 2)).hom :=
      (CategoryTheory.ComposableArrows.mk₁_hom _).symm
    _ = edgeChain C d.f₀₁ := by
      congr 1

/-- The face opposite vertex `2` is the first adjacent coherent edge. -/
theorem coherentSimplex_delta_two (d : TriangleData C) :
    (CategoryTheory.SimplicialNerve C).δ (2 : Fin 3) (coherentSimplex C d) =
      coherentEdgeSimplex C d.f₀₁ := by
  rw [coherentSimplex_delta_two_eq_locallyConstant]
  have hnat := ConcreteCategory.congr_hom
    ((OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve C).naturality
      (SimplexCategory.δ (2 : Fin 3)).op) d.ordinaryChain
  simp only [ConcreteCategory.comp_apply] at hnat
  change OrdinaryToSimplicialNerve.coherentSimplexOfChain C
      ((CategoryTheory.nerve (CategoryTheory.ForgetEnrichment SSet.{v} C)).δ
        (2 : Fin 3) d.ordinaryChain) =
    (CategoryTheory.SimplicialNerve C).δ (2 : Fin 3)
      d.locallyConstantSimplex at hnat
  rw [ordinaryChain_delta_two C d] at hnat
  exact hnat.symm

/-- The second adjacent face is unaffected by the modified long-path map. -/
theorem coherentSimplex_delta_zero_eq_locallyConstant (d : TriangleData C) :
    (CategoryTheory.SimplicialNerve C).δ (0 : Fin 3) (coherentSimplex C d) =
      (CategoryTheory.SimplicialNerve C).δ (0 : Fin 3) d.locallyConstantSimplex := by
  classical
  change (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp
        (E := C) SSet (coherentSimplex C d) =
    (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp
        (E := C) SSet d.locallyConstantSimplex
  refine CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  fin_cases i <;> fin_cases j <;>
    simp only [CategoryTheory.EnrichedFunctor.comp_map, coherentSimplex,
      eqToHom_refl, Category.comp_id]
  all_goals
    rw [triangleMap_eq_locallyConstant_of_not_special C d] <;> simp

/-- The ordinary second adjacent face is the one-arrow chain represented by `f₁₂`. -/
theorem ordinaryChain_delta_zero (d : TriangleData C) :
    (CategoryTheory.nerve (CategoryTheory.ForgetEnrichment SSet.{v} C)).δ
        (0 : Fin 3) d.ordinaryChain = edgeChain C d.f₁₂ := by
  change d.ordinaryChain.δ₀ = edgeChain C d.f₁₂
  rfl

/-- The face opposite vertex `0` is the second adjacent coherent edge. -/
theorem coherentSimplex_delta_zero (d : TriangleData C) :
    (CategoryTheory.SimplicialNerve C).δ (0 : Fin 3) (coherentSimplex C d) =
      coherentEdgeSimplex C d.f₁₂ := by
  rw [coherentSimplex_delta_zero_eq_locallyConstant]
  have hnat := ConcreteCategory.congr_hom
    ((OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve C).naturality
      (SimplexCategory.δ (0 : Fin 3)).op) d.ordinaryChain
  simp only [ConcreteCategory.comp_apply] at hnat
  change OrdinaryToSimplicialNerve.coherentSimplexOfChain C
      ((CategoryTheory.nerve (CategoryTheory.ForgetEnrichment SSet.{v} C)).δ
        (0 : Fin 3) d.ordinaryChain) =
    (CategoryTheory.SimplicialNerve C).δ (0 : Fin 3)
      d.locallyConstantSimplex at hnat
  rw [ordinaryChain_delta_zero C d] at hnat
  exact hnat.symm

/-- The long mapping object of the coherent simplex is the supplied path map. -/
theorem triangleMap_zero_two (d : TriangleData C) :
    triangleMap C d triangleZero triangleTwo = d.pathMap := by
  rw [triangleMap]
  split
  · rename_i h
    have hh : h = (⟨rfl, rfl⟩ : triangleZero = triangleZero ∧
        triangleTwo = triangleTwo) := Subsingleton.elim _ _
    rw [hh]
    rfl
  · rename_i h
    exact (h ⟨rfl, rfl⟩).elim

/-- A nerve map followed by the unique map to the tensor unit is the unique source map. -/
theorem nerveMap_comp_toUnit
    {A B : Type v} [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) :
    CategoryTheory.nerveMap F ≫
        CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve B) =
      CategoryTheory.SemiCartesianMonoidalCategory.toUnit
        (CategoryTheory.nerve A) :=
  CategoryTheory.SemiCartesianMonoidalCategory.comp_toUnit
    (CategoryTheory.nerveMap F)

/-- The face opposite vertex `1` is the supplied long coherent edge. -/
theorem coherentSimplex_delta_one (d : TriangleData C) :
    (CategoryTheory.SimplicialNerve C).δ (1 : Fin 3) (coherentSimplex C d) =
      coherentEdgeSimplex C d.f₀₂ := by
  classical
  change (CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap).comp
        (E := C) SSet (coherentSimplex C d) = coherentEdgeSimplex C d.f₀₂
  refine CategoryTheory.EnrichedFunctor.ext SSet (fun i ↦ ?_) ?_
  · obtain ⟨⟨i⟩⟩ := i
    fin_cases i <;> rfl
  · rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
    fin_cases i <;> fin_cases j
    · change CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap edgeZero edgeZero) ≫
          triangleMap C d triangleZero triangleZero =
        (coherentEdgeSimplex C d.f₀₂).map edgeZero edgeZero
      rw [triangleMap_eq_locallyConstant_of_not_special C d] <;> try simp
      change CategoryTheory.nerveMap _ ≫
          (CategoryTheory.SemiCartesianMonoidalCategory.toUnit _ ≫
            CategoryTheory.eId SSet d.X₀) =
        CategoryTheory.SemiCartesianMonoidalCategory.toUnit _ ≫
          CategoryTheory.eId SSet d.X₀
      rw [← Category.assoc, nerveMap_comp_toUnit]
    · change CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap edgeZero edgeOne) ≫
          triangleMap C d triangleZero triangleTwo =
        (coherentEdgeSimplex C d.f₀₂).map edgeZero edgeOne
      rw [triangleMap_zero_two]
      exact deltaOnePathMap_eq_coherentEdgeMap C d
    · ext U x
      exact ((by decide : ¬ edgeOne.as ≤ edgeZero.as)
        (CategoryTheory.SimplicialThickening.Path.le (x.obj 0))).elim
    · change CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            (SimplexCategory.δ (1 : Fin 3)).toOrderHom.uliftMap edgeOne edgeOne) ≫
          triangleMap C d triangleTwo triangleTwo =
        (coherentEdgeSimplex C d.f₀₂).map edgeOne edgeOne
      rw [triangleMap_eq_locallyConstant_of_not_special C d] <;> try simp
      change CategoryTheory.nerveMap _ ≫
          (CategoryTheory.SemiCartesianMonoidalCategory.toUnit _ ≫
            CategoryTheory.eId SSet d.X₂) =
        CategoryTheory.SemiCartesianMonoidalCategory.toUnit _ ≫
          CategoryTheory.eId SSet d.X₂
      rw [← Category.assoc, nerveMap_comp_toUnit]

/-- The coherent triangle as a composition structure in the coherent nerve. -/
def triangleCompStruct (d : TriangleData C) :
    SSet.Edge.CompStruct (coherentEdge C d.f₀₁)
      (coherentEdge C d.f₁₂) (coherentEdge C d.f₀₂) :=
  SSet.Edge.CompStruct.mk (coherentSimplex C d)
    (by simpa using coherentSimplex_delta_two C d)
    (by simpa using coherentSimplex_delta_zero C d)
    (by simpa using coherentSimplex_delta_one C d)

end TriangleData

/-- An ordinary arrow with an inverse candidate and two enriched homotopies to the identities. -/
structure HomotopyInverseData {X Y : C} (f : X ⟶ Y) where
  inverse : Y ⟶ X
  rightPath : SSet.Edge
    (CategoryTheory.SimplicialCategory.homEquiv' X X (𝟙 X))
    ((CategoryTheory.SimplicialCategory.sHomComp X Y X).app (op ⦋0⦌)
      (CategoryTheory.SimplicialCategory.homEquiv' X Y f,
        CategoryTheory.SimplicialCategory.homEquiv' Y X inverse))
  leftPath : SSet.Edge
    (CategoryTheory.SimplicialCategory.homEquiv' Y Y (𝟙 Y))
    ((CategoryTheory.SimplicialCategory.sHomComp Y X Y).app (op ⦋0⦌)
      (CategoryTheory.SimplicialCategory.homEquiv' Y X inverse,
        CategoryTheory.SimplicialCategory.homEquiv' X Y f))

namespace HomotopyInverseData

/-- The triangle witnessing `f ≫ inverse ≃ 𝟙`. -/
def rightTriangle {X Y : C} {f : X ⟶ Y} (d : HomotopyInverseData C f) :
    TriangleData C where
  X₀ := X
  X₁ := Y
  X₂ := X
  f₀₁ := f
  f₁₂ := d.inverse
  f₀₂ := 𝟙 X
  path := d.rightPath

/-- The triangle witnessing `inverse ≫ f ≃ 𝟙`. -/
def leftTriangle {X Y : C} {f : X ⟶ Y} (d : HomotopyInverseData C f) :
    TriangleData C where
  X₀ := Y
  X₁ := X
  X₂ := Y
  f₀₁ := d.inverse
  f₁₂ := f
  f₀₂ := 𝟙 Y
  path := d.leftPath

end HomotopyInverseData

/-- A two-sided enriched homotopy inverse makes the corresponding coherent-nerve edge an
 equivalence. -/
theorem coherentEdge_isEquivalence_of_homotopyInverse
    {X Y : C} (f : X ⟶ Y) (d : HomotopyInverseData C f) :
    EdgeIsEquivalence (TriangleData.coherentEdge C f) := by
  let e := TriangleData.coherentEdge C f
  let g := TriangleData.coherentEdge C d.inverse
  let sr := TriangleData.triangleCompStruct C d.rightTriangle
  let sl := TriangleData.triangleCompStruct C d.leftTriangle
  have hr : edgeHomotopyClass e ≫ edgeHomotopyClass g =
      𝟙 (homotopyObject (TriangleData.coherentVertex C X)) := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      sr.toTruncated).trans (by
        change SSet.Truncated.HomotopyCategory.homMk
            (TriangleData.coherentEdge C (𝟙 X)).toTruncated =
          𝟙 (homotopyObject (TriangleData.coherentVertex C X))
        rw [TriangleData.coherentEdge_id]
        exact SSet.Truncated.HomotopyCategory.homMk_id _)
  have hl : edgeHomotopyClass g ≫ edgeHomotopyClass e =
      𝟙 (homotopyObject (TriangleData.coherentVertex C Y)) := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      sl.toTruncated).trans (by
        change SSet.Truncated.HomotopyCategory.homMk
            (TriangleData.coherentEdge C (𝟙 Y)).toTruncated =
          𝟙 (homotopyObject (TriangleData.coherentVertex C Y))
        rw [TriangleData.coherentEdge_id]
        exact SSet.Truncated.HomotopyCategory.homMk_id _)
  letI : IsIso (edgeHomotopyClass e) := ⟨⟨edgeHomotopyClass g, hr, hl⟩⟩
  infer_instance

end CoherentNerveHomotopyInverse
end LeanLCAExactChallenge.Infinity
