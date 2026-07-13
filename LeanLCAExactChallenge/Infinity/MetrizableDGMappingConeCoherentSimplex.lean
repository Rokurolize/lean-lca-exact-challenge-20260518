import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeCoherentEdge
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

/-!
# The coherent mapping-cone simplex

The mapping-cone nullhomotopy supplies a genuine coherent two-simplex in the direct DG nerve.

Its long edge is the explicit Dold--Kan edge, not a locally constant replacement.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.MappingConeTriangle

open CategoryTheory
open CategoryTheory.EnrichedCategory
open CategoryTheory.MonoidalCategory
open LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve
open Opposite
open Simplicial
open scoped Simplicial

abbrev directDGHomOfBounded {K L : ComplexCategory} (f : K ⟶ L) :
    directDGObject K ⟶ directDGObject L :=
  directDGMorphism f

@[simp]
theorem directDGHomOfBounded_toComplex {K L : ComplexCategory} (f : K ⟶ L) :
    directDGToComplexHomEquiv (directDGObject K) (directDGObject L)
      (directDGHomOfBounded f) = f :=
  directDGToComplexFunctor_map_directDGMorphism f

def mappingConeOrdinaryChain {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.ComposableArrows DirectDGSimplicialCategory 2 :=
  CategoryTheory.ComposableArrows.mk₂
    (directDGHomOfBounded f)
    (directDGHomOfBounded (dgMappingConeInr f))

def mappingConeLocallyConstantSimplex {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin 3)))
      DirectDGSimplicialCategory :=
  coherentSimplexOfChain DirectDGSimplicialCategory (mappingConeOrdinaryChain f)

abbrev triangleZero : CategoryTheory.SimplicialThickening (ULift (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

abbrev triangleOne : CategoryTheory.SimplicialThickening (ULift (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 1)

abbrev triangleTwo : CategoryTheory.SimplicialThickening (ULift (Fin 3)) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 2)

def mappingConeTriangleSpecialMap {K L : ComplexCategory} (f : K ⟶ L)
    (i j : CategoryTheory.SimplicialThickening (ULift (Fin 3)))
    (h : i = triangleZero ∧ j = triangleTwo) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      ((mappingConeLocallyConstantSimplex f).obj i ⟶[SSet]
        (mappingConeLocallyConstantSimplex f).obj j) := by
  rcases h with ⟨rfl, rfl⟩
  exact trianglePathCoherenceMap f

def mappingConeTriangleMap {K L : ComplexCategory} (f : K ⟶ L)
    (i j : CategoryTheory.SimplicialThickening (ULift (Fin 3))) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      ((mappingConeLocallyConstantSimplex f).obj i ⟶[SSet]
        (mappingConeLocallyConstantSimplex f).obj j) := by
  classical
  exact if h : i = triangleZero ∧ j = triangleTwo then
    mappingConeTriangleSpecialMap f i j h
  else
    (mappingConeLocallyConstantSimplex f).map i j

@[simp]
theorem mappingConeTriangleSpecialMap_zero_two {K L : ComplexCategory}
    (f : K ⟶ L) (h : triangleZero = triangleZero ∧
      triangleTwo = triangleTwo) :
    mappingConeTriangleSpecialMap f triangleZero triangleTwo h =
      trianglePathCoherenceMap f := by
  have hh : h = ⟨rfl, rfl⟩ := Subsingleton.elim _ _
  rw [hh]
  rfl

theorem mappingConeTriangleMap_id {K L : ComplexCategory} (f : K ⟶ L) :
    ∀ i : CategoryTheory.SimplicialThickening (ULift (Fin 3)),
      CategoryTheory.eId SSet i ≫ mappingConeTriangleMap f i i =
        CategoryTheory.eId SSet ((mappingConeLocallyConstantSimplex f).obj i) := by
  intro i
  classical
  have hspecial : ¬ (i = triangleZero ∧ i = triangleTwo) := by
    rintro ⟨rfl, h⟩
    simp at h
  simp only [mappingConeTriangleMap, dif_neg hspecial]
  exact (mappingConeLocallyConstantSimplex f).map_id i

def triangleFullPath : triangleZero ⟶ triangleTwo where
  I := Set.Icc (ULift.up (0 : Fin 3)) (ULift.up (2 : Fin 3))
  left := by simp
  right := by simp
  left_le _ h := h.1
  le_right _ h := h.2

theorem triangleAdjacentComp_eq_full
    (P : CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3)) (ULift.up (1 : Fin 3)))
    (Q : CategoryTheory.SimplicialThickening.Path
      (ULift.up (1 : Fin 3)) (ULift.up (2 : Fin 3))) :
    (P : triangleZero ⟶ triangleOne) ≫ (Q : triangleOne ⟶ triangleTwo) =
      triangleFullPath := by
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

def triangleFullPathVertex :
    (CategoryTheory.nerve TrianglePath).obj (op (SimplexCategory.mk 0)) :=
  (CategoryTheory.Functor.const (Fin 1)).obj triangleFullPath

theorem trianglePathOrderIso_fullPath :
    trianglePathOrderIso triangleFullPath = 1 := by
  classical
  change (if triangleInteriorOne.val ∈ triangleFullPath.I then 1 else 0) = 1
  rw [if_pos]
  exact ⟨by decide, by decide⟩

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
      rw [trianglePathOrderIso_fullPath,
        trianglePathOrderIso.apply_symm_apply])
    (h_map := by intros; rfl)

theorem triangle_eComp_apply_eq_full_degeneracy
    (U : SimplexCategoryᵒᵖ)
    (x : ((CategoryTheory.nerve
        (CategoryTheory.SimplicialThickening.Path
          (ULift.up (0 : Fin 3)) (ULift.up (1 : Fin 3)))) ⊗
      CategoryTheory.nerve
        (CategoryTheory.SimplicialThickening.Path
          (ULift.up (1 : Fin 3)) (ULift.up (2 : Fin 3)))).obj U) :
    (CategoryTheory.eComp SSet
      (CategoryTheory.SimplicialThickening.mk (ULift.up (0 : Fin 3)))
      (CategoryTheory.SimplicialThickening.mk (ULift.up (1 : Fin 3)))
      (CategoryTheory.SimplicialThickening.mk (ULift.up (2 : Fin 3)))).app U x =
        (CategoryTheory.nerve TrianglePath).map
          (SimplexCategory.const U.unop (SimplexCategory.mk 0) 0).op
          triangleFullPathVertex := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ triangleAdjacentComp_eq_full (x.1.obj a) (x.2.obj a))
    (h_map := by intros; rfl)

theorem trianglePathCoherenceMap_fullVertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    (trianglePathCoherenceMap f).app (op (SimplexCategory.mk 0))
        triangleFullPathVertex =
      ((dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).δ 0).hom
        (dgMappingConeCoherenceGammaOneSimplex f) := by
  rw [show (trianglePathCoherenceMap f).app (op (SimplexCategory.mk 0))
      triangleFullPathVertex =
      (dgMappingConeCoherenceEdgeMap f).app (op (SimplexCategory.mk 0))
        (trianglePathNerveIso.inv.app (op (SimplexCategory.mk 0))
          triangleFullPathVertex) by rfl]
  rw [trianglePathNerveIso_inv_fullVertex]
  rfl

set_option maxRecDepth 2000 in
theorem mappingConeLocallyConstantSimplex_fullVertex_toComplex
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K (dgMappingConeObject f)
      (((mappingConeLocallyConstantSimplex f).map
        (CategoryTheory.SimplicialThickening.mk (ULift.up (0 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (2 : Fin 3)))).app
          (op (SimplexCategory.mk 0)) triangleFullPathVertex) =
      f ≫ dgMappingConeInr f := by
  have h02 : (ULift.up (0 : Fin 3) : ULift.{0, 0} (Fin 3)) ≤
      (ULift.up (2 : Fin 3) : ULift.{0, 0} (Fin 3)) := by
    change (0 : Fin 3) ≤ 2
    decide
  simp only [mappingConeLocallyConstantSimplex, coherentSimplexOfChain,
    coherentMapOfChain, dif_pos h02]
  have h02down : (0 : Fin 3) ≤ 2 := by decide
  change directDGToComplexFunctor.map
    ((mappingConeOrdinaryChain f).map (homOfLE h02down)) = _
  rw [show (mappingConeOrdinaryChain f).map (homOfLE h02down) =
      directDGMorphism f ≫ directDGMorphism (dgMappingConeInr f) by rfl,
    directDGToComplexFunctor.map_comp,
    directDGToComplexFunctor_map_directDGMorphism,
    directDGToComplexFunctor_map_directDGMorphism]

theorem trianglePathCoherenceMap_fullVertex_eq_locallyConstant
    {K L : ComplexCategory} (f : K ⟶ L) :
    (trianglePathCoherenceMap f).app (op (SimplexCategory.mk 0))
        triangleFullPathVertex =
      ((mappingConeLocallyConstantSimplex f).map
        (CategoryTheory.SimplicialThickening.mk (ULift.up (0 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (2 : Fin 3)))).app
          (op (SimplexCategory.mk 0)) triangleFullPathVertex := by
  apply (dgMappingDirectZModuleVerticesEquivBoundedMorphisms
    K (dgMappingConeObject f)).injective
  rw [trianglePathCoherenceMap_fullVertex,
    dgMappingConeCoherenceGammaOneSimplex_delta_zero_vertex,
    mappingConeLocallyConstantSimplex_fullVertex_toComplex]

theorem triangle_eComp_ext_of_fullVertex {X : SSet}
    (a b : CategoryTheory.nerve TrianglePath ⟶ X)
    (h : a.app (op (SimplexCategory.mk 0)) triangleFullPathVertex =
      b.app (op (SimplexCategory.mk 0)) triangleFullPathVertex) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up (0 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (1 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (2 : Fin 3))) ≫
      a =
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up (0 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (1 : Fin 3)))
        (CategoryTheory.SimplicialThickening.mk (ULift.up (2 : Fin 3))) ≫
      b := by
  ext U x
  change a.app U
      ((CategoryTheory.eComp SSet _ _ _).app U x) =
    b.app U
      ((CategoryTheory.eComp SSet _ _ _).app U x)
  rw [triangle_eComp_apply_eq_full_degeneracy]
  let c := (SimplexCategory.const U.unop (SimplexCategory.mk 0) 0).op
  have hs := ConcreteCategory.congr_hom
    (a.naturality c) triangleFullPathVertex
  have hb := ConcreteCategory.congr_hom
    (b.naturality c) triangleFullPathVertex
  calc
    _ = X.map c (a.app (op (SimplexCategory.mk 0))
        triangleFullPathVertex) := by
      simpa only [ConcreteCategory.comp_apply] using hs
    _ = X.map c (b.app (op (SimplexCategory.mk 0))
        triangleFullPathVertex) := congrArg _ h
    _ = _ := by
      simpa only [ConcreteCategory.comp_apply] using hb.symm

theorem eComp_trianglePathCoherenceMap_eq_locallyConstant
    {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫
      trianglePathCoherenceMap f =
    CategoryTheory.eComp SSet triangleZero triangleOne triangleTwo ≫
      (mappingConeLocallyConstantSimplex f).map triangleZero triangleTwo :=
  triangle_eComp_ext_of_fullVertex _ _
    (trianglePathCoherenceMap_fullVertex_eq_locallyConstant f)

theorem selfPath_eq_id (i : ULift.{0, 0} (Fin 3))
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

theorem trianglePathCoherenceMap_left_identity
    {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.eComp SSet triangleZero triangleZero triangleTwo ≫
      trianglePathCoherenceMap f =
    ((mappingConeLocallyConstantSimplex f).map triangleZero triangleZero ⊗ₘ
      trianglePathCoherenceMap f) ≫
      CategoryTheory.eComp SSet
        ((mappingConeLocallyConstantSimplex f).obj triangleZero)
        ((mappingConeLocallyConstantSimplex f).obj triangleZero)
        ((mappingConeLocallyConstantSimplex f).obj triangleTwo) := by
  ext U x
  change ((triangleZero ⟶[SSet] triangleZero).obj U ×
    (triangleZero ⟶[SSet] triangleTwo).obj U) at x
  change (trianglePathCoherenceMap f).app U
      ((CategoryTheory.eComp SSet _ _ _).app U x) = _
  have hs : (CategoryTheory.eComp SSet triangleZero triangleZero triangleTwo).app U x =
      x.2 := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        change x.1.obj a ≫ x.2.obj a = x.2.obj a
        have hx : x.1.obj a = 𝟙 triangleZero := selfPath_eq_id _ _
        rw [hx, Category.id_comp])
      (h_map := by intros; rfl)
  rw [hs]
  simp only [mappingConeLocallyConstantSimplex, coherentSimplexOfChain,
    coherentMapOfChain, dif_pos le_rfl, CategoryTheory.homOfLE_refl,
    CategoryTheory.Functor.map_id, CategoryTheory.ForgetEnrichment.homTo_id]
  have ht := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.app U) (CategoryTheory.e_id_comp SSet
      ((mappingConeLocallyConstantSimplex f).obj triangleZero)
      ((mappingConeLocallyConstantSimplex f).obj triangleTwo)))
    ((trianglePathCoherenceMap f).app U x.2)
  have hin :
      (((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleZero ⟶ triangleZero))).app U ≫
          (CategoryTheory.eId SSet
            ((mappingConeLocallyConstantSimplex f).obj triangleZero)).app U) ⊗ₘ
        (trianglePathCoherenceMap f).app U) x =
      ((CategoryTheory.eId SSet
          ((mappingConeLocallyConstantSimplex f).obj triangleZero) ▷
          ((mappingConeLocallyConstantSimplex f).obj triangleZero ⟶[SSet]
            (mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U)
        (((λ_ ((mappingConeLocallyConstantSimplex f).obj triangleZero ⟶[SSet]
            (mappingConeLocallyConstantSimplex f).obj triangleTwo)).inv.app U)
          ((trianglePathCoherenceMap f).app U x.2)) := by
    rfl
  change (trianglePathCoherenceMap f).app U x.2 =
    (CategoryTheory.eComp SSet
      ((mappingConeLocallyConstantSimplex f).obj triangleZero)
      ((mappingConeLocallyConstantSimplex f).obj triangleZero)
      ((mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U
      ((((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleZero ⟶ triangleZero))).app U ≫
          (CategoryTheory.eId SSet
            ((mappingConeLocallyConstantSimplex f).obj triangleZero)).app U) ⊗ₘ
        (trianglePathCoherenceMap f).app U) x)
  rw [hin]
  simpa only [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app,
    ConcreteCategory.comp_apply, CategoryTheory.id_apply] using ht.symm

theorem trianglePathCoherenceMap_right_identity
    {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.eComp SSet triangleZero triangleTwo triangleTwo ≫
      trianglePathCoherenceMap f =
    (trianglePathCoherenceMap f ⊗ₘ
      (mappingConeLocallyConstantSimplex f).map triangleTwo triangleTwo) ≫
      CategoryTheory.eComp SSet
        ((mappingConeLocallyConstantSimplex f).obj triangleZero)
        ((mappingConeLocallyConstantSimplex f).obj triangleTwo)
        ((mappingConeLocallyConstantSimplex f).obj triangleTwo) := by
  ext U x
  change ((triangleZero ⟶[SSet] triangleTwo).obj U ×
    (triangleTwo ⟶[SSet] triangleTwo).obj U) at x
  change (trianglePathCoherenceMap f).app U
      ((CategoryTheory.eComp SSet _ _ _).app U x) = _
  have hs : (CategoryTheory.eComp SSet triangleZero triangleTwo triangleTwo).app U x =
      x.1 := by
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        change x.1.obj a ≫ x.2.obj a = x.1.obj a
        have hx : x.2.obj a = 𝟙 triangleTwo := selfPath_eq_id _ _
        rw [hx, Category.comp_id])
      (h_map := by intros; rfl)
  rw [hs]
  simp only [mappingConeLocallyConstantSimplex, coherentSimplexOfChain,
    coherentMapOfChain, dif_pos le_rfl, CategoryTheory.homOfLE_refl,
    CategoryTheory.Functor.map_id, CategoryTheory.ForgetEnrichment.homTo_id]
  have ht := ConcreteCategory.congr_hom
    (congrArg (fun q ↦ q.app U) (CategoryTheory.e_comp_id SSet
      ((mappingConeLocallyConstantSimplex f).obj triangleZero)
      ((mappingConeLocallyConstantSimplex f).obj triangleTwo)))
    ((trianglePathCoherenceMap f).app U x.1)
  have hin :
      ((trianglePathCoherenceMap f).app U ⊗ₘ
        ((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleTwo ⟶ triangleTwo))).app U ≫
          (CategoryTheory.eId SSet
            ((mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U)) x =
      ((((mappingConeLocallyConstantSimplex f).obj triangleZero ⟶[SSet]
            (mappingConeLocallyConstantSimplex f).obj triangleTwo) ◁
          CategoryTheory.eId SSet
            ((mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U)
        (((ρ_ ((mappingConeLocallyConstantSimplex f).obj triangleZero ⟶[SSet]
            (mappingConeLocallyConstantSimplex f).obj triangleTwo)).inv.app U)
          ((trianglePathCoherenceMap f).app U x.1)) := by
    rfl
  change (trianglePathCoherenceMap f).app U x.1 =
    (CategoryTheory.eComp SSet
      ((mappingConeLocallyConstantSimplex f).obj triangleZero)
      ((mappingConeLocallyConstantSimplex f).obj triangleTwo)
      ((mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U
      (((trianglePathCoherenceMap f).app U ⊗ₘ
        ((CategoryTheory.SemiCartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve (triangleTwo ⟶ triangleTwo))).app U ≫
          (CategoryTheory.eId SSet
            ((mappingConeLocallyConstantSimplex f).obj triangleTwo)).app U)) x)
  rw [hin]
  simpa only [CategoryTheory.NatTrans.comp_app, CategoryTheory.NatTrans.id_app,
    ConcreteCategory.comp_apply, CategoryTheory.id_apply] using ht.symm

theorem trianglePath_one_zero_empty {U : SimplexCategoryᵒᵖ}
    (x : (triangleOne ⟶[SSet] triangleZero).obj U) : False := by
  have h := CategoryTheory.SimplicialThickening.Path.le (x.obj 0)
  simp at h

theorem trianglePath_two_zero_empty {U : SimplexCategoryᵒᵖ}
    (x : (triangleTwo ⟶[SSet] triangleZero).obj U) : False := by
  have h := CategoryTheory.SimplicialThickening.Path.le (x.obj 0)
  simp at h

theorem trianglePath_two_one_empty {U : SimplexCategoryᵒᵖ}
    (x : (triangleTwo ⟶[SSet] triangleOne).obj U) : False := by
  have h := CategoryTheory.SimplicialThickening.Path.le (x.obj 0)
  simp at h

theorem trianglePath_empty_of_not_le
    {i j : CategoryTheory.SimplicialThickening (ULift (Fin 3))}
    {U : SimplexCategoryᵒᵖ} (hij : ¬ i.as ≤ j.as)
    (x : (i ⟶[SSet] j).obj U) : False := by
  have y := x.obj 0
  change CategoryTheory.SimplicialThickening.Path i.as j.as at y
  exact hij y.le

theorem triangleComposedPath_empty
    {i j k : CategoryTheory.SimplicialThickening (ULift (Fin 3))}
    {U : SimplexCategoryᵒᵖ}
    (h : ¬ i.as ≤ j.as ∨ ¬ j.as ≤ k.as)
    (x : ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)).obj U) : False := by
  rcases h with hij | hjk
  · exact trianglePath_empty_of_not_le hij x.1
  · exact trianglePath_empty_of_not_le hjk x.2

theorem mappingConeTriangleMap_comp {K L : ComplexCategory} (f : K ⟶ L) :
    ∀ i j k : CategoryTheory.SimplicialThickening (ULift (Fin 3)),
      CategoryTheory.eComp SSet i j k ≫ mappingConeTriangleMap f i k =
        (mappingConeTriangleMap f i j ⊗ₘ mappingConeTriangleMap f j k) ≫
          CategoryTheory.eComp SSet
            ((mappingConeLocallyConstantSimplex f).obj i)
            ((mappingConeLocallyConstantSimplex f).obj j)
            ((mappingConeLocallyConstantSimplex f).obj k) := by
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      mappingConeTriangleMap, CategoryTheory.SimplicialThickening.mk.injEq,
      ULift.up.injEq, Fin.reduceEq, one_ne_zero, and_self, and_false, and_true,
      ↓reduceDIte, CategoryTheory.EnrichedFunctor.map_comp,
      mappingConeTriangleSpecialMap_zero_two]
  all_goals first
    | exact (eComp_trianglePathCoherenceMap_eq_locallyConstant f).trans
        ((mappingConeLocallyConstantSimplex f).map_comp _ _ _)
    | exact trianglePathCoherenceMap_left_identity f
    | exact trianglePathCoherenceMap_right_identity f
    | (ext U x; exact (triangleComposedPath_empty (by decide) x).elim)

def mappingConeCoherentSimplex {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin 3)))
      DirectDGSimplicialCategory where
  obj := (mappingConeLocallyConstantSimplex f).obj
  map := mappingConeTriangleMap f
  map_id := mappingConeTriangleMap_id f
  map_comp := mappingConeTriangleMap_comp f

theorem mappingConeTriangleMap_zero_two {K L : ComplexCategory} (f : K ⟶ L) :
    mappingConeTriangleMap f triangleZero triangleTwo =
      trianglePathCoherenceMap f := by
  rw [mappingConeTriangleMap]
  split
  · rename_i h
    have hh : h = (⟨rfl, rfl⟩ : triangleZero = triangleZero ∧
        triangleTwo = triangleTwo) := Subsingleton.elim _ _
    rw [hh]
    rfl
  · rename_i h
    exact (h ⟨rfl, rfl⟩).elim

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.MappingConeTriangle
