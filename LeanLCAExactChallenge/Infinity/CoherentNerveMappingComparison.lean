/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
import LeanLCAExactChallenge.Infinity.CoherentNerveLatchingCompatibility
import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import LeanLCAExactChallenge.Infinity.CoherentNerveHomotopyInverse

/-!
# Enriched Hom comparison for the homotopy coherent nerve

This module constructs the all-dimensional coherent arrow associated to a simplex of an
enriched Hom object. It packages the construction as a simplicial map into the fixed-endpoint
fiber of the homotopy coherent nerve and develops the prism extraction used for its inverse.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison

open CategoryTheory CategoryTheory.EnrichedCategory CategoryTheory.MonoidalCategory
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

abbrev CoherentOrdinal (n : ℕ) := ULift.{u, 0} (Fin (n + 1))

/-- The value of an interval simplex at one coherent-ordinal vertex. -/
def intervalValue {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CoherentOrdinal n) : Fin 2 :=
  (SSet.stdSimplex.objEquiv s).toOrderHom i.down

/-- The zero-side vertices contained in a thick path. -/
def zeroVertices {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (P : i ⟶ j) : Finset (CoherentOrdinal n) :=
  by
    classical
    exact Finset.univ.filter fun k ↦ k ∈ P.I ∧ intervalValue s k = 0

theorem zeroVertices_nonempty {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (P : i ⟶ j) :
    (zeroVertices s P).Nonempty := by
  classical
  refine ⟨i.as, ?_⟩
  simp [zeroVertices, P.left, hi]

/-- The last zero-side vertex of a thick path. -/
def lastZero {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (P : i ⟶ j) : CoherentOrdinal n :=
  (zeroVertices s P).max' (zeroVertices_nonempty s hi P)

theorem lastZero_mem {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (P : i ⟶ j) :
    lastZero s hi P ∈ P.I ∧ intervalValue s (lastZero s hi P) = 0 := by
  classical
  have h := Finset.max'_mem (zeroVertices s P) (zeroVertices_nonempty s hi P)
  simpa only [lastZero, zeroVertices, Finset.mem_filter, Finset.mem_univ,
    true_and] using h

theorem lastZero_mono {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) {P Q : i ⟶ j} (f : P ⟶ Q) :
    lastZero s hi P ≤ lastZero s hi Q := by
  classical
  apply Finset.le_max'
  simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨f.1.1.1 (lastZero_mem s hi P).1, (lastZero_mem s hi P).2⟩

theorem intervalValue_mono {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CoherentOrdinal n} (h : i ≤ j) :
    intervalValue s i ≤ intervalValue s j := by
  exact (SSet.stdSimplex.objEquiv s).toOrderHom.monotone h

theorem lastZero_comp_of_middle_zero {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as = 0)
    (P : i ⟶ j) (Q : j ⟶ k) :
    lastZero s hi (P ≫ Q) = lastZero s hj Q := by
  classical
  apply le_antisymm
  · apply Finset.max'_le
    intro l hl
    have hl' : l ∈ (P ≫ Q).I ∧ intervalValue s l = 0 := by
      simpa only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    rcases hl'.1 with hlP | hlQ
    · exact (P.le_right l hlP).trans
        (Finset.le_max' (zeroVertices s Q) j.as (by
          simp [zeroVertices, Q.left, hj]))
    · exact Finset.le_max' (zeroVertices s Q) l (by
        simp [zeroVertices, hlQ, hl'.2])
  · apply Finset.le_max'
    simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Or.inr (lastZero_mem s hj Q).1, (lastZero_mem s hj Q).2⟩

theorem lastZero_comp_of_middle_right {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as ≠ 0)
    (P : i ⟶ j) (Q : j ⟶ k) :
    lastZero s hi (P ≫ Q) = lastZero s hi P := by
  classical
  apply le_antisymm
  · apply Finset.max'_le
    intro l hl
    have hl' : l ∈ (P ≫ Q).I ∧ intervalValue s l = 0 := by
      simpa only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    rcases hl'.1 with hlP | hlQ
    · exact Finset.le_max' (zeroVertices s P) l (by
        simp [zeroVertices, hlP, hl'.2])
    · have hm := intervalValue_mono s (Q.left_le l hlQ)
      rw [Fin.eq_one_of_ne_zero _ hj, hl'.2] at hm
      omega
  · apply Finset.le_max'
    simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Or.inl (lastZero_mem s hi P).1, (lastZero_mem s hi P).2⟩

/-- Select the last zero-side vertex functorially along inclusions of thick paths. -/
def lastZeroFunctor {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) : (i ⟶ j) ⥤ CoherentOrdinal n where
  obj P := lastZero s hi P
  map f := homOfLE (lastZero_mono s hi f)

/-- A thick path maps to the standard simplex by its last zero-side vertex. -/
def lastZeroSimplexMap {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) :
    CategoryTheory.nerve (i ⟶ j) ⟶ (Δ[n] : SSet.{u}) :=
  CategoryTheory.nerveMap (lastZeroFunctor s i j hi) ≫
    (SSet.stdSimplex.isoNerve n).inv

theorem intervalValue_map {n m : ℕ}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CoherentOrdinal m) :
    intervalValue ((Δ[1] : SSet.{u}).map f s) i =
      intervalValue s (f.unop.toOrderHom.uliftMap i) := by
  rfl

def reindexedLeftZero {n m : ℕ}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal m))
    (hi : intervalValue ((Δ[1] : SSet.{u}).map f s) i.as = 0) :
    intervalValue s ((CategoryTheory.SimplicialThickening.functor
      f.unop.toOrderHom.uliftMap).obj i).as = 0 :=
  (intervalValue_map f s i.as).symm.trans hi

theorem lastZero_map {n m : ℕ}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal m)}
    (hi : intervalValue ((Δ[1] : SSet.{u}).map f s) i.as = 0)
    (P : i ⟶ j) :
    lastZero s (reindexedLeftZero f s i hi)
        ((CategoryTheory.SimplicialThickening.functorMap
          f.unop.toOrderHom.uliftMap i j).obj P) =
      f.unop.toOrderHom.uliftMap
        (lastZero ((Δ[1] : SSet.{u}).map f s) hi P) := by
  classical
  let phi := f.unop.toOrderHom.uliftMap
  let P' := (CategoryTheory.SimplicialThickening.functorMap phi i j).obj P
  let hi' : intervalValue s (phi i.as) = 0 := reindexedLeftZero f s i hi
  change lastZero s hi' P' = phi
    (lastZero ((Δ[1] : SSet.{u}).map f s) hi P)
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    have hz' : z ∈ P'.I ∧ intervalValue s z = 0 := by
      simpa only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and] using hz
    rcases hz'.1 with ⟨l, hl, rfl⟩
    apply phi.monotone
    apply Finset.le_max'
    simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hl, by
      rw [intervalValue_map]
      exact hz'.2⟩
  · apply Finset.le_max'
    simp only [zeroVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨lastZero ((Δ[1] : SSet.{u}).map f s) hi P,
      (lastZero_mem ((Δ[1] : SSet.{u}).map f s) hi P).1, rfl⟩, by
        rw [← intervalValue_map]
        exact (lastZero_mem ((Δ[1] : SSet.{u}).map f s) hi P).2⟩

@[simp]
theorem lastZeroSimplexMap_app_apply {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0)
    (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (i ⟶ j)).obj U)
    (a : Fin (U.unop.len + 1)) :
    (SSet.stdSimplex.objEquiv ((lastZeroSimplexMap s i j hi).app U x)).toOrderHom a =
      (lastZero s hi (x.obj a)).down := by
  rfl

theorem lastZeroSimplexMap_map {n m : ℕ}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal m)}
    (hi : intervalValue ((Δ[1] : SSet.{u}).map f s) i.as = 0) :
    CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          f.unop.toOrderHom.uliftMap i j) ≫
      lastZeroSimplexMap s
        ((CategoryTheory.SimplicialThickening.functor
          f.unop.toOrderHom.uliftMap).obj i)
        ((CategoryTheory.SimplicialThickening.functor
          f.unop.toOrderHom.uliftMap).obj j)
        (reindexedLeftZero f s i hi) =
      lastZeroSimplexMap ((Δ[1] : SSet.{u}).map f s) i j hi ≫
        SSet.stdSimplex.map f.unop := by
  ext U x
  apply SSet.stdSimplex.ext
  intro a
  change (lastZero s (reindexedLeftZero f s i hi)
      ((CategoryTheory.SimplicialThickening.functorMap
        f.unop.toOrderHom.uliftMap i j).obj (x.obj a))).down =
    f.unop.toOrderHom
      (lastZero ((Δ[1] : SSet.{u}).map f s) hi (x.obj a)).down
  exact congrArg ULift.down (lastZero_map f s hi (x.obj a))

theorem lastZeroSimplexMap_comp_of_middle_zero {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as = 0) :
    CategoryTheory.eComp SSet i j k ≫ lastZeroSimplexMap s i k hi =
      SemiCartesianMonoidalCategory.snd
          (CategoryTheory.nerve (i ⟶ j)) (CategoryTheory.nerve (j ⟶ k)) ≫
        lastZeroSimplexMap s j k hj := by
  apply (cancel_mono (SSet.stdSimplex.isoNerve n).hom).1
  simp only [lastZeroSimplexMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  ext U x a
  exact congrArg (fun z : CoherentOrdinal n ↦ z.down.val)
    (lastZero_comp_of_middle_zero s hi hj (x.1.obj a) (x.2.obj a))

theorem lastZeroSimplexMap_comp_of_middle_right {n : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as ≠ 0) :
    CategoryTheory.eComp SSet i j k ≫ lastZeroSimplexMap s i k hi =
      SemiCartesianMonoidalCategory.fst
          (CategoryTheory.nerve (i ⟶ j)) (CategoryTheory.nerve (j ⟶ k)) ≫
        lastZeroSimplexMap s i j hi := by
  apply (cancel_mono (SSet.stdSimplex.isoNerve n).hom).1
  simp only [lastZeroSimplexMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  ext U x a
  exact congrArg (fun z : CoherentOrdinal n ↦ z.down.val)
    (lastZero_comp_of_middle_right s hi hj (x.1.obj a) (x.2.obj a))

variable (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]

theorem constantCoherentMap_comp {A : Type u} [EnrichedCategory SSet.{u} A]
    (X : C) (i j k : A) :
    eComp SSet i j k ≫
        (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet X) =
      ((SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet X) ⊗ₘ
          (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet X)) ≫
        eComp SSet X X X := by
  rw [← Category.assoc]
  have hu : eComp SSet i j k ≫
      SemiCartesianMonoidalCategory.toUnit (i ⟶[SSet] k) =
      SemiCartesianMonoidalCategory.toUnit
        ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)) :=
    SemiCartesianMonoidalCategory.toUnit_unique _ _
  rw [hu]
  rw [← tensorHom_comp_tensorHom]
  have hid := eHomEquiv_comp SSet (𝟙 X) (𝟙 X)
  simp only [Category.comp_id, eHomEquiv_id] at hid
  have ht :
      SemiCartesianMonoidalCategory.toUnit
          ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)) ≫ (λ_ (𝟙_ SSet)).inv =
        SemiCartesianMonoidalCategory.toUnit (i ⟶[SSet] j) ⊗ₘ
          SemiCartesianMonoidalCategory.toUnit (j ⟶[SSet] k) := by
    apply (cancel_mono (λ_ (𝟙_ SSet)).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact SemiCartesianMonoidalCategory.toUnit_unique _ _
  calc
    _ = SemiCartesianMonoidalCategory.toUnit
          ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)) ≫
        ((λ_ (𝟙_ SSet)).inv ≫
          (eId SSet X ⊗ₘ eId SSet X) ≫ eComp SSet X X X) :=
      congrArg (fun f ↦ SemiCartesianMonoidalCategory.toUnit
        ((i ⟶[SSet] j) ⊗ (j ⟶[SSet] k)) ≫ f) hid
    _ = _ := by
      slice_lhs 1 2 => rw [ht]

theorem parameterizedLeftUnit (A B : SSet.{u}) (X Y : C)
    (g : B ⟶ (X ⟶[SSet] Y)) :
    ((SemiCartesianMonoidalCategory.toUnit A ≫ eId SSet X) ⊗ₘ g) ≫
        eComp SSet X X Y =
      SemiCartesianMonoidalCategory.snd A B ≫ g := by
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [comp_whiskerRight_assoc]
  rw [whisker_exchange_assoc]
  calc
    _ = (SemiCartesianMonoidalCategory.toUnit A ▷ B) ≫
        (𝟙_ SSet ◁ g) ≫ (λ_ (X ⟶[SSet] Y)).hom ≫
          (λ_ (X ⟶[SSet] Y)).inv ≫
            (eId SSet X ▷ (X ⟶[SSet] Y)) ≫ eComp SSet X X Y := by
      simp only [Iso.hom_inv_id_assoc]
    _ = (SemiCartesianMonoidalCategory.toUnit A ▷ B) ≫
        (λ_ B).hom ≫ g ≫ (λ_ (X ⟶[SSet] Y)).inv ≫
          (eId SSet X ▷ (X ⟶[SSet] Y)) ≫ eComp SSet X X Y := by
      rw [leftUnitor_naturality_assoc]
    _ = SemiCartesianMonoidalCategory.snd A B ≫ g := by
      rw [e_id_comp]
      simp only [Category.comp_id, SemiCartesianMonoidalCategory.snd_def]
      rw [SemiCartesianMonoidalCategory.toUnit_unique
        (SemiCartesianMonoidalCategory.toUnit A)
        (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from A)]
      simp only [Category.assoc]

theorem parameterizedRightUnit (A B : SSet.{u}) (X Y : C)
    (f : A ⟶ (X ⟶[SSet] Y)) :
    (f ⊗ₘ (SemiCartesianMonoidalCategory.toUnit B ≫ eId SSet Y)) ≫
        eComp SSet X Y Y =
      SemiCartesianMonoidalCategory.fst A B ≫ f := by
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [whiskerLeft_comp_assoc]
  rw [← whisker_exchange_assoc]
  calc
    _ = (A ◁ SemiCartesianMonoidalCategory.toUnit B) ≫
        (f ▷ 𝟙_ SSet) ≫ (ρ_ (X ⟶[SSet] Y)).hom ≫
          (ρ_ (X ⟶[SSet] Y)).inv ≫
            ((X ⟶[SSet] Y) ◁ eId SSet Y) ≫ eComp SSet X Y Y := by
      simp only [Iso.hom_inv_id_assoc]
    _ = (A ◁ SemiCartesianMonoidalCategory.toUnit B) ≫
        (ρ_ A).hom ≫ f ≫ (ρ_ (X ⟶[SSet] Y)).inv ≫
          ((X ⟶[SSet] Y) ◁ eId SSet Y) ≫ eComp SSet X Y Y := by
      rw [rightUnitor_naturality_assoc]
    _ = SemiCartesianMonoidalCategory.fst A B ≫ f := by
      rw [e_comp_id]
      simp only [Category.comp_id, SemiCartesianMonoidalCategory.fst_def]
      rw [SemiCartesianMonoidalCategory.toUnit_unique
        (SemiCartesianMonoidalCategory.toUnit B)
        (SemiCartesianMonoidalCategory.isTerminalTensorUnit.from B)]
      simp only [Category.assoc]

/-- The object row selected by an interval simplex. -/
abbrev coherentArrowObject {n : ℕ} (X Y : C)
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n)) : C :=
  if intervalValue s i.as = 0 then X else Y

omit [Category.{u} C] [CategoryTheory.SimplicialCategory C] in
@[simp]
theorem coherentArrowObject_eq_left {n : ℕ} (X Y : C)
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) :
    coherentArrowObject C X Y s i = X := by
  simp [coherentArrowObject, hi]

omit [Category.{u} C] [CategoryTheory.SimplicialCategory C] in
@[simp]
theorem coherentArrowObject_eq_right {n : ℕ} (X Y : C)
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as ≠ 0) :
    coherentArrowObject C X Y s i = Y := by
  simp [coherentArrowObject, hi]

/-- Object transport from the left endpoint into the selected coherent row. -/
def coherentArrowLeftEq {n : ℕ} (X Y : C)
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) :
    X = coherentArrowObject C X Y s i :=
  (coherentArrowObject_eq_left C X Y s i hi).symm

/-- Object transport from the right endpoint into the selected coherent row. -/
def coherentArrowRightEq {n : ℕ} (X Y : C)
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as ≠ 0) :
    Y = coherentArrowObject C X Y s i :=
  (coherentArrowObject_eq_right C X Y s i hi).symm

/-- The coherent Hom map selected by a parameter simplex and an interval simplex. -/
def coherentArrowMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n)) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      (coherentArrowObject C X Y s i ⟶[SSet]
        coherentArrowObject C X Y s j) := by
  classical
  by_cases hi : intervalValue s i.as = 0
  · by_cases hj : intervalValue s j.as = 0
    · exact
        (SemiCartesianMonoidalCategory.toUnit
            (CategoryTheory.nerve (i ⟶ j)) ≫ CategoryTheory.eId SSet X) ≫
          eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
            (coherentArrowObject_eq_left C X Y s i hi).symm
            (coherentArrowObject_eq_left C X Y s j hj).symm)
    · exact
        (lastZeroSimplexMap s i j hi ≫ SSet.yonedaEquiv.symm h) ≫
          eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
            (coherentArrowObject_eq_left C X Y s i hi).symm
            (coherentArrowObject_eq_right C X Y s j hj).symm)
  · by_cases hj : intervalValue s j.as = 0
    · have hnot : ¬ i.as ≤ j.as := by
        intro hij
        have hm := intervalValue_mono s hij
        rw [Fin.eq_one_of_ne_zero _ hi, hj] at hm
        omega
      exact
        CoherentNervePathFiltration.Path.mapFromNerveThickPathOfNotLE hnot
            (Y ⟶[SSet] X) ≫
          eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
            (coherentArrowObject_eq_right C X Y s i hi).symm
            (coherentArrowObject_eq_left C X Y s j hj).symm)
    · exact
        (SemiCartesianMonoidalCategory.toUnit
            (CategoryTheory.nerve (i ⟶ j)) ≫ CategoryTheory.eId SSet Y) ≫
          eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
            (coherentArrowObject_eq_right C X Y s i hi).symm
            (coherentArrowObject_eq_right C X Y s j hj).symm)

theorem coherentArrowMap_left_left {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as = 0) :
    coherentArrowMap C h s i j =
      (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet X) ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
          (coherentArrowLeftEq C X Y s i hi)
          (coherentArrowLeftEq C X Y s j hj)) := by
  unfold coherentArrowMap coherentArrowLeftEq
  rw [dif_pos hi, dif_pos hj]

theorem coherentArrowMap_left_right {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as ≠ 0) :
    coherentArrowMap C h s i j =
      (lastZeroSimplexMap s i j hi ≫ SSet.yonedaEquiv.symm h) ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
          (coherentArrowLeftEq C X Y s i hi)
          (coherentArrowRightEq C X Y s j hj)) := by
  unfold coherentArrowMap coherentArrowLeftEq coherentArrowRightEq
  rw [dif_pos hi, dif_neg hj]

theorem coherentArrowMap_right_left {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as ≠ 0) (hj : intervalValue s j.as = 0) :
    coherentArrowMap C h s i j =
      CoherentNervePathFiltration.Path.mapFromNerveThickPathOfNotLE
          (fun hij ↦ by
            have hm := intervalValue_mono s hij
            rw [Fin.eq_one_of_ne_zero _ hi, hj] at hm
            omega)
          (Y ⟶[SSet] X) ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
          (coherentArrowRightEq C X Y s i hi)
          (coherentArrowLeftEq C X Y s j hj)) := by
  unfold coherentArrowMap coherentArrowLeftEq coherentArrowRightEq
  rw [dif_neg hi, dif_pos hj]

theorem coherentArrowMap_right_right {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as ≠ 0) (hj : intervalValue s j.as ≠ 0) :
    coherentArrowMap C h s i j =
      (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet Y) ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
          (coherentArrowRightEq C X Y s i hi)
          (coherentArrowRightEq C X Y s j hj)) := by
  unfold coherentArrowMap coherentArrowRightEq
  rw [dif_neg hi, dif_neg hj]

/-- On an equal-endpoint path object, the coherent arrow map is the enriched identity. -/
theorem coherentArrowMap_self {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n)) :
    coherentArrowMap C h s i i =
      SemiCartesianMonoidalCategory.toUnit _ ≫
        CategoryTheory.eId SSet (coherentArrowObject C X Y s i) := by
  classical
  by_cases hi : intervalValue s i.as = 0
  · unfold coherentArrowMap
    rw [dif_pos hi, dif_pos hi]
    simp [coherentArrowObject, hi]
  · unfold coherentArrowMap
    rw [dif_neg hi, dif_neg hi]
    simp [coherentArrowObject, hi]

theorem coherentArrowMap_id {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal n)) :
    CategoryTheory.eId SSet i ≫ coherentArrowMap C h s i i =
      CategoryTheory.eId SSet (coherentArrowObject C X Y s i) := by
  rw [coherentArrowMap_self]
  rw [← Category.assoc]
  have he : CategoryTheory.eId SSet i ≫
      SemiCartesianMonoidalCategory.toUnit (CategoryTheory.nerve (i ⟶ i)) =
    𝟙 (𝟙_ SSet) := SemiCartesianMonoidalCategory.toUnit_unique _ _
  rw [he, Category.id_comp]

theorem coherentArrowMap_comp_zero_zero_zero {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as = 0)
    (hk : intervalValue s k.as = 0) :
    CategoryTheory.eComp SSet i j k ≫ coherentArrowMap C h s i k =
      (coherentArrowMap C h s i j ⊗ₘ coherentArrowMap C h s j k) ≫
        CategoryTheory.eComp SSet
          (coherentArrowObject C X Y s i)
          (coherentArrowObject C X Y s j)
          (coherentArrowObject C X Y s k) := by
  rw [coherentArrowMap_left_left C h s i k hi hk,
    coherentArrowMap_left_left C h s i j hi hj,
    coherentArrowMap_left_left C h s j k hj hk]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.eComp_eqToHom_of_obj_eq
    (coherentArrowLeftEq C X Y s i hi)
    (coherentArrowLeftEq C X Y s j hj)
    (coherentArrowLeftEq C X Y s k hk)]
  have hconst :
      CategoryTheory.eComp SSet i j k ≫
          (SemiCartesianMonoidalCategory.toUnit
            (CategoryTheory.nerve (i ⟶ k)) ≫ eId SSet X) =
        ((SemiCartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve (i ⟶ j)) ≫ eId SSet X) ⊗ₘ
            (SemiCartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve (j ⟶ k)) ≫ eId SSet X)) ≫
          CategoryTheory.eComp SSet X X X := by
    exact constantCoherentMap_comp C X i j k
  slice_lhs 1 3 => rw [hconst]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]

theorem coherentArrowMap_comp_zero_zero_one {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as = 0)
    (hk : intervalValue s k.as ≠ 0) :
    CategoryTheory.eComp SSet i j k ≫ coherentArrowMap C h s i k =
      (coherentArrowMap C h s i j ⊗ₘ coherentArrowMap C h s j k) ≫
        CategoryTheory.eComp SSet
          (coherentArrowObject C X Y s i)
          (coherentArrowObject C X Y s j)
          (coherentArrowObject C X Y s k) := by
  rw [coherentArrowMap_left_right C h s i k hi hk,
    coherentArrowMap_left_left C h s i j hi hj,
    coherentArrowMap_left_right C h s j k hj hk]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.eComp_eqToHom_of_obj_eq
    (coherentArrowLeftEq C X Y s i hi)
    (coherentArrowLeftEq C X Y s j hj)
    (coherentArrowRightEq C X Y s k hk)]
  slice_lhs 1 2 => rw [lastZeroSimplexMap_comp_of_middle_zero s hi hj]
  slice_rhs 1 2 => rw [tensorHom_comp_tensorHom]
  slice_rhs 1 2 => rw [parameterizedLeftUnit C
    (CategoryTheory.nerve (i ⟶ j)) (CategoryTheory.nerve (j ⟶ k)) X Y
    (lastZeroSimplexMap s j k hj ≫ SSet.yonedaEquiv.symm h)]
  simp only [Category.assoc]

theorem coherentArrowMap_comp_zero_one_one {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as = 0) (hj : intervalValue s j.as ≠ 0)
    (hk : intervalValue s k.as ≠ 0) :
    CategoryTheory.eComp SSet i j k ≫ coherentArrowMap C h s i k =
      (coherentArrowMap C h s i j ⊗ₘ coherentArrowMap C h s j k) ≫
        CategoryTheory.eComp SSet
          (coherentArrowObject C X Y s i)
          (coherentArrowObject C X Y s j)
          (coherentArrowObject C X Y s k) := by
  rw [coherentArrowMap_left_right C h s i k hi hk,
    coherentArrowMap_left_right C h s i j hi hj,
    coherentArrowMap_right_right C h s j k hj hk]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.eComp_eqToHom_of_obj_eq
    (coherentArrowLeftEq C X Y s i hi)
    (coherentArrowRightEq C X Y s j hj)
    (coherentArrowRightEq C X Y s k hk)]
  slice_lhs 1 2 => rw [lastZeroSimplexMap_comp_of_middle_right s hi hj]
  slice_rhs 1 2 => rw [tensorHom_comp_tensorHom]
  slice_rhs 1 2 => rw [parameterizedRightUnit C
    (CategoryTheory.nerve (i ⟶ j)) (CategoryTheory.nerve (j ⟶ k)) X Y
    (lastZeroSimplexMap s i j hi ≫ SSet.yonedaEquiv.symm h)]
  simp only [Category.assoc]

theorem coherentArrowMap_comp_one_one_one {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n))
    (hi : intervalValue s i.as ≠ 0) (hj : intervalValue s j.as ≠ 0)
    (hk : intervalValue s k.as ≠ 0) :
    CategoryTheory.eComp SSet i j k ≫ coherentArrowMap C h s i k =
      (coherentArrowMap C h s i j ⊗ₘ coherentArrowMap C h s j k) ≫
        CategoryTheory.eComp SSet
          (coherentArrowObject C X Y s i)
          (coherentArrowObject C X Y s j)
          (coherentArrowObject C X Y s k) := by
  rw [coherentArrowMap_right_right C h s i k hi hk,
    coherentArrowMap_right_right C h s i j hi hj,
    coherentArrowMap_right_right C h s j k hj hk]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.eComp_eqToHom_of_obj_eq
    (coherentArrowRightEq C X Y s i hi)
    (coherentArrowRightEq C X Y s j hj)
    (coherentArrowRightEq C X Y s k hk)]
  have hconst :
      CategoryTheory.eComp SSet i j k ≫
          (SemiCartesianMonoidalCategory.toUnit
            (CategoryTheory.nerve (i ⟶ k)) ≫ eId SSet Y) =
        ((SemiCartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve (i ⟶ j)) ≫ eId SSet Y) ⊗ₘ
            (SemiCartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve (j ⟶ k)) ≫ eId SSet Y)) ≫
          CategoryTheory.eComp SSet Y Y Y := by
    exact constantCoherentMap_comp C Y i j k
  slice_lhs 1 3 => rw [hconst]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]

theorem false_of_composable_left_decrease {n : ℕ}
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (h : ¬ i.as ≤ j.as) {U : SimplexCategoryᵒᵖ}
    (x : ((CategoryTheory.nerve (i ⟶ j)) ⊗
      CategoryTheory.nerve (j ⟶ k)).obj U) : False :=
  h (CategoryTheory.SimplicialThickening.Path.le (x.1.obj 0))

theorem false_of_composable_right_decrease {n : ℕ}
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)}
    (h : ¬ j.as ≤ k.as) {U : SimplexCategoryᵒᵖ}
    (x : ((CategoryTheory.nerve (i ⟶ j)) ⊗
      CategoryTheory.nerve (j ⟶ k)).obj U) : False :=
  h (CategoryTheory.SimplicialThickening.Path.le (x.2.obj 0))

/-- The coherent arrow map preserves enriched composition in every interval pattern. -/
theorem coherentArrowMap_comp {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal n)) :
    CategoryTheory.eComp SSet i j k ≫ coherentArrowMap C h s i k =
      (coherentArrowMap C h s i j ⊗ₘ coherentArrowMap C h s j k) ≫
        CategoryTheory.eComp SSet
          (coherentArrowObject C X Y s i)
          (coherentArrowObject C X Y s j)
          (coherentArrowObject C X Y s k) := by
  classical
  by_cases hi : intervalValue s i.as = 0
  · by_cases hj : intervalValue s j.as = 0
    · by_cases hk : intervalValue s k.as = 0
      · exact coherentArrowMap_comp_zero_zero_zero C h s i j k hi hj hk
      · exact coherentArrowMap_comp_zero_zero_one C h s i j k hi hj hk
    · by_cases hk : intervalValue s k.as = 0
      · ext U x
        have hnot : ¬ j.as ≤ k.as := by
          intro hjk
          have hm := intervalValue_mono s hjk
          rw [Fin.eq_one_of_ne_zero _ hj, hk] at hm
          omega
        exact (false_of_composable_right_decrease.{u}
          (n := n) (i := i) (j := j) (k := k) hnot x).elim
      · exact coherentArrowMap_comp_zero_one_one C h s i j k hi hj hk
  · by_cases hj : intervalValue s j.as = 0
    · have hnot : ¬ i.as ≤ j.as := by
        intro hij
        have hm := intervalValue_mono s hij
        rw [Fin.eq_one_of_ne_zero _ hi, hj] at hm
        omega
      by_cases hk : intervalValue s k.as = 0
      · ext U x
        exact (false_of_composable_left_decrease.{u}
          (n := n) (i := i) (j := j) (k := k) hnot x).elim
      · ext U x
        exact (false_of_composable_left_decrease.{u}
          (n := n) (i := i) (j := j) (k := k) hnot x).elim
    · by_cases hk : intervalValue s k.as = 0
      · ext U x
        have hnot : ¬ j.as ≤ k.as := by
          intro hjk
          have hm := intervalValue_mono s hjk
          rw [Fin.eq_one_of_ne_zero _ hj, hk] at hm
          omega
        exact (false_of_composable_right_decrease.{u}
          (n := n) (i := i) (j := j) (k := k) hnot x).elim
      · exact coherentArrowMap_comp_one_one_one C h s i j k hi hj hk

/-- One enriched-Hom simplex as an all-dimensional coherent arrow simplex. -/
def coherentArrowSimplex {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n))) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (CoherentOrdinal n)) C where
  obj := coherentArrowObject C X Y s
  map := coherentArrowMap C h s
  map_id := coherentArrowMap_id C h s
  map_comp := coherentArrowMap_comp C h s

omit [Category.{u} C] [CategoryTheory.SimplicialCategory C] in
theorem coherentArrowObject_map {n m : ℕ} {X Y : C}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal m)) :
    coherentArrowObject C X Y ((Δ[1] : SSet.{u}).map f s) i =
      coherentArrowObject C X Y s
        ((CategoryTheory.SimplicialThickening.functor
          f.unop.toOrderHom.uliftMap).obj i) := by
  rfl

theorem coherentHom_yoneda_map {n m : ℕ} {X Y : C}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    SSet.yonedaEquiv.symm ((X ⟶[SSet] Y).map f h) =
      SSet.stdSimplex.map f.unop ≫ SSet.yonedaEquiv.symm h := by
  exact CategoryTheory.uliftYonedaEquiv_symm_map f h

/-- Reindexing a coherent arrow simplex preserves every enriched Hom map. -/
theorem coherentArrowMap_map {n m : ℕ} {X Y : C}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)))
    (s : (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)))
    (i j : CategoryTheory.SimplicialThickening (CoherentOrdinal m)) :
    coherentArrowMap C ((X ⟶[SSet] Y).map f h)
        ((Δ[1] : SSet.{u}).map f s) i j =
      CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            f.unop.toOrderHom.uliftMap i j) ≫
        coherentArrowMap C h s
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj j) := by
  classical
  let s' := (Δ[1] : SSet.{u}).map f s
  by_cases hi : intervalValue s' i.as = 0
  · let hi' := reindexedLeftZero f s i hi
    by_cases hj : intervalValue s' j.as = 0
    · let hj' := reindexedLeftZero f s j hj
      rw [coherentArrowMap_left_left C _ s' i j hi hj,
        coherentArrowMap_left_left C h s _ _ hi' hj']
      ext U x
      rfl
    · let hj' : intervalValue s
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj j).as ≠ 0 := fun h0 ↦
        hj ((intervalValue_map f s j.as).trans h0)
      rw [coherentArrowMap_left_right C _ s' i j hi hj,
        coherentArrowMap_left_right C h s _ _ hi' hj']
      simp only [Category.assoc]
      rw [coherentHom_yoneda_map C f h]
      have hlz := lastZeroSimplexMap_map (i := i) (j := j) f s hi
      dsimp only [s']
      let e₁ := congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
        (coherentArrowLeftEq C X Y ((Δ[1] : SSet.{u}).map f s) i hi)
        (coherentArrowRightEq C X Y ((Δ[1] : SSet.{u}).map f s) j hj)
      convert congrArg (fun q ↦ q ≫ SSet.yonedaEquiv.symm h ≫ eqToHom e₁)
        hlz.symm using 1
      all_goals simp only [Category.assoc]
      all_goals rfl
  · let hi' : intervalValue s
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj i).as ≠ 0 := fun h0 ↦
        hi ((intervalValue_map f s i.as).trans h0)
    by_cases hj : intervalValue s' j.as = 0
    · have hnot : ¬ i.as ≤ j.as := by
        intro hij
        have hm := intervalValue_mono s' hij
        rw [Fin.eq_one_of_ne_zero _ hi, hj] at hm
        omega
      ext U x
      exact (hnot (CategoryTheory.SimplicialThickening.Path.le (x.obj 0))).elim
    · let hj' : intervalValue s
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj j).as ≠ 0 := fun h0 ↦
        hj ((intervalValue_map f s j.as).trans h0)
      rw [coherentArrowMap_right_right C _ s' i j hi hj,
        coherentArrowMap_right_right C h s _ _ hi' hj']
      ext U x
      rfl

theorem eqToHom_self {D : Type u} [Category.{u} D] {X : D} (h : X = X) :
    eqToHom h = 𝟙 X := by
  have hp : h = rfl := Subsingleton.elim _ _
  cases hp
  rfl

/-- The universal coherent arrow cylinder over one enriched Hom object. -/
def coherentArrowCylinderMap {X Y : C} :
    (X ⟶[SSet] Y) ⊗ (Δ[1] : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C where
  app U := by
    rcases U with ⟨⟨n⟩⟩
    exact ↾fun hs ↦ coherentArrowSimplex C hs.1 hs.2
  naturality U V f := by
    rcases U with ⟨⟨n⟩⟩
    rcases V with ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro hs
    change coherentArrowSimplex C
        ((X ⟶[SSet] Y).map f hs.1)
        ((Δ[1] : SSet.{u}).map f hs.2) =
      (CategoryTheory.SimplicialThickening.functor
        f.unop.toOrderHom.uliftMap).comp (E := C) SSet
          (coherentArrowSimplex C hs.1 hs.2)
    apply CategoryTheory.EnrichedFunctor.ext SSet
      (F := coherentArrowSimplex C
        ((X ⟶[SSet] Y).map f hs.1)
        ((Δ[1] : SSet.{u}).map f hs.2))
      (G := (CategoryTheory.SimplicialThickening.functor
        f.unop.toOrderHom.uliftMap).comp (E := C) SSet
          (coherentArrowSimplex C hs.1 hs.2))
      (fun _ ↦ rfl)
    intro i j
    change coherentArrowMap C
        ((X ⟶[SSet] Y).map f hs.1)
        ((Δ[1] : SSet.{u}).map f hs.2) i j ≫ eqToHom _ =
      CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            f.unop.toOrderHom.uliftMap i j) ≫
        coherentArrowMap C hs.1 hs.2
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj j)
    rw [coherentArrowMap_map C f hs.1 hs.2 i j]
    change (CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            f.unop.toOrderHom.uliftMap i j) ≫
        coherentArrowMap C hs.1 hs.2
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            f.unop.toOrderHom.uliftMap).obj j)) ≫ 𝟙 _ = _
    rw [Category.comp_id]

def coherentNerveVertex (X : C) :
    (CategoryTheory.SimplicialNerve C) _⦋0⦌ :=
  CoherentNerveHomotopyInverse.TriangleData.coherentVertex C X

def zeroSimplex (n : ℕ) :
    (Δ[0] : SSet.{u}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objMk (n := SimplexCategory.mk 0) (OrderHom.const _ 0)

def intervalZeroSimplex (n : ℕ) :
    (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objMk (n := SimplexCategory.mk 1) (OrderHom.const _ 0)

def intervalOneSimplex (n : ℕ) :
    (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objMk (n := SimplexCategory.mk 1) (OrderHom.const _ 1)

theorem coherentArrowSimplex_intervalZero {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (SSet.const (X := (Δ[0] : SSet.{u})) (coherentNerveVertex C X)).app
        (op (SimplexCategory.mk n)) (zeroSimplex n) =
      coherentArrowSimplex C h (intervalZeroSimplex n) := by
  apply CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  change ((SSet.const (X := (Δ[0] : SSet.{u}))
      (coherentNerveVertex C X)).app (op (SimplexCategory.mk n))
      (zeroSimplex n)).map i j ≫ 𝟙 _ = _
  rw [Category.comp_id]

theorem coherentArrowSimplex_intervalOne {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (SSet.const (X := (Δ[0] : SSet.{u})) (coherentNerveVertex C Y)).app
        (op (SimplexCategory.mk n)) (zeroSimplex n) =
      coherentArrowSimplex C h (intervalOneSimplex n) := by
  apply CategoryTheory.EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  change ((SSet.const (X := (Δ[0] : SSet.{u}))
      (coherentNerveVertex C Y)).app (op (SimplexCategory.mk n))
      (zeroSimplex n)).map i j ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- The coherent arrow cylinder, transposed to the internal Hom of the coherent nerve. -/
def coherentArrowInternalHomMap {X Y : C} :
    (X ⟶[SSet] Y) ⟶
      (CategoryTheory.ihom (Δ[1] : SSet.{u})).obj
        (CategoryTheory.SimplicialNerve C) :=
  CategoryTheory.MonoidalClosed.curry
    ((β_ (Δ[1] : SSet.{u}) (X ⟶[SSet] Y)).hom ≫
      coherentArrowCylinderMap C)

/-- The transposed coherent arrow has the selected fixed endpoints. -/
theorem coherentArrowEndpoint_condition (X Y : C) :
    SemiCartesianMonoidalCategory.toUnit (X ⟶[SSet] Y) ≫
        endpointPoint (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C X) (coherentNerveVertex C Y) =
      coherentArrowInternalHomMap C ≫
        endpointEvaluation (CategoryTheory.SimplicialNerve C) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [endpointPoint, endpointEvaluation, Category.assoc,
      CartesianMonoidalCategory.lift_fst]
    apply CategoryTheory.MonoidalClosed.uncurry_injective
    rw [CategoryTheory.MonoidalClosed.uncurry_natural_left]
    rw [CategoryTheory.MonoidalClosed.uncurry_pre_app]
    unfold coherentArrowInternalHomMap
    rw [CategoryTheory.MonoidalClosed.uncurry_curry]
    unfold CategoryTheory.MonoidalClosed.curry'
    rw [CategoryTheory.MonoidalClosed.uncurry_curry]
    ext U x
    rcases U with ⟨⟨n⟩⟩
    rcases x with ⟨x0, h⟩
    have hx0 : x0 = zeroSimplex n := by
      apply SSet.stdSimplex.ext
      intro a
      exact Fin.eq_zero _
    subst x0
    dsimp [zeroSimplex, endpointVertex, coherentNerveVertex,
      coherentArrowCylinderMap,
      CoherentNerveHomotopyInverse.TriangleData.coherentVertex]
    change (SSet.const (X := (Δ[0] : SSet.{u}))
        (coherentNerveVertex C X)).app _ (zeroSimplex n) =
      coherentArrowSimplex C h (intervalZeroSimplex n)
    exact coherentArrowSimplex_intervalZero C h
  · simp only [endpointPoint, endpointEvaluation, Category.assoc,
      CartesianMonoidalCategory.lift_snd]
    apply CategoryTheory.MonoidalClosed.uncurry_injective
    rw [CategoryTheory.MonoidalClosed.uncurry_natural_left]
    rw [CategoryTheory.MonoidalClosed.uncurry_pre_app]
    unfold coherentArrowInternalHomMap
    rw [CategoryTheory.MonoidalClosed.uncurry_curry]
    unfold CategoryTheory.MonoidalClosed.curry'
    rw [CategoryTheory.MonoidalClosed.uncurry_curry]
    ext U x
    rcases U with ⟨⟨n⟩⟩
    rcases x with ⟨x0, h⟩
    have hx0 : x0 = zeroSimplex n := by
      apply SSet.stdSimplex.ext
      intro a
      exact Fin.eq_zero _
    subst x0
    dsimp [zeroSimplex, endpointVertex, coherentNerveVertex,
      coherentArrowCylinderMap,
      CoherentNerveHomotopyInverse.TriangleData.coherentVertex]
    change (SSet.const (X := (Δ[0] : SSet.{u}))
        (coherentNerveVertex C Y)).app _ (zeroSimplex n) =
      coherentArrowSimplex C h (intervalOneSimplex n)
    exact coherentArrowSimplex_intervalOne C h

/-- The all-dimensional comparison from an enriched Hom simplicial set to the fixed-endpoint
fiber of the homotopy coherent nerve. -/
noncomputable def coherentArrowEndpointFiberMap {X Y : C} :
    (X ⟶[SSet] Y) ⟶
      endpointFiber (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y) :=
  CategoryTheory.Limits.pullback.lift
    (SemiCartesianMonoidalCategory.toUnit (X ⟶[SSet] Y))
    (coherentArrowInternalHomMap C)
    (coherentArrowEndpoint_condition C X Y)

@[reassoc]
theorem coherentArrowEndpointFiberMap_fst {X Y : C} :
    coherentArrowEndpointFiberMap C ≫
        CategoryTheory.Limits.pullback.fst
          (endpointPoint (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C X) (coherentNerveVertex C Y))
          (endpointEvaluation (CategoryTheory.SimplicialNerve C)) =
      SemiCartesianMonoidalCategory.toUnit (X ⟶[SSet] Y) := by
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem coherentArrowEndpointFiberMap_snd {X Y : C} :
    coherentArrowEndpointFiberMap C ≫
        CategoryTheory.Limits.pullback.snd
          (endpointPoint (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C X) (coherentNerveVertex C Y))
          (endpointEvaluation (CategoryTheory.SimplicialNerve C)) =
      coherentArrowInternalHomMap C := by
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- The interval coordinate which is zero except at the final prism vertex. -/
def finalStepOrderHom (n : ℕ) : Fin (n + 2) →o Fin 2 where
  toFun i := if i.val = n + 1 then 1 else 0
  monotone' := by
    intro a b hab
    by_cases ha : a.val = n + 1
    · have hb : b.val = n + 1 := by omega
      simp [ha, hb]
    · simp [ha]

/-- The top prism simplex used to read an enriched Hom simplex back from a coherent arrow. -/
def extractionPrism (n : ℕ) :
    ((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1))) :=
  (SSet.stdSimplex.objMk
      (SimplexCategory.σ (Fin.last n)).toOrderHom,
    SSet.stdSimplex.objMk (finalStepOrderHom n))

abbrev ExtractionOrdinal (n : ℕ) := ULift.{u, 0} (Fin (n + 2))

/-- Initial vertex of the extraction prism. -/
def extractionFirst (n : ℕ) :
    CategoryTheory.SimplicialThickening (ExtractionOrdinal n) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up 0)

/-- Final vertex of the extraction prism. -/
def extractionLast (n : ℕ) :
    CategoryTheory.SimplicialThickening (ExtractionOrdinal n) :=
  CategoryTheory.SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))

/-- The increasing path whose last zero vertex records the simplex coordinate. -/
def extractionPath {n : ℕ} (a : Fin (n + 1)) :
    CoherentNervePathFiltration.Path.ThickPath
      (ULift.up (0 : Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := {k | k.down ≤ a.castSucc ∨ k.down = Fin.last (n + 1)}
  left := Or.inl (by simp)
  right := Or.inr rfl
  left_le k hk := by
    change (0 : Fin (n + 2)) ≤ k.down
    exact Fin.zero_le _
  le_right k hk := by
    change k.down ≤ Fin.last (n + 1)
    exact Fin.le_last _

/-- The canonical increasing chain of extraction paths. -/
def extractionPathChain (n : ℕ) :
    CoherentNervePathFiltration.Chain.PathChain n
      (ULift.up (0 : Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  path := extractionPath
  monotone' := by
    intro a b hab k hk
    rcases hk with hk | hk
    · exact Or.inl (hk.trans (Fin.castSucc_le_castSucc_iff.mpr hab))
    · exact Or.inr hk

/-- The path-poset simplex used for extraction. -/
noncomputable def extractionPathSimplex (n : ℕ) :
    (CategoryTheory.nerve
      (extractionFirst n ⟶ extractionLast n)).obj
        (op (SimplexCategory.mk n)) :=
  (extractionPathChain n).toNerveSimplex

/-- Turn an internal-Hom simplex into its cylinder map. -/
def cylinderOfInternalHomSimplex {Q : SSet.{u}} {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj Q).obj
      (op (SimplexCategory.mk n))) :
    (Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Q :=
  (β_ (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm a)

/-- Restricting an internal-Hom simplex at an interval endpoint restricts its cylinder map. -/
theorem cylinderOfInternalHomSimplex_pre {Q : SSet.{u}} {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj Q).obj
      (op (SimplexCategory.mk n)))
    (g : (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u})) :
    (β_ (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})).hom ≫
        CategoryTheory.MonoidalClosed.uncurry
          (SSet.yonedaEquiv.symm
            (((CategoryTheory.MonoidalClosed.pre g).app Q).app _ a)) =
      ((Δ[n] : SSet.{u}) ◁ g) ≫ cylinderOfInternalHomSimplex a := by
  unfold cylinderOfInternalHomSimplex
  rw [← SSet.yonedaEquiv_symm_comp]
  rw [CategoryTheory.MonoidalClosed.uncurry_pre_app]
  rw [CategoryTheory.BraidedCategory.braiding_naturality_right_assoc]

/-- The coherent prism simplex represented by an internal-Hom simplex. -/
def coherentPrismSimplex {Q : SSet.{u}} {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj Q).obj
      (op (SimplexCategory.mk n))) :
    Q.obj (op (SimplexCategory.mk (n + 1))) :=
  (cylinderOfInternalHomSimplex a).app _ (extractionPrism n)

/-- Read the long enriched Hom simplex carried by the extraction prism. -/
def rawCoherentExtraction {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n))) :
    (((coherentPrismSimplex a).obj (extractionFirst n)) ⟶[SSet]
      ((coherentPrismSimplex a).obj (extractionLast n))).obj
        (op (SimplexCategory.mk n)) :=
  ((coherentPrismSimplex a).map (extractionFirst n) (extractionLast n)).app _
    (extractionPathSimplex n)

def identitySimplex (n : ℕ) :
    (Δ[n] : SSet.{u}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))

/-- Object evaluation of a coherent-nerve simplex is simplicially natural in a vertex. -/
theorem simplicialNerveMap_obj_vertex {A : SSet.{u}}
    (F : A ⟶ CategoryTheory.SimplicialNerve C) {n : ℕ}
    (s : A.obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    (F.app _ s).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up i)) =
      (F.app (op (SimplexCategory.mk 0))
        (A.map (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) i).op s)).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) := by
  have h := F.naturality_apply
    (SimplexCategory.const (SimplexCategory.mk 0)
      (SimplexCategory.mk n) i).op s
  have hobj := congrArg
    (fun G ↦ G.obj
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))) h
  exact hobj.symm

def endpointSourceObject {n : ℕ}
    (b : ((CategoryTheory.ihom (Δ[0] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n))) : C :=
  (((β_ (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})).hom ≫
      CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm b)).app _
        (identitySimplex n, zeroSimplex n)).obj
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))

def endpointTargetObject {n : ℕ}
    (b : ((CategoryTheory.ihom (Δ[0] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n))) : C :=
  (((β_ (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})).hom ≫
      CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm b)).app _
        (identitySimplex n, zeroSimplex n)).obj
    (CategoryTheory.SimplicialThickening.mk (ULift.up (Fin.last n)))

theorem endpointSourceObject_constant {n : ℕ} (X : C)
    (q : (𝟙_ SSet.{u}).obj (op (SimplexCategory.mk n))) :
    endpointSourceObject C
      ((CategoryTheory.MonoidalClosed.curry'
        (endpointVertex (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C X))).app _ q) = X := by
  rfl

theorem endpointTargetObject_constant {n : ℕ} (Y : C)
    (q : (𝟙_ SSet.{u}).obj (op (SimplexCategory.mk n))) :
    endpointTargetObject C
      ((CategoryTheory.MonoidalClosed.curry'
        (endpointVertex (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C Y))).app _ q) = Y := by
  rfl

theorem endpointSourceObject_restrict {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n))) :
    endpointSourceObject C
      (((CategoryTheory.MonoidalClosed.pre
        (SSet.stdSimplex.δ (1 : Fin 2))).app
          (CategoryTheory.SimplicialNerve C)).app _ a) =
      (coherentPrismSimplex a).obj (extractionFirst n) := by
  let b := ((CategoryTheory.MonoidalClosed.pre
    (SSet.stdSimplex.δ (1 : Fin 2))).app
      (CategoryTheory.SimplicialNerve C)).app _ a
  let F0 : (Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C :=
    (β_ (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})).hom ≫
      CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm b)
  let F := cylinderOfInternalHomSimplex a
  change (F0.app _ (identitySimplex n, zeroSimplex n)).obj
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) =
    (F.app _ (extractionPrism n)).obj (extractionFirst n)
  calc
    _ = (F0.app (op (SimplexCategory.mk 0))
        (((Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u})).map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) 0).op
          (identitySimplex n, zeroSimplex n))).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) :=
      simplicialNerveMap_obj_vertex C F0
        (identitySimplex n, zeroSimplex n) 0
    _ = (F.app (op (SimplexCategory.mk 0))
        (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk (n + 1)) 0).op
          (extractionPrism n))).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) := by
      rfl
    _ = _ := (simplicialNerveMap_obj_vertex C F
      (extractionPrism n) 0).symm

/-- The final object of the extraction prism is the restricted target endpoint. -/
theorem endpointTargetObject_restrict {n : ℕ}
    (a : ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n))) :
    endpointTargetObject C
      (((CategoryTheory.MonoidalClosed.pre
        (SSet.stdSimplex.δ (0 : Fin 2))).app
          (CategoryTheory.SimplicialNerve C)).app _ a) =
      (coherentPrismSimplex a).obj (extractionLast n) := by
  let g : (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
    SSet.stdSimplex.δ (0 : Fin 2)
  let b := ((CategoryTheory.MonoidalClosed.pre g).app
      (CategoryTheory.SimplicialNerve C)).app _ a
  let F0 : (Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C :=
    (β_ (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})).hom ≫
      CategoryTheory.MonoidalClosed.uncurry (SSet.yonedaEquiv.symm b)
  let F := cylinderOfInternalHomSimplex a
  have hF : F0 = ((Δ[n] : SSet.{u}) ◁ g) ≫ F := by
    exact cylinderOfInternalHomSimplex_pre a g
  change (F0.app _ (identitySimplex n, zeroSimplex n)).obj
      (CategoryTheory.SimplicialThickening.mk (ULift.up (Fin.last n))) =
    (F.app _ (extractionPrism n)).obj (extractionLast n)
  calc
    _ = (F0.app (op (SimplexCategory.mk 0))
        (((Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u})).map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) (Fin.last n)).op
          (identitySimplex n, zeroSimplex n))).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) :=
      simplicialNerveMap_obj_vertex C F0
        (identitySimplex n, zeroSimplex n) (Fin.last n)
    _ = ((((Δ[n] : SSet.{u}) ◁ g) ≫ F).app (op (SimplexCategory.mk 0))
        (((Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u})).map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk n) (Fin.last n)).op
          (identitySimplex n, zeroSimplex n))).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) := by
      rw [← hF]
    _ = (F.app (op (SimplexCategory.mk 0))
        (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).map
          (SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk (n + 1)) (Fin.last (n + 1))).op
          (extractionPrism n))).obj
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) := by
      let p0 := (((Δ[n] : SSet.{u}) ⊗ (Δ[0] : SSet.{u})).map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk n) (Fin.last n)).op
        (identitySimplex n, zeroSimplex n))
      let p1 := (((Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})).map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk (n + 1)) (Fin.last (n + 1))).op
        (extractionPrism n))
      change (F.app _ (((Δ[n] : SSet.{u}) ◁ g).app _ p0)).obj _ =
        (F.app _ p1).obj _
      congr 2
      change (p0.1, g.app _ p0.2) = p1
      apply SSet.prodStdSimplex.objEquiv.injective
      apply OrderHom.ext
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change (p0.1 0, (g.app _ p0.2) 0) = (p1.1 0, p1.2 0)
      apply Prod.ext
      · dsimp [p0, p1, identitySimplex, extractionPrism]
        apply Fin.ext
        change (Fin.last n).val =
          ((Fin.last n).predAbove (Fin.last (n + 1))).val
        rw [Fin.predAbove_right_last]
      · dsimp [p0, p1, g, zeroSimplex, extractionPrism]
        apply Fin.ext
        change 1 = (finalStepOrderHom n (Fin.last (n + 1))).val
        simp [finalStepOrderHom]
    _ = _ := (simplicialNerveMap_obj_vertex C F
      (extractionPrism n) (Fin.last (n + 1))).symm

/-- The internal-Hom simplex underlying a simplex of the endpoint fiber. -/
def endpointFiberInternalHomSimplex {n : ℕ} {X Y : C}
    (z : (endpointFiber (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y)).obj
        (op (SimplexCategory.mk n))) :
    ((CategoryTheory.ihom (Δ[1] : SSet.{u})).obj
      (CategoryTheory.SimplicialNerve C)).obj
        (op (SimplexCategory.mk n)) :=
  (CategoryTheory.Limits.pullback.snd
    (endpointPoint (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y))
    (endpointEvaluation (CategoryTheory.SimplicialNerve C))).app _ z

/-- The extraction prism of an endpoint-fiber simplex starts at the prescribed source. -/
theorem endpointFiber_coherentPrismSimplex_first {n : ℕ} {X Y : C}
    (z : (endpointFiber (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y)).obj
        (op (SimplexCategory.mk n))) :
    (coherentPrismSimplex (endpointFiberInternalHomSimplex C z)).obj
        (extractionFirst n) = X := by
  let q :=
    (CategoryTheory.Limits.pullback.fst
      (endpointPoint (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y))
      (endpointEvaluation (CategoryTheory.SimplicialNerve C))).app _ z
  have hmap := CategoryTheory.Limits.pullback.condition
      (f := endpointPoint (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y))
      (g := endpointEvaluation (CategoryTheory.SimplicialNerve C))
  have happ := congrArg
    (fun t ↦ t.app (op (SimplexCategory.mk n))) hmap
  have h := CategoryTheory.congr_fun happ z
  calc
    _ = endpointSourceObject C
        (((CategoryTheory.MonoidalClosed.pre
          (SSet.stdSimplex.δ (1 : Fin 2))).app
            (CategoryTheory.SimplicialNerve C)).app _
              (endpointFiberInternalHomSimplex C z)) :=
      (endpointSourceObject_restrict C
        (endpointFiberInternalHomSimplex C z)).symm
    _ = endpointSourceObject C
        ((CategoryTheory.MonoidalClosed.curry'
          (endpointVertex (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C X))).app _ q) :=
      congrArg (endpointSourceObject C) (congrArg Prod.fst h).symm
    _ = X := endpointSourceObject_constant C X q

/-- The extraction prism of an endpoint-fiber simplex ends at the prescribed target. -/
theorem endpointFiber_coherentPrismSimplex_last {n : ℕ} {X Y : C}
    (z : (endpointFiber (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y)).obj
        (op (SimplexCategory.mk n))) :
    (coherentPrismSimplex (endpointFiberInternalHomSimplex C z)).obj
        (extractionLast n) = Y := by
  let q :=
    (CategoryTheory.Limits.pullback.fst
      (endpointPoint (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y))
      (endpointEvaluation (CategoryTheory.SimplicialNerve C))).app _ z
  have hmap := CategoryTheory.Limits.pullback.condition
      (f := endpointPoint (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y))
      (g := endpointEvaluation (CategoryTheory.SimplicialNerve C))
  have happ := congrArg
    (fun t ↦ t.app (op (SimplexCategory.mk n))) hmap
  have h := CategoryTheory.congr_fun happ z
  calc
    _ = endpointTargetObject C
        (((CategoryTheory.MonoidalClosed.pre
          (SSet.stdSimplex.δ (0 : Fin 2))).app
            (CategoryTheory.SimplicialNerve C)).app _
              (endpointFiberInternalHomSimplex C z)) :=
      (endpointTargetObject_restrict C
        (endpointFiberInternalHomSimplex C z)).symm
    _ = endpointTargetObject C
        ((CategoryTheory.MonoidalClosed.curry'
          (endpointVertex (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C Y))).app _ q) :=
      congrArg (endpointTargetObject C) (congrArg Prod.snd h).symm
    _ = Y := endpointTargetObject_constant C Y q

/--
The dimensionwise prism extraction from an endpoint-fiber simplex. This is the canonical raw
simplex supplied by the top prism, transported along the proved endpoint identifications.

It is intentionally not advertised as a simplicial map: composing the chain of prism arrows
requires the Kan-composition construction.
-/
def endpointFiberRawCoherentExtraction {n : ℕ} {X Y : C}
    (z : (endpointFiber (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y)).obj
        (op (SimplexCategory.mk n))) :
    (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n)) :=
  (eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
    (endpointFiber_coherentPrismSimplex_first C z)
    (endpointFiber_coherentPrismSimplex_last C z))).app _
      (rawCoherentExtraction C (endpointFiberInternalHomSimplex C z))

theorem endpointFiberInternalHomSimplex_forward {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    endpointFiberInternalHomSimplex C
        ((coherentArrowEndpointFiberMap C).app _ h) =
      (coherentArrowInternalHomMap C).app _ h := by
  have hmap := coherentArrowEndpointFiberMap_snd (C := C) (X := X) (Y := Y)
  have happ := congrArg
    (fun t ↦ t.app (op (SimplexCategory.mk n))) hmap
  exact CategoryTheory.congr_fun happ h

end LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison
