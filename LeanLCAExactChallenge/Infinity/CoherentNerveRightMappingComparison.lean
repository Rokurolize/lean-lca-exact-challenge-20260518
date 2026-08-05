/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison
import LeanLCAExactChallenge.Infinity.RightMappingSpaces

/-! # Coherent enriched-Hom right cones

The final vertex of a prism is the target vertex of the coherent arrow.  Unlike
the initial-step cone, this keeps the last-zero coordinate moving through the
whole source simplex and therefore retains all dimensions of an enriched Hom
simplex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution
  MonoidalCategory.ExternalProduct MonoidalCategory Prod

variable (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]

/-- Extend an ordinal map by sending the new final vertex to the new final vertex. -/
def finalAdjoinOrderHom {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    Fin (m + 2) →o Fin (n + 2) where
  toFun i := if hi : i = Fin.last (m + 1) then
      Fin.last (n + 1)
    else
      Fin.castSucc (f.toOrderHom ((Fin.last m).predAbove i))
  monotone' := by
    intro a b hab
    by_cases ha : a = Fin.last (m + 1)
    · subst a
      have hb : b = Fin.last (m + 1) := by
        have hab' : m < b.val := by
          simpa using (Fin.le_def.mp hab)
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      simp [hb]
    · by_cases hb : b = Fin.last (m + 1)
      · simp [ha, hb]
        exact Fin.le_last _
      · simp only [dif_neg ha, dif_neg hb]
        rw [Fin.castSucc_le_castSucc_iff]
        apply f.toOrderHom.monotone
        apply Fin.predAbove_right_monotone (Fin.last m)
        exact hab

/-- The corresponding morphism of the simplex category. -/
def finalAdjoinHom {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SimplexCategory.mk (m + 1) ⟶ SimplexCategory.mk (n + 1) :=
  SimplexCategory.mkHom (finalAdjoinOrderHom f)

/-- The last degeneracy, which projects the right-cone prism to its Hom simplex. -/
def rightConeProjection (n : ℕ) :
    SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk n :=
  SimplexCategory.σ (Fin.last n)

/-- The interval coordinate which is zero except at the final prism vertex. -/
def rightConeIntervalSimplex (n : ℕ) :
    (Δ[1] : SSet.{u}).obj (op (SimplexCategory.mk (n + 1))) :=
  SSet.stdSimplex.objMk (finalStepOrderHom n)

/-- The coherent right-cone simplex associated to an enriched Hom simplex. -/
def coherentArrowRightConeSimplex {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (CategoryTheory.SimplicialNerve C).obj
      (op (SimplexCategory.mk (n + 1))) :=
  coherentArrowSimplex C
    ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
    (rightConeIntervalSimplex n)

theorem finalAdjoinHom_projection_apply_of_ne_last
    {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (i : Fin (m + 2)) (hi : i.val ≠ m + 1) :
    (rightConeProjection n).toOrderHom
        ((finalAdjoinHom f).toOrderHom i) =
      f.toOrderHom ((rightConeProjection m).toOrderHom i) := by
  have hi' : i ≠ Fin.last (m + 1) := by
    intro hlast
    apply hi
    simpa [hlast]
  simp [rightConeProjection, finalAdjoinHom, finalAdjoinOrderHom,
    SimplexCategory.σ, hi']

theorem lastZero_rightCone_ne_last {n : ℕ}
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (n + 1))}
    (hi : intervalValue (rightConeIntervalSimplex n) i.as = 0)
    (P : i ⟶ j) :
    lastZero (rightConeIntervalSimplex n) hi P ≠
      ULift.up (Fin.last (n + 1)) := by
  intro hlast
  have hz := (lastZero_mem (rightConeIntervalSimplex n) hi P).2
  rw [hlast] at hz
  change finalStepOrderHom n (Fin.last (n + 1)) = 0 at hz
  simp [finalStepOrderHom] at hz

theorem rightConeIntervalSimplex_map
    {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
        (rightConeIntervalSimplex n) =
      rightConeIntervalSimplex m := by
  apply SSet.stdSimplex.ext
  intro i
  change finalStepOrderHom n ((finalAdjoinHom f).toOrderHom i) =
    finalStepOrderHom m i
  by_cases hi : i = Fin.last (m + 1)
  · simp [finalStepOrderHom, finalAdjoinHom, finalAdjoinOrderHom, hi]
  · have hf : ((f.toOrderHom ((Fin.last m).predAbove i)).val) < n + 1 :=
      (f.toOrderHom ((Fin.last m).predAbove i)).isLt
    have hival : i.val ≠ m + 1 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa only [Fin.val_last]
    have hpred : (Fin.last m).predAbove i = i.castPred hi :=
      Fin.predAbove_last_of_ne_last hi
    have hf' : ((f.toOrderHom (i.castPred hi)).val) < n + 1 := by
      rw [← hpred]
      exact hf
    simp [finalStepOrderHom, finalAdjoinHom, finalAdjoinOrderHom,
      hi, hival, hpred, hf']
    exact Nat.ne_of_lt hf'

theorem rightConeIntervalValue_map
    {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (i : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (m + 1))) :
    intervalValue
        ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
          (rightConeIntervalSimplex n)) i.as =
      intervalValue (rightConeIntervalSimplex n)
        ((CategoryTheory.SimplicialThickening.functor
          (finalAdjoinHom f).toOrderHom.uliftMap).obj i).as := by
  change intervalValue
      ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
        (rightConeIntervalSimplex n)) i.as =
    intervalValue (rightConeIntervalSimplex n)
      ((finalAdjoinHom f).toOrderHom.uliftMap i.as)
  exact intervalValue_map.{u, u, u} (f := (finalAdjoinHom f).op)
    (s := rightConeIntervalSimplex n) (i := i.as)

/-- The coordinate of a right-cone path in the original Hom simplex. -/
def rightConeCoordinateSimplexMap {n : ℕ}
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (n + 1))}
    (hi : intervalValue (rightConeIntervalSimplex n) i.as = 0) :
    CategoryTheory.nerve (i ⟶ j) ⟶ (Δ[n] : SSet.{u}) :=
  lastZeroSimplexMap (rightConeIntervalSimplex n) i j hi ≫
    SSet.stdSimplex.map (rightConeProjection n)

theorem rightConeCoordinateSimplexMap_comp_of_middle_zero
    {n : ℕ}
    {i j k : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (n + 1))}
    (hi : intervalValue (rightConeIntervalSimplex n) i.as = 0)
    (hj : intervalValue (rightConeIntervalSimplex n) j.as = 0) :
    CategoryTheory.eComp SSet i j k ≫
        rightConeCoordinateSimplexMap hi =
      SemiCartesianMonoidalCategory.snd
          (CategoryTheory.nerve (i ⟶ j))
          (CategoryTheory.nerve (j ⟶ k)) ≫
        rightConeCoordinateSimplexMap hj := by
  unfold rightConeCoordinateSimplexMap
  calc
    _ = (CategoryTheory.eComp SSet i j k ≫
        lastZeroSimplexMap (rightConeIntervalSimplex n) i k hi) ≫
          SSet.stdSimplex.map (rightConeProjection n) :=
      (Category.assoc _ _ _).symm
    _ = (SemiCartesianMonoidalCategory.snd
          (CategoryTheory.nerve (i ⟶ j))
          (CategoryTheory.nerve (j ⟶ k)) ≫
        lastZeroSimplexMap (rightConeIntervalSimplex n) j k hj) ≫
          SSet.stdSimplex.map (rightConeProjection n) := by
      rw [lastZeroSimplexMap_comp_of_middle_zero]
    _ = _ := Category.assoc _ _ _

theorem lastZero_rightCone_map
    {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (m + 1))}
    (hi : intervalValue (rightConeIntervalSimplex m) i.as = 0)
    (P : i ⟶ j) :
    lastZero (rightConeIntervalSimplex n)
        (by
          change intervalValue (rightConeIntervalSimplex n)
            ((finalAdjoinHom f).toOrderHom.uliftMap i.as) = 0
          have hvalue := rightConeIntervalValue_map f i
          change intervalValue
              ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
                (rightConeIntervalSimplex n)) i.as =
            intervalValue (rightConeIntervalSimplex n)
              ((finalAdjoinHom f).toOrderHom.uliftMap i.as) at hvalue
          rw [← hvalue]
          rw [rightConeIntervalSimplex_map f]
          exact hi)
        ((CategoryTheory.SimplicialThickening.functorMap
          (finalAdjoinHom f).toOrderHom.uliftMap i j).obj P) =
      (finalAdjoinHom f).toOrderHom.uliftMap
        (lastZero (rightConeIntervalSimplex m) hi P) := by
  have hlast := lastZero_map (f := (finalAdjoinHom f).op)
      (s := rightConeIntervalSimplex n) (i := i) (j := j)
      (hi := by
        rw [rightConeIntervalSimplex_map f]
        exact hi) P
  change lastZero (rightConeIntervalSimplex n) _
      ((CategoryTheory.SimplicialThickening.functorMap
        (finalAdjoinHom f).op.unop.toOrderHom.uliftMap i j).obj P) =
    (finalAdjoinHom f).op.unop.toOrderHom.uliftMap
      (lastZero (rightConeIntervalSimplex m) hi P)
  convert hlast using 1 <;> try rfl
  congr 1
  simpa only [rightConeIntervalSimplex_map f]

theorem rightConeCoordinateSimplexMap_map
    {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    {i j : CategoryTheory.SimplicialThickening (CoherentOrdinal.{u} (m + 1))}
    (hi : intervalValue (rightConeIntervalSimplex m) i.as = 0)
    (hi' : intervalValue (rightConeIntervalSimplex n)
        ((finalAdjoinHom f).toOrderHom.uliftMap i.as) = 0) :
    CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          (finalAdjoinHom f).toOrderHom.uliftMap i j) ≫
      rightConeCoordinateSimplexMap (n := n)
        (i := (CategoryTheory.SimplicialThickening.functor
          (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
        (j := (CategoryTheory.SimplicialThickening.functor
          (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' =
      rightConeCoordinateSimplexMap (n := m) hi ≫
        SSet.stdSimplex.map f := by
  let hmap : intervalValue
      ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
        (rightConeIntervalSimplex n)) i.as = 0 := by
    rw [rightConeIntervalSimplex_map f]
    exact hi
  have hlast := lastZeroSimplexMap_map
    (f := (finalAdjoinHom f).op)
    (s := rightConeIntervalSimplex n) (i := i) (j := j) hmap
  have hlast' :
      CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            (finalAdjoinHom f).toOrderHom.uliftMap i j) ≫
        lastZeroSimplexMap (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' =
      lastZeroSimplexMap
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i j hmap ≫
        SSet.stdSimplex.map (finalAdjoinHom f) := by
    convert hlast using 1 <;> try rfl
    all_goals apply Subsingleton.elim
  have hlastS :
      lastZeroSimplexMap
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i j hmap =
        lastZeroSimplexMap (rightConeIntervalSimplex m) i j hi := by
    simpa only [rightConeIntervalSimplex_map f]
  unfold rightConeCoordinateSimplexMap
  calc
    _ = (CategoryTheory.nerveMap
          (CategoryTheory.SimplicialThickening.functorMap
            (finalAdjoinHom f).toOrderHom.uliftMap i j) ≫
        lastZeroSimplexMap (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi') ≫
        SSet.stdSimplex.map (rightConeProjection n) :=
      (Category.assoc _ _ _).symm
    _ = (lastZeroSimplexMap
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i j hmap ≫
        SSet.stdSimplex.map (finalAdjoinHom f)) ≫
        SSet.stdSimplex.map (rightConeProjection n) := by
      rw [hlast']
    _ = (lastZeroSimplexMap (rightConeIntervalSimplex m) i j hi ≫
        SSet.stdSimplex.map (rightConeProjection m)) ≫
        SSet.stdSimplex.map f := by
      rw [hlastS]
      rw [Category.assoc, Category.assoc]
      ext U x
      apply SSet.stdSimplex.ext
      intro z
      have hz : (lastZero (rightConeIntervalSimplex m) hi
          (x.obj z)).down ≠ Fin.last (m + 1) := by
        intro hlastz
        apply lastZero_rightCone_ne_last hi (x.obj z)
        apply ULift.ext
        exact hlastz
      have hz' : (lastZero (rightConeIntervalSimplex m) hi
          (x.obj z)).down.val ≠ m + 1 := by
        intro hval
        apply hz
        apply Fin.ext
        simpa only [Fin.val_last]
      exact finalAdjoinHom_projection_apply_of_ne_last f
        (lastZero (rightConeIntervalSimplex m) hi (x.obj z)).down hz'
    _ = _ := Category.assoc _ _ _

set_option maxHeartbeats 800000 in
theorem coherentArrowRightConeSimplex_map
    {m n : ℕ} {X Y : C}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (CategoryTheory.SimplicialThickening.functor
        (finalAdjoinHom f).toOrderHom.uliftMap).comp
          (E := C) SSet
          (coherentArrowRightConeSimplex C h) =
      coherentArrowRightConeSimplex C
        ((X ⟶[SSet] Y).map f.op h) := by
  classical
  unfold coherentArrowRightConeSimplex
  symm
  apply CategoryTheory.EnrichedFunctor.ext SSet
    (F := coherentArrowSimplex C
      ((X ⟶[SSet] Y).map (rightConeProjection m).op
        ((X ⟶[SSet] Y).map f.op h))
      (rightConeIntervalSimplex m))
    (G := (CategoryTheory.SimplicialThickening.functor
      (finalAdjoinHom f).toOrderHom.uliftMap).comp (E := C) SSet
      (coherentArrowSimplex C
        ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
        (rightConeIntervalSimplex n)))
    (fun i ↦ by
      rw [← rightConeIntervalSimplex_map f]
      exact coherentArrowObject_map C (finalAdjoinHom f).op
        (rightConeIntervalSimplex n) i)
  intro i j
  change coherentArrowMap C
      ((X ⟶[SSet] Y).map (rightConeProjection m).op
        ((X ⟶[SSet] Y).map f.op h))
      (rightConeIntervalSimplex m) i j ≫ eqToHom _ =
    CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          (finalAdjoinHom f).toOrderHom.uliftMap i j) ≫
      coherentArrowMap C
        ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
      (rightConeIntervalSimplex n)
        ((CategoryTheory.SimplicialThickening.functor
          (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
        ((CategoryTheory.SimplicialThickening.functor
          (finalAdjoinHom f).toOrderHom.uliftMap).obj j)
  have hvi := rightConeIntervalValue_map f i
  have hvj := rightConeIntervalValue_map f j
  change intervalValue
      ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
        (rightConeIntervalSimplex n)) i.as =
    intervalValue (rightConeIntervalSimplex n)
      ((finalAdjoinHom f).toOrderHom.uliftMap i.as) at hvi
  change intervalValue
      ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
        (rightConeIntervalSimplex n)) j.as =
    intervalValue (rightConeIntervalSimplex n)
      ((finalAdjoinHom f).toOrderHom.uliftMap j.as) at hvj
  rw [rightConeIntervalSimplex_map f] at hvi hvj
  have hobj_i :
      coherentArrowObject C X Y (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i) =
        coherentArrowObject C X Y (rightConeIntervalSimplex m) i := by
    have he := coherentArrowObject_map C (X := X) (Y := Y)
      (finalAdjoinHom f).op
      (rightConeIntervalSimplex n) i
    have hs := congrArg (fun t ↦ coherentArrowObject C X Y t i)
      (rightConeIntervalSimplex_map f)
    exact he.symm.trans hs
  have hobj_j :
      coherentArrowObject C X Y (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) =
        coherentArrowObject C X Y (rightConeIntervalSimplex m) j := by
    have he := coherentArrowObject_map C (X := X) (Y := Y)
      (finalAdjoinHom f).op
      (rightConeIntervalSimplex n) j
    have hs := congrArg (fun t ↦ coherentArrowObject C X Y t j)
      (rightConeIntervalSimplex_map f)
    exact he.symm.trans hs
  have hobj_i_map :
      coherentArrowObject C X Y
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i =
        coherentArrowObject C X Y (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i) :=
    coherentArrowObject_map C (finalAdjoinHom f).op
      (rightConeIntervalSimplex n) i
  have hobj_j_map :
      coherentArrowObject C X Y
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) j =
        coherentArrowObject C X Y (rightConeIntervalSimplex n)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) :=
    coherentArrowObject_map C (finalAdjoinHom f).op
      (rightConeIntervalSimplex n) j
  have hHom := congrArg₂
    (fun A B : C ↦ CategoryTheory.nerve (i ⟶ j) ⟶
      (A ⟶[SSet] B)) hobj_i hobj_j
  have hHom_map := congrArg₂
    (fun A B : C ↦ CategoryTheory.nerve (i ⟶ j) ⟶
      (A ⟶[SSet] B)) hobj_i_map.symm hobj_j_map.symm
  by_cases hi : intervalValue (rightConeIntervalSimplex m) i.as = 0
  · by_cases hj : intervalValue (rightConeIntervalSimplex m) j.as = 0
    · have hi' := hvi.symm.trans hi
      have hj' := hvj.symm.trans hj
      have hmap_i : intervalValue
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i.as = 0 := by
        rw [rightConeIntervalSimplex_map f]
        exact hi
      have hmap_j : intervalValue
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) j.as = 0 := by
        rw [rightConeIntervalSimplex_map f]
        exact hj
      rw [coherentArrowMap_left_left C _ _ i j hi hj,
        coherentArrowMap_left_left C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' hj']
      have hg := coherentArrowMap_map C (finalAdjoinHom f).op
        ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
        (rightConeIntervalSimplex n) i j
      rw [coherentArrowMap_left_left C _ _ i j hmap_i hmap_j,
        coherentArrowMap_left_left C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).op.unop.toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).op.unop.toOrderHom.uliftMap).obj j) hi' hj'] at hg
      convert hg using 1
      all_goals try exact hHom
      all_goals try simp only [Category.assoc, eqToHom_trans]
      all_goals try simp only [Quiver.Hom.unop_op]
      all_goals try (apply heq_of_eq; congr 1)
      all_goals try rfl

    · have hi' := hvi.symm.trans hi
      have hj' : intervalValue (rightConeIntervalSimplex n)
          ((finalAdjoinHom f).toOrderHom.uliftMap j.as) ≠ 0 := by
        intro hz
        exact hj (hvj.trans hz)
      rw [coherentArrowMap_left_right C _ _ i j hi hj,
        coherentArrowMap_left_right C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' hj']
      simp only [Category.assoc]
      rw [coherentHom_yoneda_map C (rightConeProjection m).op
        ((X ⟶[SSet] Y).map f.op h)]
      rw [coherentHom_yoneda_map C f.op h]
      rw [coherentHom_yoneda_map C (rightConeProjection n).op h]
      let e₁ := congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
        (coherentArrowLeftEq C X Y (rightConeIntervalSimplex m) i hi)
        (coherentArrowRightEq C X Y (rightConeIntervalSimplex m) j hj)
      have hcoord := rightConeCoordinateSimplexMap_map f (i := i) (j := j) hi hi'
      unfold rightConeCoordinateSimplexMap at hcoord
      convert congrArg (fun q ↦ q ≫ SSet.yonedaEquiv.symm h ≫ eqToHom e₁)
        hcoord.symm using 1
      all_goals try subst_vars
      all_goals try exact hHom
      all_goals try simp only [Category.assoc, eqToHom_trans]
      all_goals try simp only [Quiver.Hom.unop_op]
      all_goals repeat rw [← Category.assoc]
      all_goals
        change _ ≍ (_ ≫ eqToHom e₁)
        apply (heq_comp_eqToHom_iff _ _ _).2
        exact comp_eqToHom_heq _ _
      all_goals try rfl
  · by_cases hj : intervalValue (rightConeIntervalSimplex m) j.as = 0
    · have hi' : intervalValue (rightConeIntervalSimplex n)
          ((finalAdjoinHom f).toOrderHom.uliftMap i.as) ≠ 0 := by
        intro hz
        exact hi (hvi.trans hz)
      have hj' := hvj.symm.trans hj
      rw [coherentArrowMap_right_left C _ _ i j hi hj,
        coherentArrowMap_right_left C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' hj']
      have hnot : ¬ i.as ≤ j.as := by
        intro hij
        have hm := intervalValue_mono (rightConeIntervalSimplex m) hij
        rw [Fin.eq_one_of_ne_zero _ hi, hj] at hm
        omega
      ext U x
      exact (hnot (CategoryTheory.SimplicialThickening.Path.le (x.obj 0))).elim
    · have hi' : intervalValue (rightConeIntervalSimplex n)
          ((finalAdjoinHom f).toOrderHom.uliftMap i.as) ≠ 0 := by
        intro hz
        exact hi (hvi.trans hz)
      have hj' : intervalValue (rightConeIntervalSimplex n)
          ((finalAdjoinHom f).toOrderHom.uliftMap j.as) ≠ 0 := by
        intro hz
        exact hj (hvj.trans hz)
      rw [coherentArrowMap_right_right C _ _ i j hi hj,
        coherentArrowMap_right_right C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).toOrderHom.uliftMap).obj j) hi' hj']
      have hmap_i : intervalValue
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) i.as ≠ 0 := by
        intro hz
        exact hi (by simpa only [rightConeIntervalSimplex_map f] using hz)
      have hmap_j : intervalValue
          ((Δ[1] : SSet.{u}).map (finalAdjoinHom f).op
            (rightConeIntervalSimplex n)) j.as ≠ 0 := by
        intro hz
        exact hj (by simpa only [rightConeIntervalSimplex_map f] using hz)
      have hg := coherentArrowMap_map C (finalAdjoinHom f).op
        ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
        (rightConeIntervalSimplex n) i j
      rw [coherentArrowMap_right_right C _ _ i j hmap_i hmap_j,
        coherentArrowMap_right_right C _ _
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).op.unop.toOrderHom.uliftMap).obj i)
          ((CategoryTheory.SimplicialThickening.functor
            (finalAdjoinHom f).op.unop.toOrderHom.uliftMap).obj j) hi' hj'] at hg
      simpa only [Category.assoc, eqToHom_trans, Quiver.Hom.unop_op,
        hobj_i, hobj_j, hobj_i_map, hobj_j_map, hHom, hHom_map] using hg

/-- Normalize the cone used after passing to the opposite simplicial set. -/
def rightConeUnderStdSimplexIso (n : ℕ) :
    simplicialJoin (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≅
      (Δ[n + 1] : SSet.{u}) :=
  simplicialJoinStdSimplexIsoNat 0 n ≪≫
    SSet.stdSimplex.mapIso
      (eqToIso (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1)))

theorem simplicialJoinLeftInclusion_rightConeUnderStdSimplexIso (n : ℕ) :
    simplicialJoinLeftInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (rightConeUnderStdSimplexIso n).hom =
      SSet.stdSimplex.map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk (n + 1)) 0) := by
  unfold rightConeUnderStdSimplexIso
  rw [Iso.trans_hom, ← Category.assoc,
    simplicialJoinLeftInclusion_stdSimplex]
  change SSet.stdSimplex.map (standardJoinLeftOperator 0 n) ≫
      SSet.stdSimplex.map (eqToHom
        (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1))) = _
  rw [← Functor.map_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [standardJoinLeftOperator]

theorem simplicialJoinRightInclusion_rightConeUnderStdSimplexIso (n : ℕ) :
    simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        (rightConeUnderStdSimplexIso n).hom =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2))) := by
  unfold rightConeUnderStdSimplexIso
  rw [Iso.trans_hom, ← Category.assoc,
    simplicialJoinRightInclusion_stdSimplex]
  change SSet.stdSimplex.map (standardJoinRightOperator 0 n) ≫
      SSet.stdSimplex.map (eqToHom
        (congrArg SimplexCategory.mk (by omega : 0 + n + 1 = n + 1))) = _
  rw [← Functor.map_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext i
  simp [standardJoinRightOperator, SimplexCategory.δ]
  omega

/-- The final vertex of the right cone is the target vertex of the enriched arrow. -/
theorem coherentArrowRightConeSimplex_final_vertex {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (CategoryTheory.SimplicialNerve C).map
        (SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk (n + 1)) (Fin.last (n + 1))).op
        (coherentArrowRightConeSimplex C h) =
      coherentNerveVertex C Y := by
  let h' := (X ⟶[SSet] Y).map (rightConeProjection n).op h
  let s : (Δ[1] : SSet.{u}).obj
      (op (SimplexCategory.mk (n + 1))) := rightConeIntervalSimplex n
  let f := SimplexCategory.const (SimplexCategory.mk 0)
    (SimplexCategory.mk (n + 1)) (Fin.last (n + 1))
  let hs : ((X ⟶[SSet] Y) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1))) := (h', s)
  have hn := (coherentArrowCylinderMap C (X := X) (Y := Y)).naturality_apply
    f.op hs
  change coherentArrowSimplex C ((X ⟶[SSet] Y).map f.op h')
      ((Δ[1] : SSet.{u}).map f.op s) =
    (CategoryTheory.SimplicialNerve C).map f.op
      (coherentArrowRightConeSimplex C h) at hn
  rw [← hn]
  have hsone : (Δ[1] : SSet.{u}).map f.op s = intervalOneSimplex 0 := by
    apply SSet.stdSimplex.ext
    intro i
    change finalStepOrderHom n (f.toOrderHom i) = 1
    simp [f, finalStepOrderHom, SimplexCategory.const]
  rw [hsone]
  have hz := (coherentArrowSimplex_intervalOne C
    ((X ⟶[SSet] Y).map f.op h')).symm
  have hc : (SSet.const (X := (Δ[0] : SSet.{u}))
      (coherentNerveVertex C Y)).app
        (op (SimplexCategory.mk 0)) (zeroSimplex 0) =
      coherentNerveVertex C Y := by
    change SSet.yonedaEquiv
      (SSet.const (X := (Δ[0] : SSet.{u}))
        (coherentNerveVertex C Y)) = coherentNerveVertex C Y
    exact SSet.yonedaEquiv_const _
  exact hz.trans hc

/-- Deleting the final vertex of a right cone recovers the constant source vertex. -/
theorem coherentArrowRightConeSimplex_initial_face {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (CategoryTheory.SimplicialNerve C).map
        (SimplexCategory.δ (Fin.last (n + 1))).op
        (coherentArrowRightConeSimplex C h) =
      (SSet.const (X := (Δ[0] : SSet.{u}))
        (coherentNerveVertex C X)).app
        (op (SimplexCategory.mk n)) (zeroSimplex n) := by
  let h' := (X ⟶[SSet] Y).map (rightConeProjection n).op h
  let s : (Δ[1] : SSet.{u}).obj
      (op (SimplexCategory.mk (n + 1))) := rightConeIntervalSimplex n
  let f := SimplexCategory.δ (Fin.last (n + 1))
  let hs : (Δ[1] : SSet.{u}).map f.op s = intervalZeroSimplex n := by
    apply SSet.stdSimplex.ext
    intro i
    change finalStepOrderHom n (f.toOrderHom i) = 0
    have hi : i.val ≤ n := by
      exact (Fin.le_last i)
    simp [f, finalStepOrderHom, SimplexCategory.δ, hi]
    omega
  let hpair : ((X ⟶[SSet] Y) ⊗ (Δ[1] : SSet.{u})).obj
      (op (SimplexCategory.mk (n + 1))) := (h', s)
  have hn := (coherentArrowCylinderMap C (X := X) (Y := Y)).naturality_apply
    f.op hpair
  change coherentArrowSimplex C ((X ⟶[SSet] Y).map f.op h')
      ((Δ[1] : SSet.{u}).map f.op s) =
    (CategoryTheory.SimplicialNerve C).map f.op
      (coherentArrowRightConeSimplex C h) at hn
  have hδσ : f ≫ rightConeProjection n = 𝟙 _ := by
    apply SimplexCategory.Hom.ext
    ext i
    simp [f, rightConeProjection, SimplexCategory.δ, SimplexCategory.σ]
  have hh : (X ⟶[SSet] Y).map f.op h' = h := by
    change ((X ⟶[SSet] Y).map f.op)
        (((X ⟶[SSet] Y).map (rightConeProjection n).op) h) = h
    have hm := congrArg (fun g ↦ g h)
      ((X ⟶[SSet] Y).map_comp (rightConeProjection n).op f.op)
    rw [← op_comp, hδσ] at hm
    simpa using hm.symm
  rw [← hn, hs, hh]
  exact (coherentArrowSimplex_intervalZero C h).symm

theorem rightConeUnderStdSimplexIso_map
    {m n : ℕ} (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m)) :
    simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.rev.map f.unop)) ≫
        (rightConeUnderStdSimplexIso n).hom =
      (rightConeUnderStdSimplexIso m).hom ≫
        SSet.stdSimplex.map
          (SimplexCategory.rev.map (finalAdjoinHom f.unop)) := by
  unfold rightConeUnderStdSimplexIso simplicialJoinStdSimplexIsoNat
    simplicialJoinStdSimplexIso
  rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc]
  have hid : SSet.stdSimplex.map
        (SimplexCategory.Hom.mk OrderHom.id :
          SimplexCategory.mk 0 ⟶ SimplexCategory.mk 0) =
      SSet.stdSimplex.map (𝟙 (SimplexCategory.mk 0)) := by
    congr 1

  rw [← SSet.stdSimplex.map_id]
  rw [hid]
  rw [← Category.assoc]
  have hraw :
      simplicialJoinMap
          (SSet.stdSimplex.map (𝟙 (SimplexCategory.mk 0)))
          (SSet.stdSimplex.map (SimplexCategory.rev.map f.unop)) ≫
        (simplicialJoinStdSimplexIsoRaw (SimplexCategory.mk 0)
          (SimplexCategory.mk n)).hom =
      (simplicialJoinStdSimplexIsoRaw (SimplexCategory.mk 0)
          (SimplexCategory.mk m)).hom ≫
        forgetAugmentation.map
          (CategoryTheory.uliftYoneda.map
            (AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk 0)) ⊗ₘ
              AugmentedSimplexCategory.inclusion.map
                (SimplexCategory.rev.map f.unop))) := by
    convert (simplicialJoinStdSimplexIsoRaw_naturality
      (𝟙 (SimplexCategory.mk 0)) (SimplexCategory.rev.map f.unop)) using 1 <;>
      rfl
  have hinc :
      AugmentedSimplexCategory.inclusion.map
          (AugmentedSimplexCategory.tensorHomOf
            (𝟙 (SimplexCategory.mk 0))
            (SimplexCategory.rev.map f.unop)) =
        AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk 0)) ⊗ₘ
          AugmentedSimplexCategory.inclusion.map
            (SimplexCategory.rev.map f.unop) := by
    rfl
  rw [← hinc] at hraw
  rw [hraw]
  simp only [Category.assoc]
  have hnat := forgetAugmentationULiftYonedaInclusionIso_naturality.{u}
    (f := AugmentedSimplexCategory.tensorHomOf
      (𝟙 (SimplexCategory.mk 0)) (SimplexCategory.rev.map f.unop))
  have hnat' :
      forgetAugmentation.map
          (CategoryTheory.uliftYoneda.map
            (AugmentedSimplexCategory.inclusion.map
              (AugmentedSimplexCategory.tensorHomOf
                (𝟙 (SimplexCategory.mk 0))
                (SimplexCategory.rev.map f.unop)))) ≫
        (forgetAugmentationULiftYonedaInclusionIso
          (AugmentedSimplexCategory.tensorObjOf (SimplexCategory.mk 0)
            (SimplexCategory.mk n))).hom =
      (forgetAugmentationULiftYonedaInclusionIso
          (AugmentedSimplexCategory.tensorObjOf (SimplexCategory.mk 0)
            (SimplexCategory.mk m))).hom ≫
        SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf
            (𝟙 (SimplexCategory.mk 0))
            (SimplexCategory.rev.map f.unop)) := by
    simpa only [SimplexCategory.rev] using hnat
  have hfinal :
      SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf
            (𝟙 (SimplexCategory.mk 0))
            (SimplexCategory.rev.map f.unop)) ≫
        (SSet.stdSimplex.mapIso
          (eqToIso (congrArg SimplexCategory.mk
            (by omega : 0 + n + 1 = n + 1)))).hom =
      (SSet.stdSimplex.mapIso
          (eqToIso (congrArg SimplexCategory.mk
            (by omega : 0 + m + 1 = m + 1)))).hom ≫
        SSet.stdSimplex.map
          (SimplexCategory.rev.map (finalAdjoinHom f.unop)) := by
    change SSet.stdSimplex.map
          (AugmentedSimplexCategory.tensorHomOf
            (𝟙 (SimplexCategory.mk 0))
            (SimplexCategory.rev.map f.unop)) ≫
        SSet.stdSimplex.map
          (eqToHom (congrArg SimplexCategory.mk
            (by omega : 0 + n + 1 = n + 1))) =
      SSet.stdSimplex.map
          (eqToHom (congrArg SimplexCategory.mk
            (by omega : 0 + m + 1 = m + 1))) ≫
        SSet.stdSimplex.map
          (SimplexCategory.rev.map (finalAdjoinHom f.unop))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply SimplexCategory.Hom.ext
    ext i
    simp only [SimplexCategory.rev, Quiver.Hom.unop_op,
      SimplexCategory.len_mk] at *
    let k : Fin ((SimplexCategory.mk 0).len + 1 +
        ((SimplexCategory.mk m).len + 1)) :=
      i.cast (by simp [SimplexCategory.rev]; omega)
    have hik : i = k.cast (by simp [SimplexCategory.rev]; omega) := rfl
    rw [hik]
    dsimp [AugmentedSimplexCategory.tensorHomOf]
    simp only [SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe,
      SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
      Fin.castOrderIso_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_inj]
    simp [Function.comp_def]
    cases k using Fin.addCases with
    | left k =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      conv_lhs =>
        change (Fin.addCases _ _
          (Fin.castAdd (m + 1) (0 : Fin 1)) : Fin _)
        rw [Fin.addCases_left]
      simp [SimplexCategory.rev, SimplexCategory.rev_map_apply,
        finalAdjoinHom, finalAdjoinOrderHom,
        AugmentedSimplexCategory.tensorObjOf,
        Fin.rev_castAdd, Fin.rev_addNat, Fin.rev_succ, Fin.val_rev,
        Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
        Fin.castOrderIso_apply, Fin.cast_rev, Fin.cast]
      change 0 = n + 1 -
        ↑(finalAdjoinOrderHom f.unop (Fin.last (m + 1)))
      simp [finalAdjoinOrderHom]
    | right k =>
      change Fin (m + 1) at k
      conv_lhs =>
        change (Fin.addCases _ _
          (Fin.natAdd 1 k) : Fin _)
        rw [Fin.addCases_right]
      simp [SimplexCategory.rev, SimplexCategory.rev_map_apply,
        finalAdjoinHom, finalAdjoinOrderHom,
        AugmentedSimplexCategory.tensorObjOf,
        Fin.rev_castAdd, Fin.rev_addNat, Fin.rev_succ, Fin.val_rev,
        Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
        Fin.castOrderIso_apply, Fin.cast_rev, Fin.cast]
      have hklt : k.val ≤ m := by simpa using k.isLt
      let q : Fin (m + 2) := ⟨1 + k.val, by omega⟩
      change 1 + (n - ↑(f.unop.toOrderHom k.rev)) =
        n + 1 -
          ↑(finalAdjoinOrderHom f.unop q.rev)
      dsimp [finalAdjoinOrderHom]
      split_ifs with hq
      · have hv := congrArg Fin.val hq
        simp [q, Fin.val_rev] at hv
        omega
      · have hpred :
            (Fin.last m).predAbove q.rev = k.rev := by
          have hqrev : q.rev = k.rev.castSucc := by
            apply Fin.ext
            simp [q, Fin.val_rev]
            have hkrev := Fin.rev_add_cast k
            omega
          rw [hqrev, Fin.predAbove_last_castSucc]
        rw [hpred]
        have hf := (f.unop.toOrderHom k.rev).isLt
        have hf' : (f.unop.toOrderHom k.rev).val ≤ n := by
          simpa using hf
        simp only [Fin.coe_castSucc]
        omega
  have hpost := congrArg (fun k ↦
      (simplicialJoinStdSimplexIsoRaw (SimplexCategory.mk 0)
        (SimplexCategory.mk m)).hom ≫ k ≫
        (SSet.stdSimplex.mapIso
          (eqToIso (congrArg SimplexCategory.mk
            (by omega : 0 + n + 1 = n + 1)))).hom) hnat'
  simp only [Category.assoc] at hpost
  rw [hfinal] at hpost
  simpa only [Category.assoc] using hpost

/-- The same endpoint viewed as a vertex of the opposite coherent nerve. -/
def coherentNerveOppositeVertex (Y : C) :
    (CategoryTheory.SimplicialNerve C).op _⦋0⦌ :=
  SSet.opObjEquiv.symm (coherentNerveVertex C Y)

/-- The right cone, viewed as a fixed-base cone in the opposite coherent nerve. -/
def coherentArrowRightConeUnderSliceJoinMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    simplicialJoin (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶
      (CategoryTheory.SimplicialNerve C).op :=
  (rightConeUnderStdSimplexIso n).hom ≫
    SSet.yonedaEquiv.symm
      (SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C h))

theorem coherentArrowRightConeUnderSliceJoinMap_left
    {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    simplicialJoinLeftInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        coherentArrowRightConeUnderSliceJoinMap C h =
      SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y) := by
  unfold coherentArrowRightConeUnderSliceJoinMap
  rw [← Category.assoc,
    simplicialJoinLeftInclusion_rightConeUnderStdSimplexIso]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm,
    Equiv.apply_symm_apply]
  rw [SSet.op_map]
  have hconst :
      SimplexCategory.rev.map
          ((SimplexCategory.const (SimplexCategory.mk 0)
            (SimplexCategory.mk (n + 1)) 0).op.unop) =
        SimplexCategory.const (SimplexCategory.mk 0)
          (SimplexCategory.mk (n + 1)) (Fin.last (n + 1)) := by
    apply SimplexCategory.Hom.ext
    ext i
    rfl
  rw [hconst]
  exact congrArg SSet.opObjEquiv.symm
    (coherentArrowRightConeSimplex_final_vertex C h)

theorem coherentArrowRightConeUnderSliceJoinMap_map
    {m n : ℕ} {X Y : C}
    (f : op (SimplexCategory.mk n) ⟶ op (SimplexCategory.mk m))
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    coherentArrowRightConeUnderSliceJoinMap C
        ((X ⟶[SSet] Y).map f h) =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.rev.map f.unop)) ≫
        coherentArrowRightConeUnderSliceJoinMap C h := by
  unfold coherentArrowRightConeUnderSliceJoinMap
  rw [← Category.assoc, rightConeUnderStdSimplexIso_map]
  rw [Category.assoc]
  change (rightConeUnderStdSimplexIso m).hom ≫
      SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm
          (coherentArrowRightConeSimplex C
            ((X ⟶[SSet] Y).map f h))) =
    (rightConeUnderStdSimplexIso m).hom ≫
      (SSet.stdSimplex.map
          (SimplexCategory.rev.map (finalAdjoinHom f.unop)) ≫
        SSet.yonedaEquiv.symm
          (SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C h)))
  congr 1
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_symm_naturality_left]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [SSet.op_map]
  apply congrArg SSet.opObjEquiv.symm
  simp only [Quiver.Hom.unop_op, SimplexCategory.rev_map_rev_map,
    Equiv.apply_symm_apply]
  change coherentArrowRightConeSimplex C ((X ⟶[SSet] Y).map f h) =
    (CategoryTheory.SimplicialThickening.functor
        (finalAdjoinHom f.unop).toOrderHom.uliftMap).comp
      (E := C) SSet (coherentArrowRightConeSimplex C h)
  exact (coherentArrowRightConeSimplex_map C f.unop h).symm

/-- The degreewise over-slice simplex carried by a right-cone Hom simplex. -/
def coherentArrowRightConeUnderSliceMap {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (Δ[n] : SSet.{u}) ⟶
      underSlice (CategoryTheory.SimplicialNerve C).op
        (coherentNerveOppositeVertex C Y) := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj
    (CategoryTheory.SimplicialNerve C).op
  let a := emptyAugmentation.{u}.map
    (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
  let φ := fixedBaseDayConvolutionMapOfJoin
    (coherentArrowRightConeUnderSliceJoinMap C h)
    (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
    (coherentArrowRightConeUnderSliceJoinMap_left C h)
  exact (relativeDaySliceOverMapFixedBaseEquiv F G (Δ[n] : SSet.{u}) a).symm φ

theorem coherentArrowRightConeUnderSliceMap_cone {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    coherentArrowRightConeUnderSliceMap C h ≫
        underSliceProjection (CategoryTheory.SimplicialNerve C).op
          (coherentNerveOppositeVertex C Y) =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
        coherentArrowRightConeUnderSliceJoinMap C h := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj
    (CategoryTheory.SimplicialNerve C).op
  let a := emptyAugmentation.{u}.map
    (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
  let φ := fixedBaseDayConvolutionMapOfJoin
    (coherentArrowRightConeUnderSliceJoinMap C h)
    (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
    (coherentArrowRightConeUnderSliceJoinMap_left C h)
  rw [underSliceProjection_comp_eq_fixedBaseCone]
  dsimp only [coherentArrowRightConeUnderSliceMap]
  rw [Equiv.apply_symm_apply]
  dsimp only [φ, fixedBaseDayConvolutionMapOfJoin]
  change simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
      forgetAugmentation.map
        (augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})
          (CategoryTheory.SimplicialNerve C).op
          (coherentArrowRightConeUnderSliceJoinMap C h)) = _
  rw [forgetAugmentation_augmentedJoinMapOfUnderlying]

theorem rightCone_augmentedJoinMapOfUnderlying_precomp
    {K K' L L' Q : SSet.{u}} (f : K' ⟶ K) (g : L' ⟶ L)
    (ψ : simplicialJoin K L ⟶ Q) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L')
    augmentedJoinMapOfUnderlying K' L' Q
        (simplicialJoinMap f g ≫ ψ) =
      CategoryTheory.MonoidalCategory.DayConvolution.map
          (emptyAugmentation.{u}.map f) (emptyAugmentation.{u}.map g) ≫
        augmentedJoinMapOfUnderlying K L Q ψ := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L')
  apply augmentedMapToEmptyAugmentation_ext
  rw [Functor.map_comp,
    forgetAugmentation_augmentedJoinMapOfUnderlying,
    forgetAugmentation_augmentedJoinMapOfUnderlying]
  rfl

def coherentArrowRightConeOverSliceSimplex {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (overSlice (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C Y)).obj (op (SimplexCategory.mk n)) := by
  exact SSet.opObjEquiv.symm
    (SSet.yonedaEquiv (coherentArrowRightConeUnderSliceMap C h))

noncomputable def coherentArrowRightConePointMap {X Y : C} :
    (X ⟶[SSet] Y) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from (X ⟶[SSet] Y)

theorem coherentArrowRightConeOverSliceProjection_apply {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    (overSliceProjection (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C Y)).app (op (SimplexCategory.mk n))
        (coherentArrowRightConeOverSliceSimplex C h) =
      (SSet.const (X := (Δ[0] : SSet.{u}))
        (coherentNerveVertex C X)).app
        (op (SimplexCategory.mk n)) (zeroSimplex n) := by
  unfold overSliceProjection coherentArrowRightConeOverSliceSimplex
  change (ConcreteCategory.hom
      (((SSet.opFunctorCompOpFunctorIso.app
        (CategoryTheory.SimplicialNerve C)).hom.app
          (op (SimplexCategory.mk n)))))
      (SSet.opObjEquiv.symm
        ((ConcreteCategory.hom
          ((underSliceProjection (CategoryTheory.SimplicialNerve C).op
            (coherentNerveOppositeVertex C Y)).app
              (op (SimplexCategory.mk n))))
          (SSet.yonedaEquiv
            (coherentArrowRightConeUnderSliceMap C h)))) = _
  have hc := congrArg (fun k ↦
      k.app (op (SimplexCategory.mk n)) (identitySimplex n))
    (coherentArrowRightConeUnderSliceMap_cone C h)
  change (ConcreteCategory.hom
      ((underSliceProjection (CategoryTheory.SimplicialNerve C).op
        (coherentNerveOppositeVertex C Y)).app
        (op (SimplexCategory.mk n))))
      (SSet.yonedaEquiv
        (coherentArrowRightConeUnderSliceMap C h)) =
      (ConcreteCategory.hom
        ((simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫
          coherentArrowRightConeUnderSliceJoinMap C h).app
          (op (SimplexCategory.mk n))) (identitySimplex n)) at hc
  rw [hc]
  unfold coherentArrowRightConeUnderSliceJoinMap
  rw [← Category.assoc,
    simplicialJoinRightInclusion_rightConeUnderStdSimplexIso]
  rw [SSet.yonedaEquiv_symm_naturality_left]
  have hid : identitySimplex n =
      SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := rfl
  rw [hid, SSet.yonedaEquiv_symm_app_id]
  rw [SSet.op_map]
  have hδ :
      SimplexCategory.rev.map (SimplexCategory.δ (0 : Fin (n + 2))) =
        SimplexCategory.δ (Fin.last (n + 1)) := by
    simpa using (SimplexCategory.rev_map_δ (n := n)
      (0 : Fin (n + 2)))
  change ((CategoryTheory.SimplicialNerve C).map
      (SimplexCategory.rev.map (SimplexCategory.δ (0 : Fin (n + 2)))).op
      (coherentArrowRightConeSimplex C h)) = _
  rw [hδ]
  exact coherentArrowRightConeSimplex_initial_face C h

/-- The degreewise right-cone construction is simplicially natural. -/
def coherentArrowRightConeOverSliceMap {X Y : C} :
    (X ⟶[SSet] Y) ⟶
      overSlice (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C Y) where
  app U := by
    rcases U with ⟨⟨n⟩⟩
    exact ↾fun h ↦ coherentArrowRightConeOverSliceSimplex C h
  naturality U V f := by
    rcases U with ⟨⟨n⟩⟩
    rcases V with ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro h
    change coherentArrowRightConeOverSliceSimplex C
        ((X ⟶[SSet] Y).map f h) =
      ((underSlice (CategoryTheory.SimplicialNerve C).op
        (coherentNerveOppositeVertex C Y)).op).map f
        (coherentArrowRightConeOverSliceSimplex C h)
    apply SSet.opObjEquiv.injective
    rw [SSet.op_map]
    simp only [Equiv.apply_symm_apply]
    apply SSet.yonedaEquiv.symm.injective
    change SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv
          (coherentArrowRightConeUnderSliceMap C
            ((X ⟶[SSet] Y).map f h))) =
      SSet.yonedaEquiv.symm
        ((underSlice (CategoryTheory.SimplicialNerve C).op
          (coherentNerveOppositeVertex C Y)).map
          (SimplexCategory.rev.map f.unop).op
          (SSet.yonedaEquiv
            (coherentArrowRightConeUnderSliceMap C h)))
    simp only [Equiv.symm_apply_apply]
    rw [← SSet.yonedaEquiv_symm_naturality_left]
    simp only [Equiv.symm_apply_apply]
    let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
    let G := emptyAugmentation.{u}.obj
      (CategoryTheory.SimplicialNerve C).op
    let a := emptyAugmentation.{u}.map
      (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
    let g : (Δ[m] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) :=
      SSet.stdSimplex.map (SimplexCategory.rev.map f.unop)
    letI := augmentedDayConvolution F
      (emptyAugmentation.{u}.obj (Δ[m] : SSet.{u}))
    letI := augmentedDayConvolution F
      (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
    apply (relativeDaySliceOverMapFixedBaseEquiv F G (Δ[m] : SSet.{u}) a).injective
    dsimp only [coherentArrowRightConeUnderSliceMap]
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    have hpre := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst F G a g
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
        (emptyAugmentation.{u}.obj (CategoryTheory.SimplicialNerve C).op)
        (Δ[n] : SSet.{u}) a).symm
        (fixedBaseDayConvolutionMapOfJoin
          (coherentArrowRightConeUnderSliceJoinMap C h)
          (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
          (coherentArrowRightConeUnderSliceJoinMap_left C h)))
    rw [hpre]
    rw [Equiv.apply_symm_apply]
    dsimp only [fixedBaseDayConvolutionMapOfJoin]
    dsimp only [FixedBaseDayConvolutionMap, augmentedDayTensorLeft]
    simp only [id_eq]
    change augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) (Δ[m] : SSet.{u})
        (CategoryTheory.SimplicialNerve C).op
        (coherentArrowRightConeUnderSliceJoinMap C ((X ⟶[SSet] Y).map f h)) =
      CategoryTheory.MonoidalCategory.DayConvolution.map
          (𝟙 F)
          (emptyAugmentation.map g) ≫
          augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})
          (CategoryTheory.SimplicialNerve C).op
          (coherentArrowRightConeUnderSliceJoinMap C h)
    rw [← emptyAugmentation.map_id]
    rw [← rightCone_augmentedJoinMapOfUnderlying_precomp
      (𝟙 (Δ[0] : SSet.{u})) g
      (coherentArrowRightConeUnderSliceJoinMap C h)]
    rw [coherentArrowRightConeUnderSliceJoinMap_map C f h]

theorem coherentArrowRightConeOverSliceProjection_map {X Y : C} :
    coherentArrowRightConeOverSliceMap (C := C) (X := X) (Y := Y) ≫
        overSliceProjection (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C Y) =
      coherentArrowRightConePointMap (C := C) (X := X) (Y := Y) ≫
        endpointVertex (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C X) := by
  apply NatTrans.ext
  funext U
  rcases U with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro h
  change (overSliceProjection (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C Y)).app (op (SimplexCategory.mk n))
      (coherentArrowRightConeOverSliceSimplex C h) = _
  rw [coherentArrowRightConeOverSliceProjection_apply]
  change (SSet.const (coherentNerveVertex C X)).app
      (op (SimplexCategory.mk n)) (zeroSimplex n) =
    (SSet.const (coherentNerveVertex C X)).app
      (op (SimplexCategory.mk n))
      ((coherentArrowRightConePointMap C).app
        (op (SimplexCategory.mk n)) h)
  apply congrArg
    (fun z : (Δ[0] : SSet.{u}).obj (op (SimplexCategory.mk n)) ↦
      (SSet.const (coherentNerveVertex C X)).app
        (op (SimplexCategory.mk n)) z)
  exact Subsingleton.elim _ _

noncomputable def coherentArrowRightMappingSpaceMap {X Y : C} :
    (X ⟶[SSet] Y) ⟶
      rightMappingSpace (CategoryTheory.SimplicialNerve C)
        (coherentNerveVertex C X) (coherentNerveVertex C Y) :=
  CategoryTheory.Limits.pullback.lift
    (coherentArrowRightConeOverSliceMap C)
    (coherentArrowRightConePointMap C)
    (coherentArrowRightConeOverSliceProjection_map C)

@[reassoc (attr := simp)]
theorem coherentArrowRightMappingSpaceMap_fst {X Y : C} :
    coherentArrowRightMappingSpaceMap C ≫
        rightMappingSpaceToOverSlice (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C X) (coherentNerveVertex C Y) =
      coherentArrowRightConeOverSliceMap C := by
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem coherentArrowRightMappingSpaceMap_snd {X Y : C} :
    coherentArrowRightMappingSpaceMap C ≫
        rightMappingSpaceToPoint (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C X) (coherentNerveVertex C Y) =
      coherentArrowRightConePointMap C := by
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

private lemma rightConeExtraction_eqToHom_app_heq
    {A B : SSet.{u}} (e : A = B) (U : SimplexCategoryᵒᵖ) (x : A.obj U) :
    HEq ((eqToHom e).app U x) x := by
  cases e
  rfl

/-- Evaluating the first-to-last enriched path of a right-cone simplex recovers its Hom
simplex.  The heterogeneous equality records the object transports at the two endpoints. -/
theorem rightConeExtraction_heq {n : ℕ} {X Y : C}
    (h : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))) :
    HEq (((coherentArrowRightConeSimplex C h).map
      (extractionFirst (n := n)) (extractionLast (n := n))).app _
        (extractionPathSimplex n)) h := by
  dsimp [coherentArrowRightConeSimplex]
  change HEq
    ((coherentArrowMap C
      ((X ⟶[SSet] Y).map (rightConeProjection n).op h)
      (rightConeIntervalSimplex n)
      (extractionFirst (n := n)) (extractionLast (n := n))).app _
        (extractionPathSimplex n)) h
  have hzero : intervalValue (rightConeIntervalSimplex n)
      (extractionFirst (n := n)).as = 0 := by rfl
  have hone : intervalValue (rightConeIntervalSimplex n)
      (extractionLast (n := n)).as ≠ 0 := by
    change finalStepOrderHom n (Fin.last (n + 1)) ≠ 0
    rw [show finalStepOrderHom n (Fin.last (n + 1)) = 1 by
      simp [finalStepOrderHom]]
    omega
  rw [coherentArrowMap_left_right C _ _ _ _ hzero hone]
  rw [coherentHom_yoneda_map]
  simp only [Category.assoc, NatTrans.comp_app, comp_apply]
  have hzeroeq : hzero = rfl := Subsingleton.elim _ _
  rw [hzeroeq]
  have hx := lastZeroSimplexMap_extraction n
  change (SSet.stdSimplex.map (rightConeProjection n).op.unop).app _
      ((lastZeroSimplexMap (rightConeIntervalSimplex n)
        (extractionFirst (n := n)) (extractionLast (n := n)) rfl).app _
          (extractionPathSimplex n)) = identitySimplex n at hx
  rw [hx]
  have hid : identitySimplex n = SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := rfl
  rw [hid, SSet.yonedaEquiv_symm_app_id]
  exact rightConeExtraction_eqToHom_app_heq _ _ h

/-- The coherent right-cone simplex is degreewise injective. -/
theorem coherentArrowRightConeSimplex_injective {n : ℕ} {X Y : C}
    {h₁ h₂ : (X ⟶[SSet] Y).obj (op (SimplexCategory.mk n))}
    (hab : coherentArrowRightConeSimplex C h₁ =
      coherentArrowRightConeSimplex C h₂) :
    h₁ = h₂ := by
  have h₁e := rightConeExtraction_heq C h₁
  have h₂e := rightConeExtraction_heq C h₂
  rw [← hab] at h₂e
  exact eq_of_heq (h₁e.symm.trans h₂e)

/-- The all-dimensional right mapping-space comparison is a simplicial monomorphism. -/
noncomputable instance coherentArrowRightMappingSpaceMap_mono {X Y : C} :
    Mono (coherentArrowRightMappingSpaceMap C (X := X) (Y := Y)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro a b hab
  rcases U with ⟨⟨n⟩⟩
  have hslice := congrArg
    ((rightMappingSpaceToOverSlice (CategoryTheory.SimplicialNerve C)
      (coherentNerveVertex C X) (coherentNerveVertex C Y)).app
        (op (SimplexCategory.mk n))) hab
  have hslice' :
      coherentArrowRightConeOverSliceSimplex C a =
        coherentArrowRightConeOverSliceSimplex C b := by
    have hmap :
        ((coherentArrowRightMappingSpaceMap C ≫
          rightMappingSpaceToOverSlice (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C X) (coherentNerveVertex C Y)).app
          (op (SimplexCategory.mk n))) =
          (coherentArrowRightConeOverSliceMap C).app
            (op (SimplexCategory.mk n)) := NatTrans.congr_app
      (coherentArrowRightMappingSpaceMap_fst (C := C) (X := X) (Y := Y))
      (op (SimplexCategory.mk n))
    have hmapa := congrArg
      (fun k : (X ⟶[SSet] Y).obj
            (op (SimplexCategory.mk n)) ⟶
          (overSlice (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C Y)).obj
            (op (SimplexCategory.mk n)) ↦
        (ConcreteCategory.hom k) a) hmap
    have hmapb := congrArg
      (fun k : (X ⟶[SSet] Y).obj
            (op (SimplexCategory.mk n)) ⟶
          (overSlice (CategoryTheory.SimplicialNerve C)
            (coherentNerveVertex C Y)).obj
            (op (SimplexCategory.mk n)) ↦
        (ConcreteCategory.hom k) b) hmap
    exact hmapa.symm.trans (hslice.trans hmapb)
  have hop :
      SSet.yonedaEquiv (coherentArrowRightConeUnderSliceMap C a) =
        SSet.yonedaEquiv (coherentArrowRightConeUnderSliceMap C b) := by
    let yOpp := coherentNerveOppositeVertex C Y
    have hop' := congrArg
      (fun z : (overSlice (CategoryTheory.SimplicialNerve C)
          (coherentNerveVertex C Y)).obj (op (SimplexCategory.mk n)) ↦
        SSet.opObjEquiv (X := underSlice (CategoryTheory.SimplicialNerve C).op yOpp)
          (n := op (SimplexCategory.mk n)) z) hslice'
    change SSet.yonedaEquiv (coherentArrowRightConeUnderSliceMap C a) =
      SSet.yonedaEquiv (coherentArrowRightConeUnderSliceMap C b) at hop'
    exact hop'
  have hunder : coherentArrowRightConeUnderSliceMap C a =
      coherentArrowRightConeUnderSliceMap C b :=
    SSet.yonedaEquiv.injective hop
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj (CategoryTheory.SimplicialNerve C).op
  let a₀ := emptyAugmentation.{u}.map
    (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
  let e := relativeDaySliceOverMapFixedBaseEquiv F G
    (Δ[n] : SSet.{u}) a₀
  have hphi :
      fixedBaseDayConvolutionMapOfJoin
          (coherentArrowRightConeUnderSliceJoinMap C a)
          (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
          (coherentArrowRightConeUnderSliceJoinMap_left C a) =
        fixedBaseDayConvolutionMapOfJoin
          (coherentArrowRightConeUnderSliceJoinMap C b)
          (SSet.yonedaEquiv.symm (coherentNerveOppositeVertex C Y))
          (coherentArrowRightConeUnderSliceJoinMap_left C b) := by
    apply e.symm.injective
    simpa only [coherentArrowRightConeUnderSliceMap, e,
      Equiv.apply_symm_apply] using hunder
  have hjoin : coherentArrowRightConeUnderSliceJoinMap C a =
      coherentArrowRightConeUnderSliceJoinMap C b := by
    have hfirst := congrArg
      (fun φ => forgetAugmentation.{u}.map φ.1) hphi
    dsimp [fixedBaseDayConvolutionMapOfJoin] at hfirst
    change forgetAugmentation.{u}.map
        (augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})
          (CategoryTheory.SimplicialNerve C).op
          (coherentArrowRightConeUnderSliceJoinMap C a)) =
      forgetAugmentation.{u}.map
        (augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u})
          (CategoryTheory.SimplicialNerve C).op
          (coherentArrowRightConeUnderSliceJoinMap C b)) at hfirst
    rw [forgetAugmentation_augmentedJoinMapOfUnderlying,
      forgetAugmentation_augmentedJoinMapOfUnderlying] at hfirst
    exact hfirst
  have hraw :
      SSet.yonedaEquiv.symm
          (SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C a)) =
        SSet.yonedaEquiv.symm
          (SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C b)) := by
    apply (cancel_epi (rightConeUnderStdSimplexIso n).hom).1
    simpa only [coherentArrowRightConeUnderSliceJoinMap] using hjoin
  have hconeOpp :
      SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C a) =
        SSet.opObjEquiv.symm (coherentArrowRightConeSimplex C b) :=
    SSet.yonedaEquiv.symm.injective hraw
  have hcone : coherentArrowRightConeSimplex C a =
      coherentArrowRightConeSimplex C b :=
    SSet.opObjEquiv.symm.injective hconeOpp
  exact coherentArrowRightConeSimplex_injective C hcone

end LeanLCAExactChallenge.Infinity.CoherentNerveMappingComparison
