/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitney

/-!
# Alexander--Whitney unit coherence

This file proves the left and right unit laws for the Alexander--Whitney chain map, first for
alternating face-map complexes and then for normalized Moore complexes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

abbrev alternatingAlexanderWhitneyUnit :=
  AlternatingFaceMapComplex.ε.app
    (SimplicialObject.Augmented.const.obj (𝟙_ (ModuleCat.{0} ℤ)))

@[simp]
theorem alexanderWhitneyBack_zero_cut (n : ℕ) :
    alexanderWhitneyBack n (0 : Fin (n + 1)) = 𝟙 (SimplexCategory.mk n) := by
  ext i
  rw [alexanderWhitneyBack_apply]
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero,
    SimplexCategory.id_toOrderHom]
  simp only [Nat.zero_add]
  exact congrArg Fin.val (show OrderHom.id i = i from rfl)

@[simp]
theorem alexanderWhitneyFront_full_cut (n : ℕ) :
    alexanderWhitneyFront n ⟨n, by omega⟩ = 𝟙 (SimplexCategory.mk n) := by
  ext i
  simp

theorem alternatingAlexanderWhitney_right_unit_component
    (X : SimplicialObject (ModuleCat.{0} ℤ)) (n q : ℕ)
    (hq : n + q = n) :
    (alternatingChains X).X n ◁ alternatingAlexanderWhitneyUnit.f q ≫
        HomologicalComplex.ιTensorObj (alternatingChains X)
          ((ChainComplex.single₀ (ModuleCat ℤ)).obj (𝟙_ (ModuleCat ℤ)))
          n q n hq =
      HomologicalComplex.ιTensorObj (alternatingChains X)
        ((ChainComplex.single₀ (ModuleCat ℤ)).obj (𝟙_ (ModuleCat ℤ)))
        n 0 n (by omega) := by
  have hq_zero : q = 0 := by omega
  subst q
  simp only [alternatingAlexanderWhitneyUnit, AlternatingFaceMapComplex.ε_app_f_zero]
  change ((alternatingChains X).X n ◁ 𝟙 (𝟙_ (ModuleCat ℤ))) ≫ _ = _
  rw [whiskerLeft_id, Category.id_comp]

set_option linter.flexible false in
theorem alternatingAlexanderWhitney_left_unitality
    (X : SimplicialObject (ModuleCat.{0} ℤ)) :
    (λ_ (alternatingChains X)).inv =
      (alternatingFaceMapComplex (ModuleCat ℤ)).map (λ_ X).inv ≫
        alternatingAlexanderWhitney
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) X ≫
        (alternatingAlexanderWhitneyUnit ▷ alternatingChains X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change
    (HomologicalComplex.leftUnitor' (alternatingChains X)).inv n = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [alternatingFaceMapComplex_obj_X, ChainComplex.single₀_obj_zero,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv, id_whiskerRight, Category.id_comp,
    Functor.comp_obj, SimplicialObject.Augmented.point_obj,
    SimplicialObject.Augmented.const_obj_right, SimplicialObject.Augmented.drop_obj,
    SimplicialObject.Augmented.const_obj_left, HomologicalComplex.comp_f,
    Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj, alternatingFaceMapComplex_map_f,
    Monoidal.leftUnitor_inv_app, alternatingAlexanderWhitney_f,
    alternatingAlexanderWhitneyDegree, alternatingAlexanderWhitneySummand,
    Iso.cancel_iso_inv_left]
  erw [Preadditive.sum_comp]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simp [alternatingAlexanderWhitneyUnit, alexanderWhitneyBack_zero_cut]
  · intro p _ hp
    simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    rcases p with ⟨p, hp'⟩
    cases p with
    | zero => simp_all
    | succ p =>
      simp [alternatingAlexanderWhitneyUnit]
  · simp

set_option linter.flexible false in
theorem alternatingAlexanderWhitney_right_unitality
    (X : SimplicialObject (ModuleCat.{0} ℤ)) :
    (ρ_ (alternatingChains X)).inv =
      (alternatingFaceMapComplex (ModuleCat ℤ)).map (ρ_ X).inv ≫
        alternatingAlexanderWhitney X
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
        (alternatingChains X ◁ alternatingAlexanderWhitneyUnit) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change
    (HomologicalComplex.rightUnitor' (alternatingChains X)).inv n = _
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [alternatingFaceMapComplex_obj_X, ChainComplex.single₀_obj_zero,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv, whiskerLeft_id, Category.id_comp,
    Functor.comp_obj, SimplicialObject.Augmented.point_obj,
    SimplicialObject.Augmented.const_obj_right, HomologicalComplex.comp_f,
    Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj, alternatingFaceMapComplex_map_f,
    Monoidal.rightUnitor_inv_app, alternatingAlexanderWhitney_f,
    alternatingAlexanderWhitneyDegree, alternatingAlexanderWhitneySummand,
    Iso.cancel_iso_inv_left]
  erw [Preadditive.sum_comp]
  let last : Fin (n + 1) := ⟨n, by omega⟩
  rw [Finset.sum_eq_single last]
  · simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simp [last, alternatingAlexanderWhitneyUnit,
      alexanderWhitneyFront_full_cut]
    exact (alternatingAlexanderWhitney_right_unit_component
      X n (n - n) (by omega)).symm
  · intro p _ hp
    simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    dsimp [last] at hp
    have hp_ne : (p : ℕ) ≠ n := by
      intro hpn
      apply hp
      apply Fin.ext
      change (p : ℕ) = n
      exact hpn
    have hp_lt : (p : ℕ) < n := by omega
    have hdiff : n - (p : ℕ) ≠ 0 :=
      Nat.ne_of_gt (Nat.sub_pos_of_lt hp_lt)
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hdiff
    have heps : alternatingAlexanderWhitneyUnit.f (n - (p : ℕ)) = 0 := by
      rw [hq]
      exact AlternatingFaceMapComplex.ε_app_f_succ _ q
    erw [heps]
    simp
  · simp

theorem normalizedAlexanderWhitney_left_unitality
    (X : SimplicialObject (ModuleCat.{0} ℤ)) :
    (λ_ (zModuleDoldKanEquivalence.functor.obj X)).inv =
      zModuleDoldKanEquivalence.functor.map (λ_ X).inv ≫
        normalizedAlexanderWhitney
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) X ≫
        (normalizedAlexanderWhitneyUnit ▷
          zModuleDoldKanEquivalence.functor.obj X) := by
  symm
  change
    (normalizedMooreComplex (ModuleCat ℤ)).map (λ_ X).inv ≫
        normalizedAlexanderWhitney
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) X ≫
        (normalizedAlexanderWhitneyUnit ▷
          (normalizedMooreComplex (ModuleCat ℤ)).obj X) =
      (λ_ ((normalizedMooreComplex (ModuleCat ℤ)).obj X)).inv
  simp only [normalizedAlexanderWhitney]
  rw [← Category.assoc]
  rw [← Category.assoc]
  have hinc :=
    (inclusionOfMooreComplex (ModuleCat ℤ)).naturality (λ_ X).inv
  change
    (normalizedMooreComplex (ModuleCat ℤ)).map (λ_ X).inv ≫
        inclusionOfMooreComplexMap
          ((𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ⊗ X) =
      inclusionOfMooreComplexMap X ≫
        (alternatingFaceMapComplex (ModuleCat ℤ)).map (λ_ X).inv at hinc
  rw [hinc]
  have htensor :
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))))
            (DoldKan.PInftyToNormalizedMooreComplex X) ≫
          (normalizedAlexanderWhitneyUnit ▷
            (normalizedMooreComplex (ModuleCat ℤ)).obj X) =
        HomologicalComplex.tensorHom alternatingAlexanderWhitneyUnit
          (DoldKan.PInftyToNormalizedMooreComplex X) := by
    change
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))))
            (DoldKan.PInftyToNormalizedMooreComplex X) ≫
          HomologicalComplex.tensorHom normalizedAlexanderWhitneyUnit
            (𝟙 ((normalizedMooreComplex (ModuleCat ℤ)).obj X)) = _
    calc
      _ = HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
            normalizedAlexanderWhitneyUnit)
          (DoldKan.PInftyToNormalizedMooreComplex X ≫
            𝟙 ((normalizedMooreComplex (ModuleCat ℤ)).obj X)) := by
        exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = _ := by
        rw [pInfty_comp_normalizedAlexanderWhitneyUnit]
        change HomologicalComplex.tensorHom alternatingAlexanderWhitneyUnit
          (DoldKan.PInftyToNormalizedMooreComplex X ≫ 𝟙 _) = _
        exact congrArg
          (fun t : alternatingChains X ⟶
              (normalizedMooreComplex (ModuleCat ℤ)).obj X ↦
            HomologicalComplex.tensorHom alternatingAlexanderWhitneyUnit t)
          (Category.comp_id (DoldKan.PInftyToNormalizedMooreComplex X))
  simp only [Category.assoc]
  erw [htensor]
  have htensor_def :
      HomologicalComplex.tensorHom alternatingAlexanderWhitneyUnit
          (DoldKan.PInftyToNormalizedMooreComplex X) =
        (alternatingAlexanderWhitneyUnit ▷ alternatingChains X) ≫
          ((𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ)) ◁
            DoldKan.PInftyToNormalizedMooreComplex X) := by
    exact MonoidalCategory.tensorHom_def alternatingAlexanderWhitneyUnit
      (DoldKan.PInftyToNormalizedMooreComplex X)
  rw [htensor_def]
  calc
    _ = inclusionOfMooreComplexMap X ≫
          (λ_ (alternatingChains X)).inv ≫
          ((𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ)) ◁
            DoldKan.PInftyToNormalizedMooreComplex X) := by
      simpa only [Category.assoc] using congrArg
        (fun t => inclusionOfMooreComplexMap X ≫ t ≫
          ((𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ)) ◁
            DoldKan.PInftyToNormalizedMooreComplex X))
        (alternatingAlexanderWhitney_left_unitality X).symm
    _ = _ := by
      rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
      rw [← MonoidalCategory.whiskerLeft_comp]
      have hsplit := (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
      change inclusionOfMooreComplexMap X ≫
        DoldKan.PInftyToNormalizedMooreComplex X = 𝟙 _ at hsplit
      rw [hsplit]
      simp

theorem normalizedAlexanderWhitney_right_unitality
    (X : SimplicialObject (ModuleCat.{0} ℤ)) :
    (ρ_ (zModuleDoldKanEquivalence.functor.obj X)).inv =
      zModuleDoldKanEquivalence.functor.map (ρ_ X).inv ≫
        normalizedAlexanderWhitney X
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
        (zModuleDoldKanEquivalence.functor.obj X ◁
          normalizedAlexanderWhitneyUnit) := by
  symm
  change
    (normalizedMooreComplex (ModuleCat ℤ)).map (ρ_ X).inv ≫
        normalizedAlexanderWhitney X
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
        ((normalizedMooreComplex (ModuleCat ℤ)).obj X ◁
          normalizedAlexanderWhitneyUnit) =
      (ρ_ ((normalizedMooreComplex (ModuleCat ℤ)).obj X)).inv
  simp only [normalizedAlexanderWhitney]
  rw [← Category.assoc]
  rw [← Category.assoc]
  have hinc :=
    (inclusionOfMooreComplex (ModuleCat ℤ)).naturality (ρ_ X).inv
  change
    (normalizedMooreComplex (ModuleCat ℤ)).map (ρ_ X).inv ≫
        inclusionOfMooreComplexMap
          (X ⊗ (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ)))) =
      inclusionOfMooreComplexMap X ≫
        (alternatingFaceMapComplex (ModuleCat ℤ)).map (ρ_ X).inv at hinc
  rw [hinc]
  have htensor :
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ)))) ≫
          ((normalizedMooreComplex (ModuleCat ℤ)).obj X ◁
            normalizedAlexanderWhitneyUnit) =
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          alternatingAlexanderWhitneyUnit := by
    change
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ)))) ≫
          HomologicalComplex.tensorHom
            (𝟙 ((normalizedMooreComplex (ModuleCat ℤ)).obj X))
            normalizedAlexanderWhitneyUnit = _
    calc
      _ = HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X ≫
            𝟙 ((normalizedMooreComplex (ModuleCat ℤ)).obj X))
          (DoldKan.PInftyToNormalizedMooreComplex
              (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
            normalizedAlexanderWhitneyUnit) := by
        exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = _ := by
        rw [pInfty_comp_normalizedAlexanderWhitneyUnit]
        change HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X ≫ 𝟙 _)
          alternatingAlexanderWhitneyUnit = _
        exact congrArg
          (fun t ↦ HomologicalComplex.tensorHom t alternatingAlexanderWhitneyUnit)
          (Category.comp_id _)
  simp only [Category.assoc]
  erw [htensor]
  have htensor_def :
      HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          alternatingAlexanderWhitneyUnit =
        (alternatingChains X ◁ alternatingAlexanderWhitneyUnit) ≫
          (DoldKan.PInftyToNormalizedMooreComplex X ▷
            (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))) := by
    exact MonoidalCategory.tensorHom_def'
      (DoldKan.PInftyToNormalizedMooreComplex X)
      alternatingAlexanderWhitneyUnit
  rw [htensor_def]
  calc
    _ = inclusionOfMooreComplexMap X ≫
          (ρ_ (alternatingChains X)).inv ≫
          (DoldKan.PInftyToNormalizedMooreComplex X ▷
            (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))) := by
      simpa only [Category.assoc] using congrArg
        (fun t => inclusionOfMooreComplexMap X ≫ t ≫
          (DoldKan.PInftyToNormalizedMooreComplex X ▷
            (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))))
        (alternatingAlexanderWhitney_right_unitality X).symm
    _ = _ := by
      rw [MonoidalCategory.rightUnitor_inv_naturality_assoc]
      have hwhisker :
          (inclusionOfMooreComplexMap X ▷
              (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))) ≫
            (DoldKan.PInftyToNormalizedMooreComplex X ▷
              (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))) =
            (inclusionOfMooreComplexMap X ≫
                DoldKan.PInftyToNormalizedMooreComplex X) ▷
              (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :=
        (MonoidalCategory.comp_whiskerRight
          (inclusionOfMooreComplexMap X)
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ))).symm
      rw [hwhisker]
      have hsplit := (DoldKan.splitMonoInclusionOfMooreComplexMap X).id
      change inclusionOfMooreComplexMap X ≫
        DoldKan.PInftyToNormalizedMooreComplex X = 𝟙 _ at hsplit
      rw [hsplit]
      rw [id_whiskerRight, Category.comp_id]

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
