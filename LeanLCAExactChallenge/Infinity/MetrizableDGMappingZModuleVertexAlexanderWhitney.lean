/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitney
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule

/-!
# Degree-zero Alexander--Whitney formulas for dg mapping modules

This file computes the Dold--Kan counit and normalized Alexander--Whitney map in degree
zero.  These formulas identify the degree-zero tensorator with the ordinary tensor of
degree-zero projections.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

theorem gammaZero_map_on_identity_summand
    {A B : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : A ⟶ B) :
    ((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌) =
      f.f 0 ≫
        ((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) := by
  change _ ≫
      (AlgebraicTopology.DoldKan.Γ₀.splitting A).desc (op ⦋0⦌) _ = _
  erw [(AlgebraicTopology.DoldKan.Γ₀.splitting A).ι_desc]
  rfl

theorem zModuleDoldKanInverseZeroIso_inv_on_identity_summand
    (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    ((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
        (zModuleDoldKanInverseZeroIso A).inv =
      𝟙 (A.X 0) := by
  dsimp [zModuleDoldKanInverseZeroIso]
  erw [(AlgebraicTopology.DoldKan.Γ₀.splitting A).ι_desc]
  apply eqToHom_refl

theorem gammaZero_projection_eq_zeroIso_inv
    (A : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (AlgebraicTopology.DoldKan.Γ₀.splitting A).πSummand
        (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) =
      (zModuleDoldKanInverseZeroIso A).inv := by
  apply (AlgebraicTopology.DoldKan.Γ₀.splitting A).hom_ext'
  intro I
  have hI := doldKanIndexSet_zero_eq_id I
  subst I
  rw [SimplicialObject.Splitting.cofan_inj_πSummand_eq_id]
  change 𝟙 (A.X 0) = _
  exact (zModuleDoldKanInverseZeroIso_inv_on_identity_summand A).symm

theorem zModuleDoldKanInverseZeroIso_inv_naturality
    {A B : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : A ⟶ B) :
    (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map f).app (op ⦋0⦌) ≫
        (zModuleDoldKanInverseZeroIso B).inv =
      (zModuleDoldKanInverseZeroIso A).inv ≫ f.f 0 := by
  change (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌) ≫
      (zModuleDoldKanInverseZeroIso B).inv =
    (zModuleDoldKanInverseZeroIso A).inv ≫ f.f 0
  apply (AlgebraicTopology.DoldKan.Γ₀.splitting A).hom_ext'
  intro I
  have hI := doldKanIndexSet_zero_eq_id I
  subst I
  calc
    _ = (((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan
            (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
            (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌)) ≫
          (zModuleDoldKanInverseZeroIso B).inv :=
      (Category.assoc _ _ _).symm
    _ = (f.f 0 ≫
          ((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan
            (op ⦋0⦌)).inj
            (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌))) ≫
          (zModuleDoldKanInverseZeroIso B).inv := by
      rw [gammaZero_map_on_identity_summand f]
    _ = f.f 0 ≫
          (((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan
            (op ⦋0⦌)).inj
            (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
              (zModuleDoldKanInverseZeroIso B).inv) :=
      Category.assoc _ _ _
    _ = f.f 0 := by
      exact (congrArg (fun t => f.f 0 ≫ t)
        (zModuleDoldKanInverseZeroIso_inv_on_identity_summand B)).trans
          (Category.comp_id _)
    _ = _ := by
      symm
      calc
        _ = ((((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan
                (op ⦋0⦌)).inj
              (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
                (zModuleDoldKanInverseZeroIso A).inv) ≫ f.f 0) :=
          (Category.assoc _ _ _).symm
        _ = 𝟙 (A.X 0) ≫ f.f 0 := congrArg (fun t => t ≫ f.f 0)
          (zModuleDoldKanInverseZeroIso_inv_on_identity_summand A)
        _ = _ := Category.id_comp _

def zModuleDoldKanCounitKaroubiMap
    (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (CategoryTheory.Idempotents.toKaroubi _).obj
          ((AlgebraicTopology.normalizedMooreComplex (ModuleCat ℤ)).obj
            (AlgebraicTopology.DoldKan.Γ₀.obj T)) ⟶
      (CategoryTheory.Idempotents.toKaroubi _).obj T :=
  (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
      (ModuleCat ℤ)).inv.app (AlgebraicTopology.DoldKan.Γ₀.obj T) ≫
    AlgebraicTopology.DoldKan.N₁Γ₀.hom.app T

theorem toKaroubiEquivalence_preimage_eq_direct
    {C : Type*} [Category C] [CategoryTheory.IsIdempotentComplete C]
    {X Y : C}
    (f : (CategoryTheory.Idempotents.toKaroubi C).obj X ⟶
      (CategoryTheory.Idempotents.toKaroubi C).obj Y) :
    (CategoryTheory.Idempotents.toKaroubiEquivalence C).unitIso.hom.app X ≫
        (CategoryTheory.Idempotents.toKaroubiEquivalence C).inverse.map f ≫
        (CategoryTheory.Idempotents.toKaroubiEquivalence C).unitIso.inv.app Y =
      (CategoryTheory.Idempotents.fullyFaithfulToKaroubi C).preimage f := by
  apply (CategoryTheory.Idempotents.fullyFaithfulToKaroubi C).map_injective
  let e := CategoryTheory.Idempotents.toKaroubiEquivalence C
  change e.functor.map (e.fullyFaithfulFunctor.preimage f) = _
  rw [e.fullyFaithfulFunctor.map_preimage]
  exact
    (CategoryTheory.Idempotents.fullyFaithfulToKaroubi C).map_preimage f |>.symm

theorem toKaroubiEquivalence_preimage_comp_eq_direct
    {C : Type*} [Category C] [CategoryTheory.IsIdempotentComplete C]
    {X Z : C} {P : CategoryTheory.Idempotents.Karoubi C}
    (f : (CategoryTheory.Idempotents.toKaroubi C).obj X ⟶
      P)
    (g : P ⟶
      (CategoryTheory.Idempotents.toKaroubi C).obj Z) :
    ((CategoryTheory.Idempotents.toKaroubiEquivalence C).unitIso.hom.app X ≫
          (CategoryTheory.Idempotents.toKaroubiEquivalence C).inverse.map f) ≫
        ((CategoryTheory.Idempotents.toKaroubiEquivalence C).inverse.map g ≫
          (CategoryTheory.Idempotents.toKaroubiEquivalence C).unitIso.inv.app Z) =
      (CategoryTheory.Idempotents.fullyFaithfulToKaroubi C).preimage (f ≫ g) := by
  let e := CategoryTheory.Idempotents.toKaroubiEquivalence C
  have hmap := congrArg
    (fun t => e.unitIso.hom.app X ≫ t ≫ e.unitIso.inv.app Z)
    (e.inverse.map_comp f g).symm
  have hwrapped :
      (e.unitIso.hom.app X ≫ e.inverse.map f) ≫
          (e.inverse.map g ≫ e.unitIso.inv.app Z) =
        e.unitIso.hom.app X ≫
          e.inverse.map (f ≫ g) ≫ e.unitIso.inv.app Z := by
    calc
      _ = e.unitIso.hom.app X ≫
          (e.inverse.map f ≫
            (e.inverse.map g ≫ e.unitIso.inv.app Z)) :=
        Category.assoc _ _ _
      _ = e.unitIso.hom.app X ≫
          ((e.inverse.map f ≫ e.inverse.map g) ≫
            e.unitIso.inv.app Z) := congrArg
        (fun t => e.unitIso.hom.app X ≫ t)
        (Category.assoc _ _ _).symm
      _ = _ := hmap
  exact hwrapped.trans
    (toKaroubiEquivalence_preimage_eq_direct (f ≫ g))

set_option linter.flexible false in
theorem zModuleDoldKanCounit_eq_preimage
    (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app T =
      (CategoryTheory.Idempotents.fullyFaithfulToKaroubi _).preimage
        (zModuleDoldKanCounitKaroubiMap T) := by
  simp [CategoryTheory.Abelian.DoldKan.equivalence,
    CategoryTheory.Abelian.DoldKan.comparisonN,
    CategoryTheory.Idempotents.DoldKan.equivalence_counitIso,
    CategoryTheory.Idempotents.DoldKan.η,
    zModuleDoldKanCounitKaroubiMap]
  let e := CategoryTheory.Idempotents.toKaroubiEquivalence
    (ChainComplex (ModuleCat ℤ) ℕ)
  let a := (DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
      (ModuleCat ℤ)).inv.app (AlgebraicTopology.DoldKan.Γ₀.obj T)
  let b := AlgebraicTopology.DoldKan.N₁Γ₀.hom.app T
  change (e.unitIso.hom.app _ ≫ e.inverse.map a) ≫
      (e.inverse.map b ≫ e.unitIso.inv.app T) =
    (CategoryTheory.Idempotents.fullyFaithfulToKaroubi _).preimage (a ≫ b)
  exact toKaroubiEquivalence_preimage_comp_eq_direct a b

theorem zModuleDoldKanCounit_f_zero
    (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app T).f 0 =
      (NormalizedMooreComplex.objX
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj T) 0).arrow ≫
        (zModuleDoldKanInverseZeroIso T).inv := by
  rw [zModuleDoldKanCounit_eq_preimage]
  change (zModuleDoldKanCounitKaroubiMap T).f.f 0 = _
  simp [zModuleDoldKanCounitKaroubiMap,
    AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi,
    gammaZero_projection_eq_zeroIso_inv]

theorem normalizedAlexanderWhitney_f_zero_explicit
    (X Y : SimplicialObject (ModuleCat.{0} ℤ)) :
    (DoldKanMonoidal.normalizedAlexanderWhitney X Y).f 0 =
      (NormalizedMooreComplex.objX (X ⊗ Y) 0).arrow ≫
        ((DoldKan.PInftyToNormalizedMooreComplex X).f 0 ⊗ₘ
          (DoldKan.PInftyToNormalizedMooreComplex Y).f 0) ≫
          HomologicalComplex.ιTensorObj
            ((normalizedMooreComplex (ModuleCat ℤ)).obj X)
            ((normalizedMooreComplex (ModuleCat ℤ)).obj Y) 0 0 0 rfl := by
  simp [DoldKanMonoidal.normalizedAlexanderWhitney,
    DoldKanMonoidal.alternatingAlexanderWhitney_f,
    DoldKanMonoidal.alternatingAlexanderWhitneyDegree_zero,
    MonoidalCategory.tensorHom_def, Category.assoc]

theorem pInftyToNormalized_comp_counit_f_zero
    (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (DoldKan.PInftyToNormalizedMooreComplex
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj T)).f 0 ≫
        (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app T).f 0 =
      (zModuleDoldKanInverseZeroIso T).inv := by
  rw [zModuleDoldKanCounit_f_zero]
  let X := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj T
  have hP := HomologicalComplex.congr_hom
    (DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X) 0
  calc
    _ = ((DoldKan.PInftyToNormalizedMooreComplex X).f 0 ≫
          (NormalizedMooreComplex.objX X 0).arrow) ≫
        (zModuleDoldKanInverseZeroIso T).inv :=
      (Category.assoc _ _ _).symm
    _ = DoldKan.PInfty.f 0 ≫
        (zModuleDoldKanInverseZeroIso T).inv := congrArg
      (fun t => t ≫ (zModuleDoldKanInverseZeroIso T).inv) hP
    _ = _ := by rw [DoldKan.PInfty_f_0, Category.id_comp]

theorem normalizedAlexanderWhitney_comp_counits_f_zero
    (A B : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (DoldKanMonoidal.normalizedAlexanderWhitney
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A)
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B)).f 0 ≫
        (HomologicalComplex.tensorHom
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A)
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B)).f 0 =
      (NormalizedMooreComplex.objX
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A ⊗
          DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B) 0).arrow ≫
        ((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
          (zModuleDoldKanInverseZeroIso B).inv) ≫
        HomologicalComplex.ιTensorObj A B 0 0 0 rfl := by
  rw [normalizedAlexanderWhitney_f_zero_explicit]
  have hι :
      HomologicalComplex.ιTensorObj
            ((normalizedMooreComplex (ModuleCat ℤ)).obj
              (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A))
            ((normalizedMooreComplex (ModuleCat ℤ)).obj
              (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B))
            0 0 0 rfl ≫
          (HomologicalComplex.tensorHom
            (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A)
            (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B)).f 0 =
        ((DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A).f 0 ⊗ₘ
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B).f 0) ≫
            HomologicalComplex.ιTensorObj A B 0 0 0 rfl := by
    exact GradedObject.Monoidal.ι_tensorHom
      (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A).f
      (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B).f
      0 0 0 rfl
  let X := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A
  let Y := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B
  let pA := (DoldKan.PInftyToNormalizedMooreComplex X).f 0
  let pB := (DoldKan.PInftyToNormalizedMooreComplex Y).f 0
  let cA := (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A).f 0
  let cB := (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B).f 0
  let q := (NormalizedMooreComplex.objX (X ⊗ Y) 0).arrow
  let iN := HomologicalComplex.ιTensorObj
    ((normalizedMooreComplex (ModuleCat ℤ)).obj X)
    ((normalizedMooreComplex (ModuleCat ℤ)).obj Y) 0 0 0 rfl
  let iAB := HomologicalComplex.ιTensorObj A B 0 0 0 rfl
  let m := (HomologicalComplex.tensorHom
    (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A)
    (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B)).f 0
  have hpc :
      (pA ⊗ₘ pB) ≫ (cA ⊗ₘ cB) =
        (pA ≫ cA) ⊗ₘ (pB ≫ cB) :=
    MonoidalCategory.tensorHom_comp_tensorHom pA pB cA cB
  have hpTensor :
      (pA ≫ cA) ⊗ₘ (pB ≫ cB) =
        (zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
          (zModuleDoldKanInverseZeroIso B).inv := congrArg₂
    (fun f g => f ⊗ₘ g)
    (pInftyToNormalized_comp_counit_f_zero A)
    (pInftyToNormalized_comp_counit_f_zero B)
  calc
    _ = q ≫ ((pA ⊗ₘ pB) ≫
          (iN ≫ m)) := by
      exact (Category.assoc q ((pA ⊗ₘ pB) ≫ iN) m).trans
        (congrArg (fun t => q ≫ t)
          (Category.assoc (pA ⊗ₘ pB) iN m))
    _ = q ≫ ((pA ⊗ₘ pB) ≫ ((cA ⊗ₘ cB) ≫ iAB)) := by
      exact congrArg (fun t => q ≫ ((pA ⊗ₘ pB) ≫ t)) hι
    _ = q ≫ (((pA ⊗ₘ pB) ≫ (cA ⊗ₘ cB)) ≫ iAB) := by
      exact congrArg (fun t => q ≫ t)
        (Category.assoc (pA ⊗ₘ pB) (cA ⊗ₘ cB) iAB).symm
    _ = q ≫ (((pA ≫ cA) ⊗ₘ (pB ≫ cB)) ≫ iAB) := by
      exact congrArg (fun t => q ≫ (t ≫ iAB)) hpc
    _ = q ≫
        (((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
          (zModuleDoldKanInverseZeroIso B).inv) ≫ iAB) := by
      exact congrArg (fun t => q ≫ (t ≫ iAB)) hpTensor
    _ = _ := by simp only [X, Y, q, iAB]

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
