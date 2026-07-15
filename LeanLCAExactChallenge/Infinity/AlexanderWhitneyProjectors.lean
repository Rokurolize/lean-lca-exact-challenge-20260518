/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitney

/-!
# Normalization projectors and the Alexander--Whitney map

The raw Alexander--Whitney map does not generally land in the tensor of the two normalized
Moore subcomplexes. This file retains the two `PInfty` projectors and proves the correct source
fixed-point law: projecting the diagonal source before the compressed Alexander--Whitney map
does not change it.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

theorem front_sigma_not_mono_for_compressed_source
    (n : ℕ) (p : Fin (n + 2)) (i : Fin (n + 1))
    (hi : (i : ℕ) < (p : ℕ)) :
    ¬ Mono (alexanderWhitneyFront (n + 1) p ≫ SimplexCategory.σ i) := by
  rw [SimplexCategory.mono_iff_injective]
  intro h
  let a : Fin ((p : ℕ) + 1) := ⟨i, by omega⟩
  let b : Fin ((p : ℕ) + 1) := ⟨i + 1, by omega⟩
  have hab : a ≠ b := by
    intro hab
    have := congrArg Fin.val hab
    dsimp [a, b] at this
    omega
  apply hab
  apply h
  apply Fin.ext
  simp only [a, b, alexanderWhitneyFront, SimplexCategory.subinterval,
    SimplexCategory.σ, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, Fin.predAboveOrderHom_coe,
    OrderHom.coe_mk, Nat.add_zero]
  have hleft :
      i.predAbove (⟨i, by omega⟩ : Fin (n + 2)) = i := by
    have harg : (⟨i, by omega⟩ : Fin (n + 2)) = i.castSucc := by
      apply Fin.ext
      rfl
    rw [harg]
    exact Fin.predAbove_castSucc_self i
  have hright :
      i.predAbove (⟨i + 1, by omega⟩ : Fin (n + 2)) = i := by
    have harg : (⟨i + 1, by omega⟩ : Fin (n + 2)) = i.succ := by
      apply Fin.ext
      simp
    rw [harg]
    exact Fin.predAbove_succ_self i
  rw [hleft, hright]

theorem back_sigma_not_mono_for_compressed_source
    (n : ℕ) (p : Fin (n + 2)) (i : Fin (n + 1))
    (hi : (p : ℕ) ≤ (i : ℕ)) :
    ¬ Mono (alexanderWhitneyBack (n + 1) p ≫ SimplexCategory.σ i) := by
  rw [SimplexCategory.mono_iff_injective]
  intro h
  let a : Fin (n + 1 - (p : ℕ) + 1) := ⟨i - p, by omega⟩
  let b : Fin (n + 1 - (p : ℕ) + 1) := ⟨i + 1 - p, by omega⟩
  have hab : a ≠ b := by
    intro hab
    have := congrArg Fin.val hab
    dsimp [a, b] at this
    omega
  apply hab
  apply h
  apply Fin.ext
  simp only [a, b, alexanderWhitneyBack, SimplexCategory.subinterval,
    SimplexCategory.σ, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, Fin.predAboveOrderHom_coe,
    OrderHom.coe_mk, Nat.add_comm]
  have hleft :
      i.predAbove (⟨p + (i - p), by omega⟩ : Fin (n + 2)) = i := by
    have harg : (⟨p + (i - p), by omega⟩ : Fin (n + 2)) = i.castSucc := by
      ext
      simp
      omega
    rw [harg]
    exact Fin.predAbove_castSucc_self i
  have hright :
      i.predAbove (⟨p + (i + 1 - p), by omega⟩ : Fin (n + 2)) = i := by
    have harg : (⟨p + (i + 1 - p), by omega⟩ : Fin (n + 2)) = i.succ := by
      ext
      simp
      omega
    rw [harg]
    exact Fin.predAbove_succ_self i
  rw [hleft, hright]

variable (X Y : SimplicialObject (ModuleCat.{0} ℤ))

theorem compressedAlexanderWhitney_degeneraciesVanish (m : ℕ) :
    DoldKan.DegeneraciesVanish (X := X ⊗ Y)
      ((alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInfty : alternatingChains X ⟶ alternatingChains X)
          (DoldKan.PInfty : alternatingChains Y ⟶ alternatingChains Y)).f m) := by
  cases m with
  | zero => simp
  | succ n =>
      rw [DoldKan.degeneraciesVanish_succ_iff]
      intro i
      simp only [HomologicalComplex.comp_f, alternatingAlexanderWhitney_f,
        alternatingAlexanderWhitneyDegree]
      rw [Preadditive.sum_comp]
      erw [Preadditive.comp_sum]
      apply Finset.sum_eq_zero
      intro p _
      simp only [alternatingAlexanderWhitneySummand]
      slice_lhs 2 3 =>
        erw [Category.assoc]
        erw [HomologicalComplex.ι_mapBifunctorMap]
      slice_lhs 3 4 =>
        erw [← MonoidalCategory.tensorHom_def]
      change
        (X.σ i ⊗ₘ Y.σ i) ≫
            (X.map (alexanderWhitneyFront (n + 1) p).op ⊗ₘ
              Y.map (alexanderWhitneyBack (n + 1) p).op) ≫
            ((DoldKan.PInfty.f p : (alternatingChains X).X p ⟶ _) ⊗ₘ
              (DoldKan.PInfty.f (n + 1 - p) :
                (alternatingChains Y).X (n + 1 - p) ⟶ _)) ≫
            HomologicalComplex.ιTensorObj (alternatingChains X)
              (alternatingChains Y) p (n + 1 - p) (n + 1) (by omega) = 0
      slice_lhs 1 2 =>
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
      slice_lhs 1 2 =>
        rw [MonoidalCategory.tensorHom_comp_tensorHom]
      by_cases hi : (i : ℕ) < (p : ℕ)
      · have hx := DoldKan.degeneracy_comp_PInfty X p
          (alexanderWhitneyFront (n + 1) p ≫ SimplexCategory.σ i)
          (front_sigma_not_mono_for_compressed_source n p i hi)
        have hx' :
            X.σ i ≫ X.map (alexanderWhitneyFront (n + 1) p).op ≫
              DoldKan.PInfty.f p = 0 := by
          rw [SimplicialObject.σ_def, ← Category.assoc, ← Functor.map_comp, ← op_comp]
          exact hx
        have hx'' :
            (X.σ i ≫ X.map (alexanderWhitneyFront (n + 1) p).op) ≫
              DoldKan.PInfty.f p = 0 := by
          rw [Category.assoc]
          exact hx'
        rw [hx'', MonoidalPreadditive.zero_tensor, zero_comp]
      · have hpi : (p : ℕ) ≤ (i : ℕ) := by omega
        have hy := DoldKan.degeneracy_comp_PInfty Y (n + 1 - p)
          (alexanderWhitneyBack (n + 1) p ≫ SimplexCategory.σ i)
          (back_sigma_not_mono_for_compressed_source n p i hpi)
        have hy' :
            Y.σ i ≫ Y.map (alexanderWhitneyBack (n + 1) p).op ≫
              DoldKan.PInfty.f (n + 1 - p) = 0 := by
          rw [SimplicialObject.σ_def, ← Category.assoc, ← Functor.map_comp, ← op_comp]
          exact hy
        have hy'' :
            (Y.σ i ≫ Y.map (alexanderWhitneyBack (n + 1) p).op) ≫
              DoldKan.PInfty.f (n + 1 - p) = 0 := by
          rw [Category.assoc]
          exact hy'
        rw [hy'', MonoidalPreadditive.tensor_zero, zero_comp]

theorem pInfty_comp_compressedAlexanderWhitney :
    (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
          alternatingChains (X ⊗ Y)) ≫
        alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInfty : alternatingChains X ⟶ alternatingChains X)
          (DoldKan.PInfty : alternatingChains Y ⟶ alternatingChains Y) =
      alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInfty : alternatingChains X ⟶ alternatingChains X)
          (DoldKan.PInfty : alternatingChains Y ⟶ alternatingChains Y) := by
  apply HomologicalComplex.Hom.ext
  funext m
  let f := alternatingAlexanderWhitney X Y ≫
    HomologicalComplex.tensorHom
      (DoldKan.PInfty : alternatingChains X ⟶ alternatingChains X)
      (DoldKan.PInfty : alternatingChains Y ⟶ alternatingChains Y)
  let P : alternatingChains (X ⊗ Y) ⟶ alternatingChains (X ⊗ Y) :=
    DoldKan.PInfty
  let Q : alternatingChains (X ⊗ Y) ⟶ alternatingChains (X ⊗ Y) :=
    DoldKan.QInfty
  have hQ :
      Q.f m ≫ f.f m = 0 :=
    (DoldKan.degeneraciesVanish_iff_QInfty_f_comp
      (X := X ⊗ Y) (f.f m)).mp
      (compressedAlexanderWhitney_degeneraciesVanish X Y m)
  have hPQ : P.f m + Q.f m = 𝟙 _ := by
    exact DoldKan.PInfty_f_add_QInfty_f (X := X ⊗ Y) m
  change P.f m ≫ f.f m = f.f m
  calc
    P.f m ≫ f.f m =
        P.f m ≫ f.f m + Q.f m ≫ f.f m := by rw [hQ, add_zero]
    _ = (P.f m + Q.f m) ≫ f.f m :=
      (Preadditive.add_comp _ _ _ (P.f m) (Q.f m) (f.f m)).symm
    _ = f.f m := by
      rw [hPQ, Category.id_comp]

theorem pInfty_comp_compressedAlexanderWhitneyToNormalized :
    (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
        alternatingChains (X ⊗ Y)) ≫
        alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) =
      alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) := by
  let PX : alternatingChains X ⟶ alternatingChains X := DoldKan.PInfty
  let PY : alternatingChains Y ⟶ alternatingChains Y := DoldKan.PInfty
  let pX := DoldKan.PInftyToNormalizedMooreComplex X
  let pY := DoldKan.PInftyToNormalizedMooreComplex Y
  have htail :
      HomologicalComplex.tensorHom PX PY ≫
          HomologicalComplex.tensorHom pX pY =
        HomologicalComplex.tensorHom pX pY := by
    calc
      HomologicalComplex.tensorHom PX PY ≫
          HomologicalComplex.tensorHom pX pY =
        HomologicalComplex.tensorHom (PX ≫ pX) (PY ≫ pY) :=
          MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = HomologicalComplex.tensorHom pX pY := by
        rw [show PX ≫ pX = pX by
          dsimp only [PX, pX]
          exact DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex X]
        rw [show PY ≫ pY = pY by
          dsimp only [PY, pY]
          exact DoldKan.PInfty_comp_PInftyToNormalizedMooreComplex Y]
        rfl
  calc
    (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
          alternatingChains (X ⊗ Y)) ≫
        alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) =
      (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
          alternatingChains (X ⊗ Y)) ≫
        alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom PX PY ≫
        HomologicalComplex.tensorHom pX pY := by
          dsimp only [pX, pY]
          simpa only [Category.assoc] using congrArg
            (fun t => (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
              alternatingChains (X ⊗ Y)) ≫
              alternatingAlexanderWhitney X Y ≫ t) htail.symm
    _ = alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom PX PY ≫
        HomologicalComplex.tensorHom pX pY := by
      have h := congrArg
        (fun t => t ≫ HomologicalComplex.tensorHom pX pY)
        (pInfty_comp_compressedAlexanderWhitney X Y)
      dsimp only [PX, PY] at h ⊢
      calc
        _ = ((DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
              alternatingChains (X ⊗ Y)) ≫
              alternatingAlexanderWhitney X Y ≫
              HomologicalComplex.tensorHom DoldKan.PInfty DoldKan.PInfty) ≫
            HomologicalComplex.tensorHom pX pY := (Category.assoc _ _ _).symm
        _ = (alternatingAlexanderWhitney X Y ≫
              HomologicalComplex.tensorHom DoldKan.PInfty DoldKan.PInfty) ≫
            HomologicalComplex.tensorHom pX pY := h
        _ = _ := Category.assoc _ _ _
    _ = alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) := by
      dsimp only [pX, pY]
      simpa only [Category.assoc] using congrArg
        (fun t => alternatingAlexanderWhitney X Y ≫ t) htail

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
