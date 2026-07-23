/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyDifferentialComponents

/-! # Alexander--Whitney face expansions -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

variable (X Y : SimplicialObject (QuotientModule))

/-- Expand the front-adjacent contribution into its internal faces and last boundary face. -/
theorem first_factor_faces_expansion (p q : ℕ) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (QuotientModule)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) =
    (∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) •
      ((X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))) +
      ((-1 : ℤ) ^ (p + 1)) •
        ((X.map
              (SimplexCategory.subinterval
                (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
            Y.map
              (SimplexCategory.subinterval
                (n := p + q + 1) (p + 1) q (by omega)).op) ≫
          (X.δ (Fin.last (p + 1)) ⊗ₘ
            𝟙 (Y.obj (Opposite.op (SimplexCategory.mk q))))) := by
  let front :=
    X.map (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
      Y.map
        (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op
  change front ≫ _ = _
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  have hmap := Functor.map_sum (curriedTensor (QuotientModule))
    (fun i : Fin (p + 2) => ((-1 : ℤ) ^ (i : ℕ)) • X.δ i) Finset.univ
  erw [hmap]
  rw [NatTrans.app_sum]
  have hcomp := Preadditive.comp_sum Finset.univ front
    (fun i : Fin (p + 2) =>
      ((curriedTensor (QuotientModule)).map
        (((-1 : ℤ) ^ (i : ℕ)) • X.δ i)).app ((alternatingChains Y).X q))
  erw [hcomp]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Functor.map_zsmul, NatTrans.app_zsmul]
    simp only [Fin.val_castSucc]
    have hface :
        front ≫
            ((curriedTensor (QuotientModule)).map (X.δ i.castSucc)).app
              ((alternatingChains Y).X q) =
          (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
              Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
      simp only [front, curriedTensor_map_app, ← tensorHom_id]
      exact alexanderWhitneyFirstInternal_tensor X Y p q i
    calc
      _ = ((-1 : ℤ) ^ (i : ℕ)) •
          (front ≫ ((curriedTensor (QuotientModule)).map (X.δ i.castSucc)).app
            ((alternatingChains Y).X q)) :=
        Preadditive.comp_zsmul _ _ _
      _ = ((-1 : ℤ) ^ (i : ℕ)) • _ := congrArg _ hface
  · rw [Functor.map_zsmul, NatTrans.app_zsmul]
    change front ≫ (((-1 : ℤ) ^ (p + 1)) • _) =
      ((-1 : ℤ) ^ (p + 1)) • (front ≫ _)
    exact Preadditive.comp_zsmul _ _ _

/-- Expand the back-adjacent contribution into its zeroth boundary face and internal faces. -/
theorem second_factor_faces_expansion (p q : ℕ) :
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) =
    ((-1 : ℤ) ^ p) •
      ((X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 (X.obj (Opposite.op (SimplexCategory.mk p))) ⊗ₘ
          Y.δ (0 : Fin (q + 2)))) +
      ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) •
        ((X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
            Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
          (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
            Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) := by
  let back :=
    X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
      Y.map
        (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op
  change back ≫ (((-1 : ℤ) ^ p) • _) = _
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  have hmap := Functor.map_sum
    ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p))
    (fun i : Fin (q + 2) => ((-1 : ℤ) ^ (i : ℕ)) • Y.δ i) Finset.univ
  erw [hmap]
  have houter := Preadditive.comp_zsmul back
    ((∑ i : Fin (q + 2),
      ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
        (((-1 : ℤ) ^ (i : ℕ)) • Y.δ i))) ((-1 : ℤ) ^ p)
  erw [houter]
  have hcomp := Preadditive.comp_sum Finset.univ back
    (fun i : Fin (q + 2) =>
      ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
        (((-1 : ℤ) ^ (i : ℕ)) • Y.δ i))
  erw [hcomp]
  rw [Fin.sum_univ_succ, smul_add]
  congr 1
  · rw [Functor.map_zsmul]
    simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Functor.map_zsmul]
    have hface :
        back ≫
            ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
              (Y.δ i.succ) =
          (X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
              Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
      simp only [back, curriedTensor_obj_map, ← id_tensorHom]
      exact alexanderWhitneySecondInternal_tensor X Y p q i
    calc
      ((-1 : ℤ) ^ p) •
          (back ≫ (((-1 : ℤ) ^ (i.succ : ℕ)) • _)) =
        ((-1 : ℤ) ^ p) •
          (((-1 : ℤ) ^ (i.succ : ℕ)) • (back ≫ _)) := by
            rw [Preadditive.comp_zsmul]
      _ = ((-1 : ℤ) ^ p) •
          (((-1 : ℤ) ^ (i.succ : ℕ)) • _) :=
        congrArg _ (congrArg _ hface)
      _ = ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • _ :=
        neg_one_pow_succ_smul_smul p q i _

/-- The alternating differential satisfies the Alexander--Whitney cut formula. -/
theorem alternating_d_comp_alexanderWhitney_cut (p q : ℕ) :
    (alternatingChains (X ⊗ Y)).d (p + q + 1) (p + q) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map
            (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
          ((curriedTensor (QuotientModule)).map
            ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
        ((-1 : ℤ) ^ p) •
          ((X.map
                (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval (n := p + q + 1) p (q + 1)
                  (by omega)).op) ≫
            ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
              ((alternatingChains Y).d (q + 1) q)) := by
  rw [← Preadditive.comp_zsmul]
  rw [first_factor_faces_expansion X Y p q]
  erw [second_factor_faces_expansion X Y p q]
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  erw [Preadditive.sum_comp]
  have hleft :
      (∑ i : Fin (p + q + 2),
          (((-1 : ℤ) ^ (i : ℕ)) • (X ⊗ Y).δ i) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) =
        ∑ i : Fin (p + q + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((X ⊗ Y).δ i ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Preadditive.zsmul_comp _ _ _
  erw [hleft]
  rw [alternating_sum_faces_split p q]
  let early := ∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) •
    ((X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
      (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))
  let late := ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) •
    ((X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
      (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))
  let firstBoundary :
      (X.obj (Opposite.op (SimplexCategory.mk (p + q + 1))) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk (p + q + 1)))) ⟶
        X.obj (Opposite.op (SimplexCategory.mk p)) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk q)) :=
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      (X.δ (Fin.last (p + 1)) ⊗ₘ 𝟙 ((alternatingChains Y).X q))
  let secondBoundary :
      (X.obj (Opposite.op (SimplexCategory.mk (p + q + 1))) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk (p + q + 1)))) ⟶
        X.obj (Opposite.op (SimplexCategory.mk p)) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk q)) :=
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ (0 : Fin (q + 2)))
  change early + late =
    (early + ((-1 : ℤ) ^ (p + 1)) • firstBoundary) +
      (((-1 : ℤ) ^ p) • secondBoundary + late)
  have hboundary : firstBoundary = secondBoundary := by
    exact alexanderWhitneyBoundary_tensor X Y p q
  have hcancel :
      ((-1 : ℤ) ^ (p + 1)) • firstBoundary +
        ((-1 : ℤ) ^ p) • secondBoundary = 0 := by
    rw [hboundary]
    exact neg_one_pow_boundary_cancel p secondBoundary
  rw [show (early + ((-1 : ℤ) ^ (p + 1)) • firstBoundary) +
      (((-1 : ℤ) ^ p) • secondBoundary + late) =
        early +
          (((( -1 : ℤ) ^ (p + 1)) • firstBoundary +
            ((-1 : ℤ) ^ p) • secondBoundary) + late) by abel]
  rw [hcancel, zero_add]

/-- The subtraction-indexed AW summand rewritten using an exact pair of cut degrees. -/
theorem alternatingAlexanderWhitneySummand_pair
    (i j n : ℕ) (hij : i + j = n) :
    alternatingAlexanderWhitneySummand X Y n ⟨i, by omega⟩ =
      (X.map (SimplexCategory.subinterval (n := n) 0 i (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := n) i j (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j n hij := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨i, n - i⟩, by change i + (n - i) = n; omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨i, j⟩, by change i + j = n; exact hij⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y n) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y n) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y n) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
