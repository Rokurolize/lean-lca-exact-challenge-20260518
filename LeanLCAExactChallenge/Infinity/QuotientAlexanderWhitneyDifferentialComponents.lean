/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyFaceTensors

/-! # Alexander--Whitney differential components -/

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

/-- The first-factor part of the total differential lands in the preceding front cut.
The second-factor part has a different cut and vanishes after projection. -/
theorem first_inclusion_d_comp_projection (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        (p + 1) q (q + p + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    ((curriedTensor (QuotientModule)).map
      ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) (p + 1) q (by change p + 1 + q = q + p + 1; omega)
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) (p + 1) q (by change p + 1 + q = q + p + 1; omega)
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (p + 1) q (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (p + 1) q (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
    (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
    q (q + p) (by change p + q = q + p; omega)]
  have heps₁ : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p + 1, q) = 1 := rfl
  simp only [heps₁, one_smul, Category.assoc,
    ιTensorObj_tensorPairProjection_self]
  obtain rfl | q := q
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _
      (p + 1) 0 (0 + p) (by simp [ComplexShape.down])]
    rw [zero_comp]
    erw [Category.comp_id]
    exact add_zero (((curriedTensor (QuotientModule)).map
      ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X 0))
  · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
      (q + 1 + p) (by change p + 1 + q = q + 1 + p; omega)]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [ιTensorObj_tensorPairProjection_of_ne X Y
      (p + 1) q p (q + 1) (q + 1 + p)
      (by omega) (by omega) (by
        intro h
        exact Nat.succ_ne_self p (congrArg Prod.fst h))]
    rw [comp_zero, smul_zero]
    erw [Category.comp_id]
    exact add_zero (((curriedTensor (QuotientModule)).map
      ((alternatingChains X).d (p + 1) p)).app
        ((alternatingChains Y).X (q + 1)))

/-- The second-factor part of the total differential lands in the preceding back cut,
with the tensor-complex sign determined by the first degree. The first-factor part has a
different cut and vanishes after projection. -/
theorem second_inclusion_d_comp_projection (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        p (q + 1) (q + p + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    ((-1 : ℤ) ^ p) •
      ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) p (q + 1) (by change p + (q + 1) = q + p + 1; omega)
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) p (q + 1) (by change p + (q + 1) = q + p + 1; omega)
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          p (q + 1) (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          p (q + 1) (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
    (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
    (q + p) (by change p + q = q + p; omega)]
  have heps₂ : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q + 1) = (-1 : ℤˣ) ^ p := rfl
  simp only [Linear.units_smul_comp, heps₂, Category.assoc,
    ιTensorObj_tensorPairProjection_self]
  rw [Units.smul_def]
  change _ + ((-1 : ℤ) ^ p) • _ = _
  obtain rfl | p := p
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _
      0 (q + 1) (q + 0) (by simp [ComplexShape.down])]
    rw [zero_comp]
    change 0 + ((-1 : ℤ) ^ 0) •
        (((curriedTensor (QuotientModule)).obj ((alternatingChains X).X 0)).map
          ((alternatingChains Y).d (q + 1) q) ≫ 𝟙 _) =
      ((-1 : ℤ) ^ 0) •
        ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X 0)).map
          ((alternatingChains Y).d (q + 1) q)
    rw [Category.comp_id, zero_add]
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      (q + 1) (q + (p + 1)) (by change p + (q + 1) = q + (p + 1); omega)]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [ιTensorObj_tensorPairProjection_of_ne X Y
      p (q + 1) (p + 1) q (q + (p + 1))
      (by omega) (by omega) (by
        intro h
        exact Nat.succ_ne_self p (congrArg Prod.fst h).symm)]
    rw [comp_zero, smul_zero]
    change 0 + ((-1 : ℤ) ^ (p + 1)) •
        (((curriedTensor (QuotientModule)).obj ((alternatingChains X).X (p + 1))).map
          ((alternatingChains Y).d (q + 1) q) ≫ 𝟙 _) =
      ((-1 : ℤ) ^ (p + 1)) •
        ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X (p + 1))).map
          ((alternatingChains Y).d (q + 1) q)
    rw [Category.comp_id, zero_add]

/-- A source cut contributes to a target cut after one total differential only when it is
obtained by increasing exactly one coordinate of the target cut. -/
theorem nonadjacent_inclusion_d_comp_projection
    (i j p q : ℕ) (hij : i + j = q + p + 1)
    (hfirst : (i, j) ≠ (p + 1, q))
    (hsecond : (i, j) ≠ (p, q + 1)) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (q + p + 1) hij ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) i j hij
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (QuotientModule)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) i j hij
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          i j (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          i j (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    exact hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  have hd₁ :
      HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          i j (q + p) ≫
        tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
    obtain rfl | i := i
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _
        0 j (q + p) (by simp [ComplexShape.down])]
      rw [zero_comp]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.down ℕ).Rel (i + 1) i by simp [ComplexShape.down])
        j (q + p) (by change i + j = q + p; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTensorObj_tensorPairProjection_of_ne X Y
        i j p q (q + p) (by omega) (by omega) (by
          intro h
          apply hfirst
          have hi := congrArg Prod.fst h
          have hj := congrArg Prod.snd h
          simp only at hi hj
          exact Prod.ext (by omega) hj)]
      rw [comp_zero, smul_zero]
  have hd₂ :
      HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (QuotientModule)) (ComplexShape.down ℕ)
          i j (q + p) ≫
        tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
    obtain rfl | j := j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _
        i 0 (q + p) (by simp [ComplexShape.down])]
      rw [zero_comp]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ i
        (show (ComplexShape.down ℕ).Rel (j + 1) j by simp [ComplexShape.down])
        (q + p) (by change i + j = q + p; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTensorObj_tensorPairProjection_of_ne X Y
        i j p q (q + p) (by omega) (by omega) (by
          intro h
          apply hsecond
          have hi := congrArg Prod.fst h
          have hj := congrArg Prod.snd h
          simp only at hi hj
          exact Prod.ext hi (by omega))]
      rw [comp_zero, smul_zero]
  rw [hd₁, hd₂]
  change (0 : ((alternatingChains X).X i ⊗ (alternatingChains Y).X j) ⟶
    ((alternatingChains X).X p ⊗ (alternatingChains Y).X q)) + 0 = 0
  exact add_zero 0

/-- After projecting the target total degree to `(p,q)`, only the two adjacent source cuts
of the Alexander--Whitney sum survive. -/
theorem alternatingAlexanderWhitneyDegree_d_comp_projection (p q : ℕ) :
    (alternatingAlexanderWhitneyDegree X Y (q + p + 1) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    (X.map
          (SimplexCategory.subinterval (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := q + p + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (QuotientModule)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
    (X.map (SimplexCategory.subinterval (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := q + p + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) := by
  rw [alternatingAlexanderWhitneyDegree]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  let a : Fin (q + p + 2) := ⟨p + 1, by omega⟩
  let b : Fin (q + p + 2) := ⟨p, by omega⟩
  rw [fintype_sum_eq_add_two_of_eq_zero a b (by
    intro h
    exact Nat.succ_ne_self p (congrArg Fin.val h).symm)]
  · dsimp only [a, b]
    congr 1
    · rw [first_summand_eq_pair]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) (p + 1) q (by omega)).op) ≫ t)
        (first_inclusion_d_comp_projection X Y p q)
      rw [Category.assoc]
      exact h
    · rw [second_summand_eq_pair]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) p (q + 1) (by omega)).op) ≫ t)
        (second_inclusion_d_comp_projection X Y p q)
      rw [Category.assoc]
      exact h
  · intro r hra hrb
    simp only [alternatingAlexanderWhitneySummand, Category.assoc]
    have hnon := nonadjacent_inclusion_d_comp_projection X Y
      r (q + p + 1 - r) p q (by omega) (by
        intro hpair
        apply hra
        apply Fin.ext
        exact congrArg Prod.fst hpair) (by
        intro hpair
        apply hrb
        apply Fin.ext
        exact congrArg Prod.fst hpair)
    have hassoc := congrArg
      (fun t =>
        (X.map (alexanderWhitneyFront (q + p + 1) r).op ⊗ₘ
          Y.map (alexanderWhitneyBack (q + p + 1) r).op) ≫ t) hnon
    simp only [Category.assoc] at hassoc ⊢
    exact hassoc


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
