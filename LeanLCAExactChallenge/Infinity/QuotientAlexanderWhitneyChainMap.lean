/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyFaceExpansions

/-! # Alexander--Whitney chain map -/

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

theorem inclusion_d_comp_projection_congr_total
    (i j p q n n' : ℕ)
    (hsource : i + j = n + 1) (hsource' : i + j = n' + 1)
    (htarget : p + q = n) (htarget' : p + q = n') :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (n + 1) hsource ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (n + 1) n) ≫
      tensorPairProjection X Y p q n htarget =
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (n' + 1) hsource' ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (n' + 1) n') ≫
      tensorPairProjection X Y p q n' htarget' := by
  have hnn' : n = n' := htarget.symm.trans htarget'
  subst n'
  subst n
  rfl

theorem first_inclusion_d_comp_projection_pq (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        (p + 1) q (p + q + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    ((curriedTensor (QuotientModule)).map
      ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) := by
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        (p + 1) q p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = _ := first_inclusion_d_comp_projection X Y p q

theorem second_inclusion_d_comp_projection_pq (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        p (q + 1) (p + q + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    ((-1 : ℤ) ^ p) •
      ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) := by
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        p (q + 1) p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = _ := second_inclusion_d_comp_projection X Y p q

theorem nonadjacent_inclusion_d_comp_projection_pq
    (i j p q : ℕ) (hij : i + j = p + q + 1)
    (hfirst : (i, j) ≠ (p + 1, q))
    (hsecond : (i, j) ≠ (p, q + 1)) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (p + q + 1) hij ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl = 0 := by
  have hij' : i + j = q + p + 1 := by omega
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij' ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        i j p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = 0 := nonadjacent_inclusion_d_comp_projection X Y
      i j p q hij' hfirst hsecond

theorem aw_target_d_projection_explicit_pq (p q : ℕ) :
    (alternatingAlexanderWhitneyDegree X Y (p + q + 1) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (QuotientModule)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) := by
  rw [alternatingAlexanderWhitneyDegree]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  let a : Fin (p + q + 2) := ⟨p + 1, by omega⟩
  let b : Fin (p + q + 2) := ⟨p, by omega⟩
  rw [fintype_sum_eq_add_two_of_eq_zero a b (by
    intro h
    exact Nat.succ_ne_self p (congrArg Fin.val h).symm)]
  · dsimp only [a, b]
    congr 1
    · rw [alternatingAlexanderWhitneySummand_pair X Y (p + 1) q]
      focus
        have h := congrArg
          (fun t =>
            (X.map
                  (SimplexCategory.subinterval
                    (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
                Y.map
                  (SimplexCategory.subinterval
                    (n := p + q + 1) (p + 1) q (by omega)).op) ≫ t)
          (first_inclusion_d_comp_projection_pq X Y p q)
        rw [Category.assoc]
        exact h
    · rw [alternatingAlexanderWhitneySummand_pair X Y p (q + 1)]
      focus
        have h := congrArg
          (fun t =>
            (X.map
                  (SimplexCategory.subinterval
                    (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
                Y.map
                  (SimplexCategory.subinterval
                    (n := p + q + 1) p (q + 1) (by omega)).op) ≫ t)
          (second_inclusion_d_comp_projection_pq X Y p q)
        rw [Category.assoc]
        exact h
  · intro r hra hrb
    rw [alternatingAlexanderWhitneySummand_pair X Y r (p + q + 1 - r)]
    focus
      have hnon := nonadjacent_inclusion_d_comp_projection_pq X Y
        r (p + q + 1 - r) p q (by omega) (by
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
          (X.map (SimplexCategory.subinterval
                (n := p + q + 1) 0 r (by omega)).op ⊗ₘ
            Y.map (SimplexCategory.subinterval
                (n := p + q + 1) r (p + q + 1 - r) (by omega)).op) ≫ t) hnon
      simp only [Category.assoc] at hassoc ⊢
      exact hassoc

theorem alternatingAlexanderWhitney_projected_chain (p q : ℕ) :
    (alternatingChains (X ⊗ Y)).d (p + q + 1) (p + q) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (alternatingAlexanderWhitneyDegree X Y (p + q + 1) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (p + q + 1) (p + q)) ≫
        tensorPairProjection X Y p q (p + q) rfl := by
  rw [alternating_d_comp_alexanderWhitney_cut X Y p q,
    aw_target_d_projection_explicit_pq X Y p q]
  congr 1

theorem alternatingAlexanderWhitneyDegree_comp_pairProjection (p q : ℕ) :
    alternatingAlexanderWhitneyDegree X Y (p + q) ≫
        tensorPairProjection X Y p q (p + q) rfl =
      X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
  rw [alternatingAlexanderWhitneyDegree, Preadditive.sum_comp,
    Finset.sum_eq_single (⟨p, by omega⟩ : Fin (p + q + 1))]
  · rw [alternatingAlexanderWhitneySummand_pair X Y p q (p + q) rfl]
    have h := congrArg
      (fun t =>
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) ≫ t)
      (ιTensorObj_tensorPairProjection_self X Y p q (p + q) rfl)
    exact (Category.assoc _ _ _).trans (h.trans (Category.comp_id _))
  · intro r _ hrp
    rw [alternatingAlexanderWhitneySummand_pair X Y r (p + q - r) (p + q) (by omega)]
    have h := ιTensorObj_tensorPairProjection_of_ne X Y
      r (p + q - r) p q (p + q) (by omega) rfl (by
        intro hpair
        apply hrp
        apply Fin.ext
        exact congrArg Prod.fst hpair)
    have hassoc := congrArg
      (fun t =>
        (X.map (SimplexCategory.subinterval (n := p + q) 0 r (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q) r (p + q - r) (by omega)).op) ≫ t) h
    exact (Category.assoc _ _ _).trans hassoc
  · simp

theorem tensorDegree_hom_ext_pair
    (n : ℕ) {A : QuotientModule}
    {f g : A ⟶
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n}
    (h : ∀ (p q : ℕ) (hpq : p + q = n),
      f ≫ tensorPairProjection X Y p q n hpq =
        g ≫ tensorPairProjection X Y p q n hpq) :
    f = g := by
  apply tensorDegree_hom_ext X Y n
  intro p
  simpa only [tensorCutProjection] using h p (n - p) (by omega)

theorem alternatingAlexanderWhitneyDegree_comm (n : ℕ) :
    (alternatingChains (X ⊗ Y)).d (n + 1) n ≫
        alternatingAlexanderWhitneyDegree X Y n =
      alternatingAlexanderWhitneyDegree X Y (n + 1) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (n + 1) n := by
  apply tensorDegree_hom_ext_pair X Y n
  intro p q hpq
  subst n
  rw [Category.assoc,
    alternatingAlexanderWhitneyDegree_comp_pairProjection X Y p q]
  exact alternatingAlexanderWhitney_projected_chain X Y p q


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
