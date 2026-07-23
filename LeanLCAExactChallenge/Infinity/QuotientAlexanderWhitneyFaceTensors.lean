/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyCuts

/-! # Alexander--Whitney face tensors -/

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

/-- An early face of the tensor simplex is the corresponding front-factor face of the
Alexander--Whitney summand; the back factor is unchanged after shifting the cut. -/
theorem alexanderWhitneyEarlyFace_tensor (p q i : ℕ) (hi : i ≤ p) :
    (X ⊗ Y).δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ (⟨i, by omega⟩ : Fin (p + 2)) ⊗ₘ 𝟙 _) := by
  have hx :
      X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ≫
          X.δ (⟨i, by omega⟩ : Fin (p + 2)) =
        X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
          X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def, alexanderWhitneyFront]
      using congrArg (fun f => X.map f.op)
      (alexanderWhitneyFront_face (p + q) p i (by omega) hi)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op =
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def] using
      congrArg (fun f => Y.map f.op) (alexanderWhitneyBack_early_face p q i hi)
  change
    (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫ _ = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← hx, ← hy, Category.comp_id]

/-- A late face of the tensor simplex is the corresponding back-factor face of the
Alexander--Whitney summand; the front factor is unchanged. -/
theorem alexanderWhitneyLateFace_tensor (p q : ℕ)
    (i : Fin (q + 2)) (hi : 0 < i) :
    (X ⊗ Y).δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 _ ⊗ₘ Y.δ i) := by
  have hx :
      X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op =
        X.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
          X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def] using
      congrArg (fun f => X.map f.op) (alexanderWhitneyFront_late_face p q i hi)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op ≫
          Y.δ i =
        Y.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def] using
      congrArg (fun f => Y.map f.op) (alexanderWhitneyBack_face p q i)
  change
    (X.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨p + i, by omega⟩ : Fin (p + q + 2))) ≫ _ = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← hx, ← hy, Category.comp_id]

/-- The last front-factor face and the zeroth back-factor face yield the same unsigned
Alexander--Whitney boundary morphism. -/
theorem alexanderWhitneyBoundary_tensor (p q : ℕ) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ (Fin.last (p + 1)) ⊗ₘ 𝟙 _) =
      (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 _ ⊗ₘ Y.δ (0 : Fin (q + 2))) := by
  have hx :
      X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ≫
          X.δ (Fin.last (p + 1)) =
        X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def] using
      congrArg (fun f => X.map f.op) (alexanderWhitneyFront_last p q)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op ≫
          Y.δ (0 : Fin (q + 2)) =
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp, SimplicialObject.δ_def] using
      congrArg (fun f => Y.map f.op) (alexanderWhitneyBack_zero_face p q)
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [hx, hy]
  simp only [Category.comp_id]

/-- The internal first-factor faces of the front-adjacent source cut agree with the early
diagonal faces of the tensor simplex. -/
theorem alexanderWhitneyFirstInternal_tensor (p q : ℕ) (i : Fin (p + 1)) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ i.castSucc ⊗ₘ 𝟙 ((alternatingChains Y).X q)) =
      (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
  exact (alexanderWhitneyEarlyFace_tensor X Y p q i (by omega)).symm

/-- The internal second-factor faces of the back-adjacent source cut agree with the late
diagonal faces of the tensor simplex. -/
theorem alexanderWhitneySecondInternal_tensor (p q : ℕ) (i : Fin (q + 1)) :
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ i.succ) =
      (X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
  have hface :
      (⟨p + (i.succ : ℕ), by omega⟩ : Fin (p + q + 2)) =
        ⟨p + 1 + (i : ℕ), by omega⟩ := by
    ext
    simp
    omega
  have hterm := (alexanderWhitneyLateFace_tensor X Y p q i.succ (by simp)).symm
  rw [hface] at hterm
  exact hterm

/-- Multiplying two alternating signs adds their exponents. -/
theorem neg_one_pow_smul_smul {A B : QuotientModule} (p i : ℕ) (f : A ⟶ B) :
    ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ i) • f) =
      ((-1 : ℤ) ^ (p + i)) • f := by
  rw [smul_smul, pow_add]

/-- The second-factor tensor sign and the positive-index face sign combine to the global
late-face sign. -/
theorem neg_one_pow_succ_smul_smul {A B : QuotientModule}
    (p q : ℕ) (i : Fin (q + 1)) (f : A ⟶ B) :
    ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ (i.succ : ℕ)) • f) =
      ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • f := by
  rw [smul_smul, ← pow_add]
  congr 2
  simp
  omega

/-- The last front-face sign cancels the signed zeroth back-face sign. -/
theorem neg_one_pow_boundary_cancel {A B : QuotientModule} (p : ℕ) (f : A ⟶ B) :
    ((-1 : ℤ) ^ (p + 1)) • f + ((-1 : ℤ) ^ p) • f = 0 := by
  simp [pow_succ]

/-- Split a sum over all faces at the Alexander--Whitney cut. -/
theorem sum_faces_split {A B : QuotientModule} (p q : ℕ)
    (f : Fin (p + q + 2) → (A ⟶ B)) :
    (∑ i : Fin (p + q + 2), f i) =
      (∑ i : Fin (p + 1), f ⟨i, by omega⟩) +
        ∑ i : Fin (q + 1), f ⟨p + 1 + i, by omega⟩ := by
  let h : (p + 1) + (q + 1) = p + q + 2 := by omega
  let g : Fin ((p + 1) + (q + 1)) → (A ⟶ B) := fun i => f (Fin.cast h i)
  have hsum := Fin.sum_univ_add g
  have hleft : (∑ i, g i) = ∑ i, f i := by
    exact Fintype.sum_equiv (Fin.castOrderIso h).toEquiv g f (fun i => rfl)
  rw [← hleft]
  exact hsum

/-- Split an alternating face sum into its early and late families at the cut. -/
theorem alternating_sum_faces_split {A B : QuotientModule} (p q : ℕ)
    (f : Fin (p + q + 2) → (A ⟶ B)) :
    (∑ i : Fin (p + q + 2), ((-1 : ℤ) ^ (i : ℕ)) • f i) =
      (∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) • f ⟨i, by omega⟩) +
        ∑ i : Fin (q + 1),
          ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • f ⟨p + 1 + i, by omega⟩ := by
  simpa only using sum_faces_split p q
    (fun i : Fin (p + q + 2) => ((-1 : ℤ) ^ (i : ℕ)) • f i)

/-- Expand the first alternating differential after tensoring with an identity. -/
theorem first_alternating_d_tensor_expand (p q : ℕ) :
    ((curriedTensor (QuotientModule)).map ((alternatingChains X).d (p + 1) p)).app
        ((alternatingChains Y).X q) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (X.δ i ⊗ₘ 𝟙 ((alternatingChains Y).X q)) := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  change
    ((∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • X.δ i) ⊗ₘ
      𝟙 ((alternatingChains Y).X q)) = _
  rw [CategoryTheory.sum_tensor]
  apply Finset.sum_congr rfl
  intro i _
  simp only [alternatingFaceMapComplex_obj_X, Int.reduceNeg, tensorHom_id]
  exact (tensorRight ((alternatingChains Y).X q)).map_zsmul

/-- Expand the second alternating differential after tensoring with an identity. -/
theorem second_alternating_d_tensor_expand (p q : ℕ) :
    ((curriedTensor (QuotientModule)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) =
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ i) := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  change
    (𝟙 ((alternatingChains X).X p) ⊗ₘ
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Y.δ i) = _
  rw [CategoryTheory.tensor_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [alternatingFaceMapComplex_obj_X, Int.reduceNeg, id_tensorHom]
  exact (tensorLeft ((alternatingChains X).X p)).map_zsmul

/-- The `p + (n - p) = n` summand of the unnormalized Alexander--Whitney map. -/
def alternatingAlexanderWhitneySummand (n : ℕ) (p : Fin (n + 1)) :
    (X ⊗ Y).obj (op (SimplexCategory.mk n)) ⟶
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex (QuotientModule)).obj X)
        ((alternatingFaceMapComplex (QuotientModule)).obj Y)).X n :=
  (X.map (alexanderWhitneyFront n p).op ⊗ₘ
      Y.map (alexanderWhitneyBack n p).op) ≫
    HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex (QuotientModule)).obj X)
      ((alternatingFaceMapComplex (QuotientModule)).obj Y)
      p (n - p) n (by omega)

/-- The degree-`n` Alexander--Whitney formula on alternating face-map complexes. -/
def alternatingAlexanderWhitneyDegree (n : ℕ) :
    ((alternatingFaceMapComplex (QuotientModule)).obj (X ⊗ Y)).X n ⟶
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex (QuotientModule)).obj X)
        ((alternatingFaceMapComplex (QuotientModule)).obj Y)).X n :=
  ∑ p : Fin (n + 1), alternatingAlexanderWhitneySummand X Y n p

/-- Normalize the front-adjacent Alexander--Whitney summand to the exact pair `(p+1,q)`. -/
theorem first_summand_eq_pair (p q : ℕ) :
    alternatingAlexanderWhitneySummand X Y (q + p + 1) ⟨p + 1, by omega⟩ =
      (X.map
            (SimplexCategory.subinterval
              (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval
              (n := q + p + 1) (p + 1) q (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p + 1, q + p + 1 - (p + 1)⟩, by
      change p + 1 + (q + p + 1 - (p + 1)) = q + p + 1
      omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p + 1, q⟩, by change p + 1 + q = q + p + 1; omega⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y (q + p + 1)) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega

/-- Normalize the back-adjacent Alexander--Whitney summand to the exact pair `(p,q+1)`. -/
theorem second_summand_eq_pair (p q : ℕ) :
    alternatingAlexanderWhitneySummand X Y (q + p + 1) ⟨p, by omega⟩ =
      (X.map
            (SimplexCategory.subinterval
              (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval
              (n := q + p + 1) p (q + 1) (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p, q + p + 1 - p⟩, by
      change p + (q + p + 1 - p) = q + p + 1
      omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p, q + 1⟩, by change p + (q + 1) = q + p + 1; omega⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y (q + p + 1)) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega

@[simp]
theorem alternatingAlexanderWhitneyDegree_zero :
    alternatingAlexanderWhitneyDegree X Y 0 =
      HomologicalComplex.ιTensorObj
        ((alternatingFaceMapComplex (QuotientModule)).obj X)
        ((alternatingFaceMapComplex (QuotientModule)).obj Y)
        0 0 0 rfl := by
  simp [alternatingAlexanderWhitneyDegree, alternatingAlexanderWhitneySummand]

/-- Projecting the degreewise Alexander--Whitney sum to a cut recovers exactly its summand. -/
theorem alternatingAlexanderWhitneyDegree_comp_projection
    (n : ℕ) (p : Fin (n + 1)) :
    alternatingAlexanderWhitneyDegree X Y n ≫ tensorCutProjection X Y n p =
      X.map (alexanderWhitneyFront n p).op ⊗ₘ
        Y.map (alexanderWhitneyBack n p).op := by
  rw [alternatingAlexanderWhitneyDegree, Preadditive.sum_comp,
    Finset.sum_eq_single p]
  · simp only [alternatingAlexanderWhitneySummand]
    let ip : { pq // pq ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, n - p⟩, by change p + (n - p) = n; omega⟩
    change _ ≫
      (Sigma.ι (tensorCutFamily X Y n) ip ≫
        Sigma.π (tensorCutFamily X Y n) ip) = _
    rw [Sigma.ι_π_eq_id, Category.comp_id]
  · intro q _ hqp
    simp only [alternatingAlexanderWhitneySummand]
    let iq : { ij // ij ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨q, n - q⟩, by change q + (n - q) = n; omega⟩
    let ip : { ij // ij ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, n - p⟩, by change p + (n - p) = n; omega⟩
    change _ ≫
      (Sigma.ι (tensorCutFamily X Y n) iq ≫
        Sigma.π (tensorCutFamily X Y n) ip) = 0
    rw [Sigma.ι_π_of_ne, comp_zero]
    intro h
    exact hqp (Fin.ext (congrArg (fun z => z.1.1) h))
  · simp


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
