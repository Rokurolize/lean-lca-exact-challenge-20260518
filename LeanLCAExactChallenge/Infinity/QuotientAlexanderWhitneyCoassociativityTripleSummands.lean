/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyCoassociativityProjections

/-! # Alexander--Whitney triple summands -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
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

variable (X Y Z : SimplicialObject (QuotientModule))

def complexLeftTripleProjection
    (K L M : ChainComplex (QuotientModule) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    ((K ⊗ L) ⊗ M).X n ⟶ (K.X p ⊗ L.X q) ⊗ M.X r :=
  complexTensorPairProjection (HomologicalComplex.tensorObj K L) M
      (p + q) r n (by omega) ≫
    (complexTensorPairProjection K L p q (p + q) rfl ⊗ₘ 𝟙 (M.X r))

@[reassoc (attr := simp)]
lemma complexRightTripleIncl_proj_self (K L M : ChainComplex (QuotientModule) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₂₃.ι
        (curriedTensor (QuotientModule)) (curriedTensor (QuotientModule)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        p q r n h ≫ complexRightTripleProjection K L M p q r n h = 𝟙 _ := by
  change GradedObject.Monoidal.ιTensorObj₃ K.X L.X M.X p q r n h ≫ _ = _
  rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
    p q r n h (q + r) rfl]
  let ii : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
    ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
  let io : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
  change
    (𝟙 (K.X p) ⊗ₘ Sigma.ι (complexTensorFamily L M (q + r)) ii) ≫
      Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
        Sigma.π (complexTensorFamily K (L ⊗ M) n) io ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) ii) = 𝟙 _
  have ho :
      Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) io =
        𝟙 (complexTensorFamily K (L ⊗ M) n io) :=
    Sigma.ι_π_eq_id (complexTensorFamily K (L ⊗ M) n) io
  dsimp [io, ii, complexTensorFamily] at ho ⊢
  slice_lhs 2 3 => erw [ho]
  slice_lhs 1 2 => erw [Category.comp_id]
  erw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [Category.id_comp]
  erw [Sigma.ι_π_eq_id]
  simp

@[reassoc]
lemma complexRightTripleIncl_proj_ne (K L M : ChainComplex (QuotientModule) ℕ)
    (i j k p q r n : ℕ) (hijk : i + j + k = n)
    (hpqr : p + q + r = n) (hne : (i, j, k) ≠ (p, q, r)) :
    HomologicalComplex.mapBifunctor₂₃.ι
        (curriedTensor (QuotientModule)) (curriedTensor (QuotientModule)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        i j k n hijk ≫ complexRightTripleProjection K L M p q r n hpqr = 0 := by
  change GradedObject.Monoidal.ιTensorObj₃ K.X L.X M.X i j k n hijk ≫ _ = 0
  by_cases hip : i = p
  · subst i
    have hs : j + k = q + r := by omega
    have hjk : (j, k) ≠ (q, r) := by
      intro e
      apply hne
      exact congrArg (fun x ↦ (p, x.1, x.2)) e
    rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
      p j k n hijk (q + r) hs]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨j, k⟩, by change j + k = q + r; exact hs⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
    let io : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
    change
      (𝟙 (K.X p) ⊗ₘ Sigma.ι (complexTensorFamily L M (q + r)) iis) ≫
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) io ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) iit) = 0
    have ho :
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
            Sigma.π (complexTensorFamily K (L ⊗ M) n) io =
          𝟙 (complexTensorFamily K (L ⊗ M) n io) :=
      Sigma.ι_π_eq_id (complexTensorFamily K (L ⊗ M) n) io
    dsimp [io, iis, iit, complexTensorFamily] at ho ⊢
    slice_lhs 2 3 => erw [ho]
    slice_lhs 1 2 => erw [Category.comp_id]
    erw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.id_comp]
    have hz :
        Sigma.ι (complexTensorFamily L M (q + r)) iis ≫
            Sigma.π (complexTensorFamily L M (q + r)) iit = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hjk
      exact congrArg Subtype.val e
    erw [hz]
    exact MonoidalPreadditive.whiskerLeft_zero
      (C := QuotientModule) (X := K.X p)
      (Y := L.X j ⊗ M.X k) (Z := L.X q ⊗ M.X r)
  · rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
      i j k n hijk (j + k) rfl]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {j + k} } :=
      ⟨⟨j, k⟩, by change j + k = j + k; rfl⟩
    let ios : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨i, j + k⟩, by change i + (j + k) = n; omega⟩
    let iot : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
    change
      (𝟙 (K.X i) ⊗ₘ Sigma.ι (complexTensorFamily L M (j + k)) iis) ≫
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) ios ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) iot ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) iit) = 0
    have hz :
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) ios ≫
            Sigma.π (complexTensorFamily K (L ⊗ M) n) iot = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hip
      exact congrArg (fun x ↦ x.1.1) e
    dsimp [iis, ios, iot, iit, complexTensorFamily] at hz ⊢
    slice_lhs 2 3 => erw [hz]
    slice_lhs 1 2 => erw [comp_zero]
    erw [zero_comp]

@[reassoc (attr := simp)]
lemma complexLeftTripleIncl_proj_self (K L M : ChainComplex (QuotientModule) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₁₂.ι
        (curriedTensor (QuotientModule)) (curriedTensor (QuotientModule)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        p q r n h ≫ complexLeftTripleProjection K L M p q r n h = 𝟙 _ := by
  change GradedObject.Monoidal.ιTensorObj₃' K.X L.X M.X p q r n h ≫ _ = _
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
    p q r n h (p + q) rfl]
  let ii : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
    ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
  let io : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨p + q, r⟩, by change p + q + r = n; exact h⟩
  change
    (Sigma.ι (complexTensorFamily K L (p + q)) ii ⊗ₘ 𝟙 (M.X r)) ≫
      Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
        Sigma.π (complexTensorFamily (K ⊗ L) M n) io ≫
          (Sigma.π (complexTensorFamily K L (p + q)) ii ⊗ₘ 𝟙 (M.X r)) = 𝟙 _
  have ho :
      Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) io =
        𝟙 (complexTensorFamily (K ⊗ L) M n io) :=
    Sigma.ι_π_eq_id (complexTensorFamily (K ⊗ L) M n) io
  dsimp [io, ii, complexTensorFamily] at ho ⊢
  slice_lhs 2 3 => erw [ho]
  slice_lhs 1 2 => erw [Category.comp_id]
  erw [MonoidalCategory.tensorHom_comp_tensorHom]
  erw [Sigma.ι_π_eq_id]
  simp

@[reassoc]
lemma complexLeftTripleIncl_proj_ne (K L M : ChainComplex (QuotientModule) ℕ)
    (i j k p q r n : ℕ) (hijk : i + j + k = n)
    (hpqr : p + q + r = n) (hne : (i, j, k) ≠ (p, q, r)) :
    HomologicalComplex.mapBifunctor₁₂.ι
        (curriedTensor (QuotientModule)) (curriedTensor (QuotientModule)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        i j k n hijk ≫ complexLeftTripleProjection K L M p q r n hpqr = 0 := by
  change GradedObject.Monoidal.ιTensorObj₃' K.X L.X M.X i j k n hijk ≫ _ = 0
  by_cases hkr : k = r
  · subst k
    have hs : i + j = p + q := by omega
    have hij : (i, j) ≠ (p, q) := by
      intro e
      apply hne
      exact congrArg (fun x ↦ (x.1, x.2, r)) e
    rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
      i j r n hijk (p + q) hs]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨i, j⟩, by change i + j = p + q; exact hs⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
    let io : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p + q, r⟩, by change p + q + r = n; exact hpqr⟩
    change
      (Sigma.ι (complexTensorFamily K L (p + q)) iis ⊗ₘ 𝟙 (M.X r)) ≫
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) io ≫
            (Sigma.π (complexTensorFamily K L (p + q)) iit ⊗ₘ 𝟙 (M.X r)) = 0
    have ho :
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
            Sigma.π (complexTensorFamily (K ⊗ L) M n) io =
          𝟙 (complexTensorFamily (K ⊗ L) M n io) :=
      Sigma.ι_π_eq_id (complexTensorFamily (K ⊗ L) M n) io
    dsimp [io, iis, iit, complexTensorFamily] at ho ⊢
    slice_lhs 2 3 => erw [ho]
    slice_lhs 1 2 => erw [Category.comp_id]
    erw [MonoidalCategory.tensorHom_comp_tensorHom]
    have hz :
        Sigma.ι (complexTensorFamily K L (p + q)) iis ≫
            Sigma.π (complexTensorFamily K L (p + q)) iit = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hij
      exact congrArg Subtype.val e
    erw [hz]
    exact MonoidalPreadditive.zero_whiskerRight
      (C := QuotientModule) (X := M.X r)
      (Y := K.X i ⊗ L.X j) (Z := K.X p ⊗ L.X q)
  · rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
      i j k n hijk (i + j) rfl]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {i + j} } :=
      ⟨⟨i, j⟩, by change i + j = i + j; rfl⟩
    let ios : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨i + j, k⟩, by change i + j + k = n; exact hijk⟩
    let iot : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p + q, r⟩, by change p + q + r = n; exact hpqr⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
    change
      (Sigma.ι (complexTensorFamily K L (i + j)) iis ⊗ₘ 𝟙 (M.X k)) ≫
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) ios ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) iot ≫
            (Sigma.π (complexTensorFamily K L (p + q)) iit ⊗ₘ 𝟙 (M.X r)) = 0
    have hz :
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) ios ≫
            Sigma.π (complexTensorFamily (K ⊗ L) M n) iot = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hkr
      exact congrArg (fun x ↦ x.1.2) e
    dsimp [iis, ios, iot, iit, complexTensorFamily] at hz ⊢
    slice_lhs 2 3 => erw [hz]
    slice_lhs 1 2 => erw [comp_zero]
    erw [zero_comp]


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
