/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyCoassociativityProjected

/-! # Alexander--Whitney coassociativity theorem -/

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

theorem tensorLeft_complexTensor_hom_ext
    (K L M : ChainComplex (QuotientModule) ℕ)
    (p n : ℕ) {A : QuotientModule}
    {f g : A ⟶ K.X p ⊗ (L ⊗ M).X n}
    (h : ∀ (q r : ℕ) (hqr : q + r = n),
      f ≫ (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r n hqr) =
        g ≫ (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r n hqr)) :
    f = g := by
  let J : Type := { qr : ℕ × ℕ // qr ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  let F := complexTensorFamily L M n
  have hinner : ∑ j, Sigma.π F j ≫ Sigma.ι F j = 𝟙 _ := by
    apply Sigma.hom_ext
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [← Category.assoc, Sigma.ι_π_of_ne F hij.symm, zero_comp]
    · simp
  have htensor :
      ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) = 𝟙 _ := by
    calc
      _ = ∑ j, 𝟙 (K.X p) ⊗ₘ (Sigma.π F j ≫ Sigma.ι F j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      _ = 𝟙 (K.X p) ⊗ₘ (∑ j, Sigma.π F j ≫ Sigma.ι F j) := by
        change ∑ j, ((curriedTensor (QuotientModule)).obj (K.X p)).map
            (Sigma.π F j ≫ Sigma.ι F j) = _
        rw [← Functor.map_sum]
        rfl
      _ = _ := by rw [hinner]; simp
  have htensor' :
      ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) =
        𝟙 (K.X p ⊗ (L ⊗ M).X n) := by
    dsimp only [F, complexTensorFamily, HomologicalComplex.tensorObj] at htensor ⊢
    exact htensor
  have hfg :
      f = g ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
        (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
    calc
      f = f ≫ 𝟙 (K.X p ⊗ (L ⊗ M).X n) := (Category.comp_id f).symm
      _ = f ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
        erw [htensor']
      _ = ∑ j, f ≫ ((𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j)) := by
        rw [Preadditive.comp_sum]
      _ = ∑ j, g ≫ ((𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j)) := by
        apply Finset.sum_congr rfl
        rintro ⟨⟨q, r⟩, hqr⟩ -
        change q + r = n at hqr
        rw [← Category.assoc]
        erw [h q r hqr]
        erw [Category.assoc]
      _ = g ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
        rw [Preadditive.comp_sum]
  erw [htensor'] at hfg
  simpa only [Category.comp_id] using hfg

theorem complexRightTriple_hom_ext
    (K L M : ChainComplex (QuotientModule) ℕ)
    (n : ℕ) {A : QuotientModule}
    {f g : A ⟶ (K ⊗ (L ⊗ M)).X n}
    (h : ∀ (p q r : ℕ) (hpqr : p + q + r = n),
      f ≫ complexRightTripleProjection K L M p q r n hpqr =
        g ≫ complexRightTripleProjection K L M p q r n hpqr) :
    f = g := by
  let J : Type := { ps : ℕ × ℕ // ps ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  apply finiteCoproduct_hom_ext
    (complexTensorFamily K (HomologicalComplex.tensorObj L M) n)
  rintro ⟨⟨p, s⟩, hps⟩
  change p + s = n at hps
  apply tensorLeft_complexTensor_hom_ext K L M p s
  intro q r hqr
  subst s
  have hpqr : p + q + r = n := by omega
  simpa only [complexRightTripleProjection, complexTensorPairProjection,
    Category.assoc] using
    h p q r hpqr

theorem alternatingAlexanderWhitney_coassociativity :
    alternatingAlexanderWhitney (X ⊗ Y) Z ≫
          HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z)) ≫
          (α_ (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z)).hom =
      (alternatingFaceMapComplex (QuotientModule)).map ((α_ X Y Z).hom) ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply complexRightTriple_hom_ext (alternatingChains X) (alternatingChains Y)
    (alternatingChains Z) n
  intro p q r hpqr
  subst n
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    alternatingAlexanderWhitney_coassociativity_projected X Y Z p q r



end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
