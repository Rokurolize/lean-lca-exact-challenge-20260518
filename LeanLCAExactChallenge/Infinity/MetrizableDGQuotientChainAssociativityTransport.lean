/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainAssociativityRaw

/-! # Transporting associativity through smart truncation -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

lemma quotientDGChain_assoc_transport {V : Type*} [Category V] [MonoidalCategory V]
    {A₀ B₀ C₀ A B C' AB₀ BC₀ AB BC D : V}
    (a : A₀ ⟶ A) (b : B₀ ⟶ B) (c : C₀ ⟶ C')
    (t12 : A₀ ⊗ B₀ ⟶ AB₀) (s12 : AB₀ ⟶ AB) (m12 : A ⊗ B ⟶ AB)
    (t23 : B₀ ⊗ C₀ ⟶ BC₀) (s23 : BC₀ ⟶ BC) (m23 : B ⊗ C' ⟶ BC)
    (mL : AB ⊗ C' ⟶ D) (mR : A ⊗ BC ⟶ D)
    (h12 : t12 ≫ s12 = (a ⊗ₘ b) ≫ m12)
    (h23 : t23 ≫ s23 = (b ⊗ₘ c) ≫ m23)
    (hassoc : (α_ A B C').inv ≫ (m12 ⊗ₘ 𝟙 C') ≫ mL =
      (𝟙 A ⊗ₘ m23) ≫ mR) :
    (α_ A₀ B₀ C₀).inv ≫ (t12 ⊗ₘ 𝟙 C₀) ≫ (s12 ⊗ₘ c) ≫ mL =
      (𝟙 A₀ ⊗ₘ t23) ≫ (a ⊗ₘ s23) ≫ mR := by
  have ht12 :
      (t12 ⊗ₘ 𝟙 C₀) ≫ (s12 ⊗ₘ c) =
        (t12 ≫ s12) ⊗ₘ c := by
    calc
      _ = (t12 ≫ s12) ⊗ₘ ((𝟙 C₀) ≫ c) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = _ := by rw [Category.id_comp]
  have hfactorL :
      (((a ⊗ₘ b) ≫ m12) ⊗ₘ c) =
        ((a ⊗ₘ b) ⊗ₘ c) ≫ (m12 ⊗ₘ 𝟙 C') := by
    calc
      _ = (((a ⊗ₘ b) ≫ m12) ⊗ₘ (c ≫ 𝟙 C')) := by rw [Category.comp_id]
      _ = _ := (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
  have hfactorR :
      (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 A ⊗ₘ m23) =
        a ⊗ₘ ((b ⊗ₘ c) ≫ m23) := by
    calc
      _ = (a ≫ 𝟙 A) ⊗ₘ ((b ⊗ₘ c) ≫ m23) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = _ := by rw [Category.comp_id]
  have hfactorFinal :
      (𝟙 A₀ ⊗ₘ t23) ≫ (a ⊗ₘ s23) =
        a ⊗ₘ (t23 ≫ s23) := by
    calc
      _ = ((𝟙 A₀) ≫ a) ⊗ₘ (t23 ≫ s23) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = _ := by rw [Category.id_comp]
  have h1 := congrArg
    (fun t => (α_ A₀ B₀ C₀).inv ≫ t ≫ mL) ht12
  have h2 := congrArg
    (fun t => (α_ A₀ B₀ C₀).inv ≫ (t ⊗ₘ c) ≫ mL) h12
  have h3 := congrArg
    (fun t => (α_ A₀ B₀ C₀).inv ≫ t ≫ mL) hfactorL
  have h4 := congrArg
    (fun t => t ≫ (m12 ⊗ₘ 𝟙 C') ≫ mL)
    (MonoidalCategory.associator_inv_naturality a b c)
  have h5 := congrArg (fun t => (a ⊗ₘ (b ⊗ₘ c)) ≫ t) hassoc
  have h6 := congrArg (fun t => t ≫ mR) hfactorR
  have h7 := congrArg (fun t => (a ⊗ₘ t) ≫ mR) h23.symm
  have h8 := congrArg (fun t => t ≫ mR) hfactorFinal.symm
  have h1' := h1
  have h2' := h2
  have h3' := h3
  have h4' := h4.symm
  have h5' := h5
  have h6' := h6
  have h7' := h7
  have h8' := h8
  simp only [Category.assoc] at h1' h2' h3' h4' h5' h6' h7' h8'
  exact h1'.trans (h2'.trans (h3'.trans (h4'.trans
    (h5'.trans (h6'.trans (h7'.trans h8'))))))

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
