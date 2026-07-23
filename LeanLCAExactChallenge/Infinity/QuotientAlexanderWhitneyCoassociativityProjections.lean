/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitney

/-!
# Alexander--Whitney coassociativity

This file proves the coassociativity law for the unnormalized Alexander--Whitney chain map.
The proof compares the two iterated maps on every triple tensor summand.
-/

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

theorem aw_front_front (p q r : ℕ) :
    SimplexCategory.subinterval (n := p + q) 0 p (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) 0 (p + q) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) 0 p (by omega) := by
  ext i
  simp [SimplexCategory.subinterval]

theorem aw_middle_left (p q r : ℕ) :
    SimplexCategory.subinterval (n := p + q) p q (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) 0 (p + q) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) p q (by omega) := by
  ext i
  simp [SimplexCategory.subinterval]

theorem aw_middle_right (p q r : ℕ) :
    SimplexCategory.subinterval (n := q + r) 0 q (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) p (q + r) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) p q (by omega) := by
  ext i
  simp [SimplexCategory.subinterval, Nat.add_comm]

theorem aw_back_back (p q r : ℕ) :
    SimplexCategory.subinterval (n := q + r) q r (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) p (q + r) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) (p + q) r (by omega) := by
  ext i
  simp [SimplexCategory.subinterval, Nat.add_comm, Nat.add_left_comm]

variable (X Y Z : SimplicialObject (QuotientModule))

abbrev complexTensorFamily
    (K L : ChainComplex (QuotientModule) ℕ) (n : ℕ) :=
  (((((curriedTensor (QuotientModule)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) n)

def complexTensorPairProjection
    (K L : ChainComplex (QuotientModule) ℕ)
    (i j n : ℕ) (h : i + j = n) :
    (K ⊗ L).X n ⟶ K.X i ⊗ L.X j :=
  Sigma.π (complexTensorFamily K L n)
    ⟨⟨i, j⟩, by change i + j = n; exact h⟩

@[simp]
theorem complexTensorPairProjection_alternating
    (A B : SimplicialObject (QuotientModule))
    (i j n : ℕ) (h : i + j = n) :
    complexTensorPairProjection (alternatingChains A) (alternatingChains B)
        i j n h = tensorPairProjection A B i j n h := rfl

theorem alternatingAlexanderWhitney_comp_complexTensorPairProjection
    (A B : SimplicialObject (QuotientModule))
    (i j n : ℕ) (h : i + j = n) :
    (alternatingAlexanderWhitney A B).f n ≫
        complexTensorPairProjection (alternatingChains A) (alternatingChains B)
          i j n h =
      A.map (SimplexCategory.subinterval (n := n) 0 i (by omega)).op ⊗ₘ
        B.map (SimplexCategory.subinterval (n := n) i j (by omega)).op := by
  subst n
  rw [alternatingAlexanderWhitney_f,
    complexTensorPairProjection_alternating,
    alternatingAlexanderWhitneyDegree_comp_pairProjection]

theorem tensorHom_comp_complexTensorPairProjection
    {K₁ K₂ L₁ L₂ : ChainComplex (QuotientModule) ℕ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    (i j n : ℕ) (h : i + j = n) :
    (HomologicalComplex.tensorHom f g).f n ≫
        complexTensorPairProjection L₁ L₂ i j n h =
      complexTensorPairProjection K₁ K₂ i j n h ≫
        (f.f i ⊗ₘ g.f j) := by
  apply Sigma.hom_ext
  rintro ⟨⟨a, b⟩, hab⟩
  change a + b = n at hab
  by_cases hai : a = i
  · subst a
    have hbj : b = j := by omega
    subst b
    have hL :
        Sigma.ι (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, h⟩ = 𝟙 _ := by
      convert Sigma.ι_π_eq_id (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, hab⟩
    have hK :
        Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩ = 𝟙 _ := by
      convert Sigma.ι_π_eq_id (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩
    have hK' :
        (Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩) ≫
            (f.f i ⊗ₘ g.f j) = f.f i ⊗ₘ g.f j := by
      rw [hK, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    dsimp only [complexTensorPairProjection, complexTensorFamily,
      HomologicalComplex.ιMapBifunctor,
      HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    erw [hL, hK']
    change (f.f i ▷ K₂.X j ≫ L₁.X i ◁ g.f j) ≫
      𝟙 (L₁.X i ⊗ L₂.X j) = f.f i ⊗ₘ g.f j
    rw [Category.comp_id]
    exact (MonoidalCategory.tensorHom_def (f.f i) (g.f j)).symm
  · have hpairs : (a, b) ≠ (i, j) := by
      intro hp
      exact hai (congrArg Prod.fst hp)
    have hLzero :
        Sigma.ι (complexTensorFamily L₁ L₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, h⟩ = 0 := by
      apply Sigma.ι_π_of_ne
      intro hs
      exact hpairs (congrArg Subtype.val hs)
    have hKzero :
        Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩ = 0 := by
      apply Sigma.ι_π_of_ne
      intro hs
      exact hpairs (congrArg Subtype.val hs)
    have hKzero' :
        (Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩) ≫
            (f.f i ⊗ₘ g.f j) = 0 := by
      rw [hKzero, zero_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    dsimp only [complexTensorPairProjection, complexTensorFamily,
      HomologicalComplex.ιMapBifunctor,
      HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    erw [hLzero, hKzero']
    exact comp_zero

def complexRightTripleProjection
    (K L M : ChainComplex (QuotientModule) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    (K ⊗ (L ⊗ M)).X n ⟶ K.X p ⊗ (L.X q ⊗ M.X r) :=
  complexTensorPairProjection K (HomologicalComplex.tensorObj L M)
      p (q + r) n (by omega) ≫
    (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r (q + r) rfl)

theorem aw_right_iterated_projection (p q r : ℕ) :
    (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫
        (HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z)).f (p + q + r) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      X.map
            (SimplexCategory.subinterval
              (n := p + q + r) 0 p (by omega)).op ⊗ₘ
        (Y.map
              (SimplexCategory.subinterval
                (n := p + q + r) p q (by omega)).op ⊗ₘ
          Z.map
            (SimplexCategory.subinterval
              (n := p + q + r) (p + q) r (by omega)).op) := by
  have hproj := tensorHom_comp_complexTensorPairProjection
    (𝟙 (alternatingChains X)) (alternatingAlexanderWhitney Y Z)
    p (q + r) (p + q + r) (by omega)
  have hcomp := congrArg
    (fun t =>
      (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫ t ≫
        (𝟙 ((alternatingChains X).X p) ⊗ₘ
          complexTensorPairProjection (alternatingChains Y) (alternatingChains Z)
            q r (q + r) rfl)) hproj
  calc
    _ = (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫
        complexTensorPairProjection (alternatingChains X)
          (alternatingChains (Y ⊗ Z)) p (q + r) (p + q + r) (by omega) ≫
        ((((𝟙 (alternatingChains X) :
              alternatingChains X ⟶ alternatingChains X).f p) ⊗ₘ
            (alternatingAlexanderWhitney Y Z).f (q + r)) ≫
          (𝟙 ((alternatingChains X).X p) ⊗ₘ
            complexTensorPairProjection (alternatingChains Y) (alternatingChains Z)
              q r (q + r) rfl)) := by
      simpa only [complexRightTripleProjection, Category.assoc] using hcomp
    _ = _ := by
      simp only [HomologicalComplex.id_f, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]
      rw [← Category.assoc,
        alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      rw [alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      simp only [Monoidal.tensorObj_map]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [Category.comp_id]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [← Y.map_comp, ← Z.map_comp]
      simp only [← op_comp]
      rw [aw_middle_right, aw_back_back]


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
