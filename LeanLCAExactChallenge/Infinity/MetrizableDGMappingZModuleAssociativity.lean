import LeanLCAExactChallenge.Infinity.AlexanderWhitneyCoassociativity
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule

/-!
# Associativity of direct integer-module dg composition

This file proves componentwise and chain-level associativity of the direct truncated Hom
composition.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open CategoryTheory.MonoidalCategory

abbrev DirectMappingChain (K L : ComplexCategory) :=
  dgMappingDirectZModuleChainComplex K L

@[reassoc]
lemma ιTensorObj_tensorHom_direct
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫
        HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

theorem dgTruncatedCompositionComponentReversed_assoc
    (W X Y Z : ComplexCategory) {p q r n : ℕ} (h : p + q + r = n) :
    (α_ ((DirectMappingChain X W).X p)
          ((DirectMappingChain Y X).X q)
          ((DirectMappingChain Z Y).X r)).inv ≫
        (dgTruncatedCompositionComponentReversed Y X W
              (show p + q = p + q by rfl) ⊗ₘ
            𝟙 ((DirectMappingChain Z Y).X r)) ≫
        dgTruncatedCompositionComponentReversed Z Y W
          (show (p + q) + r = n by exact h) =
      (𝟙 ((DirectMappingChain X W).X p) ⊗ₘ
          dgTruncatedCompositionComponentReversed Z Y X
            (show q + r = q + r by rfl)) ≫
        dgTruncatedCompositionComponentReversed Z X W
          (show p + (q + r) = n by omega) := by
  apply (cancel_mono
    (((dgHomZModuleCochainComplex Z W).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  conv_lhs => erw [Category.assoc]
  conv_lhs => erw [Category.assoc]
  conv_rhs => erw [Category.assoc]
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro a b c
  change
    dgTruncatedCompositionToCochain Z Y W
          (show (p + q) + r = n by exact h)
        ((dgTruncatedCompositionComponentReversed Y X W
              (show p + q = p + q by rfl) ⊗ₘ
            𝟙 ((DirectMappingChain Z Y).X r))
          ((α_ ((DirectMappingChain X W).X p)
            ((DirectMappingChain Y X).X q)
            ((DirectMappingChain Z Y).X r)).inv
              (a ⊗ₜ[ℤ] (b ⊗ₜ[ℤ] c)))) =
      dgTruncatedCompositionToCochain Z X W
          (show p + (q + r) = n by omega)
        ((𝟙 ((DirectMappingChain X W).X p) ⊗ₘ
            dgTruncatedCompositionComponentReversed Z Y X
              (show q + r = q + r by rfl))
          (a ⊗ₜ[ℤ] (b ⊗ₜ[ℤ] c)))
  change
    dgTruncatedCompositionToCochain Z Y W
          (show (p + q) + r = n by exact h)
        (dgTruncatedCompositionComponentReversed Y X W
            (show p + q = p + q by rfl) (a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] c) =
      dgTruncatedCompositionToCochain Z X W
          (show p + (q + r) = n by omega)
        (a ⊗ₜ[ℤ]
          dgTruncatedCompositionComponentReversed Z Y X
            (show q + r = q + r by rfl) (b ⊗ₜ[ℤ] c))
  rw [dgTruncatedCompositionToCochain_tmul,
    dgTruncatedCompositionToCochain_tmul]
  have hab := ConcreteCategory.congr_hom
    (dgTruncatedCompositionComponentReversed_toRestriction Y X W
      (show p + q = p + q by rfl)) (a ⊗ₜ[ℤ] b)
  have hbc := ConcreteCategory.congr_hom
    (dgTruncatedCompositionComponentReversed_toRestriction Z Y X
      (show q + r = q + r by rfl)) (b ⊗ₜ[ℤ] c)
  have hab' :
      ((dgHomZModuleCochainComplex Y W).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f (p + q)
          (dgTruncatedCompositionComponentReversed Y X W
            (show p + q = p + q by rfl) (a ⊗ₜ[ℤ] b)) =
        dgTruncatedCompositionToCochain Y X W
          (show p + q = p + q by rfl) (a ⊗ₜ[ℤ] b) := by
    exact hab
  have hbc' :
      ((dgHomZModuleCochainComplex Z X).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f (q + r)
          (dgTruncatedCompositionComponentReversed Z Y X
            (show q + r = q + r by rfl) (b ⊗ₜ[ℤ] c)) =
        dgTruncatedCompositionToCochain Z Y X
          (show q + r = q + r by rfl) (b ⊗ₜ[ℤ] c) := by
    exact hbc
  rw [hab', hbc']
  rw [dgTruncatedCompositionToCochain_tmul,
    dgTruncatedCompositionToCochain_tmul]
  let a' := ((dgHomZModuleCochainComplex X W).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f p a
  let b' := ((dgHomZModuleCochainComplex Y X).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f q b
  let c' := ((dgHomZModuleCochainComplex Z Y).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f r c
  exact (CochainComplex.HomComplex.Cochain.comp_assoc c' b' a'
    (by dsimp [a', b', c']; omega)
    (by dsimp [a', b', c']; omega)
    (by dsimp [a', b', c']; omega)).symm

theorem dgTruncatedCompositionReversed_assoc
    (W X Y Z : ComplexCategory) :
    (α_ (DirectMappingChain X W)
          (DirectMappingChain Y X)
          (DirectMappingChain Z Y)).inv ≫
        dgTruncatedCompositionReversed Y X W ▷
            DirectMappingChain Z Y ≫
        dgTruncatedCompositionReversed Z Y W =
      DirectMappingChain X W ◁
          dgTruncatedCompositionReversed Z Y X ≫
        dgTruncatedCompositionReversed Z X W := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply GradedObject.Monoidal.tensorObj₃_ext
  intro p q r h
  simp only [HomologicalComplex.comp_f]
  have hassoc :
      (α_ (DirectMappingChain X W)
        (DirectMappingChain Y X)
        (DirectMappingChain Z Y)).inv.f n =
        (GradedObject.Monoidal.associator
          (DirectMappingChain X W).X
          (DirectMappingChain Y X).X
          (DirectMappingChain Z Y).X).inv n := rfl
  rw [hassoc]
  have hi := GradedObject.Monoidal.ιTensorObj₃_associator_inv
    (X₁ := (DirectMappingChain X W).X)
    (X₂ := (DirectMappingChain Y X).X)
    (X₃ := (DirectMappingChain Z Y).X) p q r n h
  have hiFull :
      GradedObject.Monoidal.ιTensorObj₃
            (DirectMappingChain X W).X
            (DirectMappingChain Y X).X
            (DirectMappingChain Z Y).X p q r n h ≫
          (GradedObject.Monoidal.associator
            (DirectMappingChain X W).X
            (DirectMappingChain Y X).X
            (DirectMappingChain Z Y).X).inv n ≫
          (dgTruncatedCompositionReversed Y X W ▷
            DirectMappingChain Z Y).f n ≫
          (dgTruncatedCompositionReversed Z Y W).f n =
        (α_ ((DirectMappingChain X W).X p)
            ((DirectMappingChain Y X).X q)
            ((DirectMappingChain Z Y).X r)).inv ≫
          GradedObject.Monoidal.ιTensorObj₃'
            (DirectMappingChain X W).X
            (DirectMappingChain Y X).X
            (DirectMappingChain Z Y).X p q r n h ≫
          (dgTruncatedCompositionReversed Y X W ▷
            DirectMappingChain Z Y).f n ≫
          (dgTruncatedCompositionReversed Z Y W).f n := by
    simpa only [Category.assoc] using congrArg
      (fun t => t ≫
        (dgTruncatedCompositionReversed Y X W ▷
          DirectMappingChain Z Y).f n ≫
        (dgTruncatedCompositionReversed Z Y W).f n) hi
  refine hiFull.trans ?_
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq
    (DirectMappingChain X W).X
    (DirectMappingChain Y X).X
    (DirectMappingChain Z Y).X p q r n h (p + q) rfl]
  rw [GradedObject.Monoidal.ιTensorObj₃_eq
    (DirectMappingChain X W).X
    (DirectMappingChain Y X).X
    (DirectMappingChain Z Y).X p q r n h (q + r) rfl]
  have hwr :
      (dgTruncatedCompositionReversed Y X W ▷
          DirectMappingChain Z Y).f n =
        (HomologicalComplex.tensorHom
          (dgTruncatedCompositionReversed Y X W)
          (𝟙 (DirectMappingChain Z Y))).f n := rfl
  have hwl :
      (DirectMappingChain X W ◁
          dgTruncatedCompositionReversed Z Y X).f n =
        (HomologicalComplex.tensorHom
          (𝟙 (DirectMappingChain X W))
          (dgTruncatedCompositionReversed Z Y X)).f n := rfl
  rw [hwr, hwl]
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj
              (DirectMappingChain X W).X
              (DirectMappingChain Y X).X)
            (DirectMappingChain Z Y).X (p + q) r n h ≫
          (HomologicalComplex.tensorHom
            (dgTruncatedCompositionReversed Y X W)
            (𝟙 (DirectMappingChain Z Y))).f n =
        ((dgTruncatedCompositionReversed Y X W).f (p + q) ⊗ₘ
            𝟙 ((DirectMappingChain Z Y).X r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (DirectMappingChain Y W).X
            (DirectMappingChain Z Y).X (p + q) r n h := by
    change
      HomologicalComplex.ιTensorObj
            (HomologicalComplex.tensorObj
              (DirectMappingChain X W) (DirectMappingChain Y X))
            (DirectMappingChain Z Y) (p + q) r n h ≫
          (HomologicalComplex.tensorHom
            (dgTruncatedCompositionReversed Y X W)
            (𝟙 (DirectMappingChain Z Y))).f n =
        (((dgTruncatedCompositionReversed Y X W).f (p + q) ⊗ₘ
            𝟙 ((DirectMappingChain Z Y).X r)) ≫
          HomologicalComplex.ιTensorObj
            (DirectMappingChain Y W) (DirectMappingChain Z Y)
            (p + q) r n h)
    exact ιTensorObj_tensorHom_direct
      (dgTruncatedCompositionReversed Y X W)
      (𝟙 (DirectMappingChain Z Y)) h
  have houterR :
      GradedObject.Monoidal.ιTensorObj
            (DirectMappingChain X W).X
            (GradedObject.Monoidal.tensorObj
              (DirectMappingChain Y X).X
              (DirectMappingChain Z Y).X)
            p (q + r) n (show p + (q + r) = n by omega) ≫
          (HomologicalComplex.tensorHom
            (𝟙 (DirectMappingChain X W))
            (dgTruncatedCompositionReversed Z Y X)).f n =
        (𝟙 ((DirectMappingChain X W).X p) ⊗ₘ
            (dgTruncatedCompositionReversed Z Y X).f (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (DirectMappingChain X W).X
            (DirectMappingChain Z X).X p (q + r) n
              (show p + (q + r) = n by omega) := by
    change
      HomologicalComplex.ιTensorObj
            (DirectMappingChain X W)
            (HomologicalComplex.tensorObj
              (DirectMappingChain Y X) (DirectMappingChain Z Y))
            p (q + r) n (show p + (q + r) = n by omega) ≫
          (HomologicalComplex.tensorHom
            (𝟙 (DirectMappingChain X W))
            (dgTruncatedCompositionReversed Z Y X)).f n =
        ((𝟙 ((DirectMappingChain X W).X p) ⊗ₘ
            (dgTruncatedCompositionReversed Z Y X).f (q + r)) ≫
          HomologicalComplex.ιTensorObj
            (DirectMappingChain X W) (DirectMappingChain Z X)
            p (q + r) n (show p + (q + r) = n by omega))
    exact ιTensorObj_tensorHom_direct
      (𝟙 (DirectMappingChain X W))
      (dgTruncatedCompositionReversed Z Y X)
      (show p + (q + r) = n by omega)
  simp only [Category.assoc]
  have hleftRaw := congrArg
    (fun t =>
      (α_ ((DirectMappingChain X W).X p)
          ((DirectMappingChain Y X).X q)
          ((DirectMappingChain Z Y).X r)).inv ≫
        (GradedObject.Monoidal.ιTensorObj
            (DirectMappingChain X W).X
            (DirectMappingChain Y X).X p q (p + q) rfl ▷
          (DirectMappingChain Z Y).X r) ≫
        t ≫ (dgTruncatedCompositionReversed Z Y W).f n)
    houterL
  have hrightRaw := congrArg
    (fun t =>
      ((DirectMappingChain X W).X p ◁
          GradedObject.Monoidal.ιTensorObj
            (DirectMappingChain Y X).X
            (DirectMappingChain Z Y).X q r (q + r) rfl) ≫
        t ≫ (dgTruncatedCompositionReversed Z X W).f n)
    houterR
  have hleft := hleftRaw
  have hright := hrightRaw
  simp only [Category.assoc] at hleft hright
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  have hcompL₀ :=
    ιTensorObj_dgTruncatedCompositionDegreeReversed
      Y X W (show p + q = p + q by rfl)
  have hcompL := congrArg
    (fun t => t ▷ (DirectMappingChain Z Y).X r) hcompL₀
  simp only [MonoidalCategory.comp_whiskerRight] at hcompL
  have houterCompL :=
    ιTensorObj_dgTruncatedCompositionDegreeReversed
      Z Y W (show (p + q) + r = n by exact h)
  have hcompR₀ :=
    ιTensorObj_dgTruncatedCompositionDegreeReversed
      Z Y X (show q + r = q + r by rfl)
  have hcompR := congrArg
    (fun t => (DirectMappingChain X W).X p ◁ t) hcompR₀
  simp only [MonoidalCategory.whiskerLeft_comp] at hcompR
  have houterCompR :=
    ιTensorObj_dgTruncatedCompositionDegreeReversed
      Z X W (show p + (q + r) = n by omega)
  have hL₁Raw := congrArg
    (fun t =>
      (α_ ((DirectMappingChain X W).X p)
          ((DirectMappingChain Y X).X q)
          ((DirectMappingChain Z Y).X r)).inv ≫
        t ≫
        GradedObject.Monoidal.ιTensorObj
          (DirectMappingChain Y W).X
          (DirectMappingChain Z Y).X (p + q) r n h ≫
        (dgTruncatedCompositionReversed Z Y W).f n)
    hcompL
  have hL₂Raw := congrArg
    (fun t =>
      (α_ ((DirectMappingChain X W).X p)
          ((DirectMappingChain Y X).X q)
          ((DirectMappingChain Z Y).X r)).inv ≫
        (dgTruncatedCompositionComponentReversed Y X W
            (show p + q = p + q by rfl) ▷
          (DirectMappingChain Z Y).X r) ≫ t)
    houterCompL
  have hR₁Raw := congrArg
    (fun t =>
      t ≫
        GradedObject.Monoidal.ιTensorObj
          (DirectMappingChain X W).X
          (DirectMappingChain Z X).X p (q + r) n
            (show p + (q + r) = n by omega) ≫
        (dgTruncatedCompositionReversed Z X W).f n)
    hcompR
  have hR₂Raw := congrArg
    (fun t =>
      ((DirectMappingChain X W).X p ◁
          dgTruncatedCompositionComponentReversed Z Y X
            (show q + r = q + r by rfl)) ≫ t)
    houterCompR
  have hL₁ := hL₁Raw
  have hL₂ := hL₂Raw
  have hR₁ := hR₁Raw
  have hR₂ := hR₂Raw
  simp only [Category.assoc] at hL₁ hL₂ hR₁ hR₂
  have hleftComponents := hL₁.trans hL₂
  have hrightComponents := hR₁.trans hR₂
  have hmiddle :=
    dgTruncatedCompositionComponentReversed_assoc W X Y Z h
  exact hleftComponents.trans (hmiddle.trans hrightComponents.symm)

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
