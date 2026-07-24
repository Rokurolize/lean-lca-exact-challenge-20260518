/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusionFunctor
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainEnrichedCategory

/-! # The smart-truncated coefficient-changed original DG category -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

/-- The coefficient-changed original Hom after nonpositive smart truncation. -/
def originalCoefficientDGChainEnrichedHom
    (K L : OriginalCoefficientDGCategory) : QuotientDGChain :=
  (originalCoefficientDGEnrichedHom K L).truncLE' ComplexShape.embeddingDownNat

/-- Composition on the smart-truncated coefficient-changed original Hom complexes. -/
def originalCoefficientDGChainEnrichedComp
    (K L M : OriginalCoefficientDGCategory) :
    originalCoefficientDGChainEnrichedHom K L ⊗
        originalCoefficientDGChainEnrichedHom L M ⟶
      originalCoefficientDGChainEnrichedHom K M :=
  quotientTruncatedMap (originalCoefficientDGEnrichedComp K L M)

lemma OriginalCoefficientDGIdentitySpan_d (K : ComplexCategory) :
    OriginalCoefficientDGIdentitySpan K ≫
      (OriginalCoefficientCochainComplex K K).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.down_injective
  apply ULift.down_injective
  change ((dgHomZModuleCochainComplex K K).d 0 1).hom
    (x.down • identityCochain K) = 0
  calc
    _ = x.down • ((dgHomZModuleCochainComplex K K).d 0 1).hom
        (identityCochain K) :=
      ((dgHomZModuleCochainComplex K K).d 0 1).hom.toAddMonoidHom.map_zsmul _ _
    _ = 0 := by rw [identityCochain_d, zsmul_zero]

/-- The original identity cocycle in smart-truncation degree zero. -/
def originalCoefficientDGChainIdentityDegreeZero
    (K : OriginalCoefficientDGCategory) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (originalCoefficientDGChainEnrichedHom K K).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  exact
    (originalCoefficientDGEnrichedHom K K).liftCycles'
        (OriginalCoefficientDGIdentitySpan K.unop) 1 rfl
        (OriginalCoefficientDGIdentitySpan_d K.unop) ≫
      ((originalCoefficientDGEnrichedHom K K).truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv

lemma originalCoefficientDGChainIdentityDegreeZero_toRestriction
    (K : OriginalCoefficientDGCategory) :
    originalCoefficientDGChainIdentityDegreeZero K ≫
        ((originalCoefficientDGEnrichedHom K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      OriginalCoefficientDGIdentitySpan K.unop := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [quotientTruncLEToRestriction_f_zero _ hb]
  dsimp [originalCoefficientDGChainIdentityDegreeZero]
  simp only [Category.assoc]
  erw [quotientTruncLEIsoCycles_inv_hom_of_proofs_assoc
    (originalCoefficientDGEnrichedHom K K) 0 0 rfl rfl hb hb]
  simp

/-- Identity chain map for the smart-truncated coefficient-changed original category. -/
def originalCoefficientDGChainEnrichedId
    (K : OriginalCoefficientDGCategory) :
    𝟙_ QuotientDGChain ⟶ originalCoefficientDGChainEnrichedHom K K :=
  (ChainComplex.fromSingle₀Equiv
    (originalCoefficientDGChainEnrichedHom K K)
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).symm
      (originalCoefficientDGChainIdentityDegreeZero K)

@[simp]
lemma originalCoefficientDGChainEnrichedId_f_zero
    (K : OriginalCoefficientDGCategory) :
    (originalCoefficientDGChainEnrichedId K).f 0 =
      originalCoefficientDGChainIdentityDegreeZero K := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (originalCoefficientDGChainIdentityDegreeZero K)

lemma originalDGCompositionComponent_identity_left_apply
    (K L : ComplexCategory) (n : ℤ)
    (x : OriginalCoefficientModule ((dgHomZModuleCochainComplex L K).X n)) :
    (originalDGCompositionComponent L K K (zero_add n)).hom
        ((OriginalCoefficientDGIdentitySpan K).hom 1 ⊗ₜ[QuotientCoefficientRing] x) = x := by
  rcases x with ⟨x⟩
  rcases x with ⟨x⟩
  rw [show (OriginalCoefficientDGIdentitySpan K).hom 1 =
      ULift.up (ULift.up (identityCochain K)) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [originalDGCompositionComponent_tmul]
  apply ULift.down_injective
  apply ULift.down_injective
  exact dgCochainCompTensorReversed_tmul L K K (zero_add n)
    (identityCochain K) x |>.trans
      (dgCochainCompTensorOfEq_tmul_identity_right L K n x)

lemma originalDGCompositionComponent_identity_right_apply
    (K L : ComplexCategory) (n : ℤ)
    (x : OriginalCoefficientModule ((dgHomZModuleCochainComplex L K).X n)) :
    (originalDGCompositionComponent L L K (add_zero n)).hom
        (x ⊗ₜ[QuotientCoefficientRing] (OriginalCoefficientDGIdentitySpan L).hom 1) = x := by
  rcases x with ⟨x⟩
  rcases x with ⟨x⟩
  rw [show (OriginalCoefficientDGIdentitySpan L).hom 1 =
      ULift.up (ULift.up (identityCochain L)) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [originalDGCompositionComponent_tmul]
  apply ULift.down_injective
  apply ULift.down_injective
  exact dgCochainCompTensorReversed_tmul L L K (add_zero n)
    x (identityCochain L) |>.trans
      (dgCochainCompTensorOfEq_identity_left_tmul L K n x)

@[reassoc]
lemma originalChain_ιTensorObj_tensorHom
    {K₁ K₂ L₁ L₂ : QuotientDGChain} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

theorem originalCoefficientDGChainEnrichedId_comp
    (K L : OriginalCoefficientDGCategory) :
    (λ_ (originalCoefficientDGChainEnrichedHom K L)).inv ≫
        originalCoefficientDGChainEnrichedId K ▷
          originalCoefficientDGChainEnrichedHom K L ≫
        originalCoefficientDGChainEnrichedComp K K L = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change ((((HomologicalComplex.leftUnitor'
      (originalCoefficientDGChainEnrichedHom K L)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (originalCoefficientDGChainEnrichedId K)
      (𝟙 (originalCoefficientDGChainEnrichedHom K L))).f n
    rw [originalChain_ιTensorObj_tensorHom]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [originalCoefficientDGChainEnrichedComp]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (originalCoefficientDGChainEnrichedHom K K)
      (originalCoefficientDGChainEnrichedHom K L) 0 n n (zero_add n) ≫
        quotientTruncatedMapDegree (originalCoefficientDGEnrichedComp K K L) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp K K L) (zero_add n)
  erw [quotientTruncatedMapComponent_toRestriction]
  dsimp [quotientTruncatedMapToCochain]
  simp only [Category.assoc, Category.id_comp,
    MonoidalCategory.id_whiskerRight]
  rw [originalCoefficientDGChainEnrichedId_f_zero]
  slice_lhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [originalCoefficientDGChainIdentityDegreeZero_toRestriction]
  simp only [Category.assoc]
  dsimp only [originalCoefficientDGEnrichedHom,
    originalCoefficientDGEnrichedComp]
  rw [ιTensorObj_originalDGComposition]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact originalDGCompositionComponent_identity_left_apply
    K.unop L.unop (-(n : ℤ)) _

theorem originalCoefficientDGChainEnriched_comp_id
    (K L : OriginalCoefficientDGCategory) :
    (ρ_ (originalCoefficientDGChainEnrichedHom K L)).inv ≫
        originalCoefficientDGChainEnrichedHom K L ◁
          originalCoefficientDGChainEnrichedId L ≫
        originalCoefficientDGChainEnrichedComp K L L = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change ((((HomologicalComplex.rightUnitor'
      (originalCoefficientDGChainEnrichedHom K L)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.rightUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (𝟙 (originalCoefficientDGChainEnrichedHom K L))
      (originalCoefficientDGChainEnrichedId L)).f n
    rw [originalChain_ιTensorObj_tensorHom]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [originalCoefficientDGChainEnrichedComp]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (originalCoefficientDGChainEnrichedHom K L)
      (originalCoefficientDGChainEnrichedHom L L) n 0 n (add_zero n) ≫
        quotientTruncatedMapDegree (originalCoefficientDGEnrichedComp K L L) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp K L L) (add_zero n)
  erw [quotientTruncatedMapComponent_toRestriction]
  dsimp [quotientTruncatedMapToCochain]
  simp only [Category.assoc, Category.id_comp,
    MonoidalCategory.whiskerLeft_id]
  rw [originalCoefficientDGChainEnrichedId_f_zero]
  slice_lhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [originalCoefficientDGChainIdentityDegreeZero_toRestriction]
  simp only [Category.assoc]
  dsimp only [originalCoefficientDGEnrichedHom,
    originalCoefficientDGEnrichedComp]
  rw [ιTensorObj_originalDGComposition]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact originalDGCompositionComponent_identity_right_apply
    K.unop L.unop (-(n : ℤ)) _

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
