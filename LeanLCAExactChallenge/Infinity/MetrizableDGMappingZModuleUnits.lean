/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule

/-!
# Units for the direct integer-module dg mapping complexes

This file constructs the identity cocycle and the corresponding chain map into each direct
truncated Hom complex. It proves the two chain-level unit laws for truncated composition.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

private lemma boundaryLE_embeddingDownNat_iff_local (n : ℕ) :
    ComplexShape.embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
    ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 n

private lemma truncLEToRestriction_f_zero_local
    (H : CochainComplex (ModuleCat ℤ) ℤ)
    (hb : ComplexShape.embeddingDownNat.BoundaryLE 0) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 =
      (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
        H.iCycles 0 := by
  dsimp [HomologicalComplex.truncLE'ToRestriction]
  have h0 : ComplexShape.embeddingDownNat.op.f 0 = (0 : ℤ) := rfl
  have hb' : ComplexShape.embeddingDownNat.op.BoundaryGE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    ComplexShape.embeddingDownNat.op h0 hb']
  dsimp [HomologicalComplex.restrictionXIso]
  simp only [Category.comp_id]
  dsimp [HomologicalComplex.truncLE'XIsoCycles, HomologicalComplex.iCycles,
    HomologicalComplex.pOpcycles]
  rw [Category.assoc]
  congr 1
  dsimp only [HomologicalComplex.cycles]
  have hp : (H.opcyclesOpIso 0).hom.unop ≫ ((H.op).pOpcycles 0).unop =
      H.iCycles 0 := by
    dsimp [HomologicalComplex.opcyclesOpIso, HomologicalComplex.pOpcycles,
      HomologicalComplex.iCycles]
    exact congrArg Quiver.Hom.unop
      (H.sc 0).op_pOpcycles_opcyclesOpIso_hom
  have hcancel : (H.opcyclesOpIso 0).hom.unop ≫
      (H.opcyclesOpIso 0).inv.unop = 𝟙 _ :=
    (H.opcyclesOpIso 0).unop.hom_inv_id
  apply (cancel_epi ((H.opcyclesOpIso 0).hom.unop)).1
  calc
    (H.opcyclesOpIso 0).hom.unop ≫ ((H.op).pOpcycles 0).unop =
        H.iCycles 0 := hp
    _ = ((H.opcyclesOpIso 0).hom.unop ≫
          (H.opcyclesOpIso 0).inv.unop) ≫ H.iCycles 0 := by
      rw [hcancel, Category.id_comp]
    _ = (H.opcyclesOpIso 0).hom.unop ≫
        ((H.opcyclesOpIso 0).inv.unop ≫ H.iCycles 0) :=
      Category.assoc _ _ _

@[reassoc]
private lemma truncLEIsoCycles_inv_hom_of_proofs_local
    (H : CochainComplex (ModuleCat ℤ) ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom = 𝟙 _ := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  exact Iso.inv_hom_id _

def dgMappingDirectZModuleIdentityToCochain (K : ComplexCategory) :
    𝟙_ (ModuleCat ℤ) ⟶ (dgHomZModuleCochainComplex K K).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
    (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj)))

lemma dgMappingDirectZModuleIdentityToCochain_d (K : ComplexCategory) :
    dgMappingDirectZModuleIdentityToCochain K ≫
      (dgHomZModuleCochainComplex K K).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  change (CochainComplex.HomComplex.δ_hom ℤ K.obj K.obj 0 1).comp
    (LinearMap.toSpanSingleton ℤ _
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj))) = 0
  rw [LinearMap.comp_toSpanSingleton]
  simp

def dgMappingDirectZModuleIdentityDegreeZero (K : ComplexCategory) :
    𝟙_ (ModuleCat ℤ) ⟶ (dgMappingDirectZModuleChainComplex K K).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff_local 0).2 rfl
  exact
    (dgHomZModuleCochainComplex K K).liftCycles'
        (dgMappingDirectZModuleIdentityToCochain K) 1 rfl
        (dgMappingDirectZModuleIdentityToCochain_d K) ≫
      ((dgHomZModuleCochainComplex K K).truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv

lemma dgMappingDirectZModuleIdentityDegreeZero_toRestriction
    (K : ComplexCategory) :
    dgMappingDirectZModuleIdentityDegreeZero K ≫
        ((dgHomZModuleCochainComplex K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      dgMappingDirectZModuleIdentityToCochain K := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff_local 0).2 rfl
  rw [truncLEToRestriction_f_zero_local _ hb]
  dsimp [dgMappingDirectZModuleIdentityDegreeZero]
  simp only [Category.assoc]
  erw [truncLEIsoCycles_inv_hom_of_proofs_local_assoc
    (dgHomZModuleCochainComplex K K) 0 0 rfl rfl hb hb]
  simp

def dgMappingDirectZModuleChainIdentity (K : ComplexCategory) :
    𝟙_ (ChainComplex (ModuleCat ℤ) ℕ) ⟶
      dgMappingDirectZModuleChainComplex K K :=
  (ChainComplex.fromSingle₀Equiv
    (dgMappingDirectZModuleChainComplex K K) (𝟙_ (ModuleCat ℤ))).symm
      (dgMappingDirectZModuleIdentityDegreeZero K)

@[simp]
lemma dgMappingDirectZModuleChainIdentity_f_zero (K : ComplexCategory) :
    (dgMappingDirectZModuleChainIdentity K).f 0 =
      dgMappingDirectZModuleIdentityDegreeZero K := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (dgMappingDirectZModuleIdentityDegreeZero K)

def dgMappingZModuleChainIdentity (K : ComplexCategory) :
    𝟙_ (ChainComplex (ModuleCat ℤ) ℕ) ⟶
      dgMappingZModuleChainComplex K K :=
  dgMappingDirectZModuleChainIdentity K ≫
    (dgMappingZModuleChainComplexIsoDirect K K).inv

@[reassoc]
lemma ιTensorObj_tensorHom_local
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫
        HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

theorem dgMappingDirectZModuleChainIdentity_comp
    (K L : ComplexCategory) :
    (λ_ (dgMappingDirectZModuleChainComplex L K)).inv ≫
          dgMappingDirectZModuleChainIdentity K ▷
            dgMappingDirectZModuleChainComplex L K ≫
          dgTruncatedCompositionReversed L K K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change ((((HomologicalComplex.leftUnitor'
      (dgMappingDirectZModuleChainComplex L K)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (dgMappingDirectZModuleChainIdentity K)
      (𝟙 (dgMappingDirectZModuleChainComplex L K))).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [dgTruncatedCompositionReversed]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (dgMappingDirectZModuleChainComplex K K)
      (dgMappingDirectZModuleChainComplex L K) 0 n n (zero_add n) ≫
        dgTruncatedCompositionDegreeReversed L K K n
    exact ιTensorObj_dgTruncatedCompositionDegreeReversed
      L K K (zero_add n)
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change _ =
    ((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  rw [dgMappingDirectZModuleChainIdentity_f_zero]
  erw [dgTruncatedCompositionToCochain_tmul]
  change
    (((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n x).comp
      (((dgHomZModuleCochainComplex K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0
        (dgMappingDirectZModuleIdentityDegreeZero K (1 : ℤ))) _ =
      ((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n x
  have hid := ConcreteCategory.congr_hom
    (dgMappingDirectZModuleIdentityDegreeZero_toRestriction K) (1 : ℤ)
  change
    ((dgHomZModuleCochainComplex K K).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0
        (dgMappingDirectZModuleIdentityDegreeZero K (1 : ℤ)) =
      dgMappingDirectZModuleIdentityToCochain K (1 : ℤ) at hid
  dsimp [dgMappingDirectZModuleIdentityToCochain] at hid
  change _ =
    (LinearMap.toSpanSingleton ℤ
      (CochainComplex.HomComplex.Cochain K.obj K.obj 0)
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj))) (1 : ℤ) at hid
  rw [LinearMap.toSpanSingleton_apply_one] at hid
  erw [hid]
  simp

theorem dgMappingDirectZModuleChain_comp_identity
    (K L : ComplexCategory) :
    (ρ_ (dgMappingDirectZModuleChainComplex L K)).inv ≫
          dgMappingDirectZModuleChainComplex L K ◁
            dgMappingDirectZModuleChainIdentity L ≫
          dgTruncatedCompositionReversed L L K = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change ((((HomologicalComplex.rightUnitor'
      (dgMappingDirectZModuleChainComplex L K)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.rightUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (𝟙 (dgMappingDirectZModuleChainComplex L K))
      (dgMappingDirectZModuleChainIdentity L)).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [dgTruncatedCompositionReversed]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (dgMappingDirectZModuleChainComplex L K)
      (dgMappingDirectZModuleChainComplex L L) n 0 n (add_zero n) ≫
        dgTruncatedCompositionDegreeReversed L L K n
    exact ιTensorObj_dgTruncatedCompositionDegreeReversed
      L L K (add_zero n)
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change _ =
    ((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  rw [dgMappingDirectZModuleChainIdentity_f_zero]
  erw [dgTruncatedCompositionToCochain_tmul]
  change
    (((dgHomZModuleCochainComplex L L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0
        (dgMappingDirectZModuleIdentityDegreeZero L (1 : ℤ))).comp
      (((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n x) _ =
      ((dgHomZModuleCochainComplex L K).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n x
  have hid := ConcreteCategory.congr_hom
    (dgMappingDirectZModuleIdentityDegreeZero_toRestriction L) (1 : ℤ)
  change
    ((dgHomZModuleCochainComplex L L).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0
        (dgMappingDirectZModuleIdentityDegreeZero L (1 : ℤ)) =
      dgMappingDirectZModuleIdentityToCochain L (1 : ℤ) at hid
  dsimp [dgMappingDirectZModuleIdentityToCochain] at hid
  change _ =
    (LinearMap.toSpanSingleton ℤ
      (CochainComplex.HomComplex.Cochain L.obj L.obj 0)
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 L.obj))) (1 : ℤ) at hid
  rw [LinearMap.toSpanSingleton_apply_one] at hid
  erw [hid]
  simp

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
