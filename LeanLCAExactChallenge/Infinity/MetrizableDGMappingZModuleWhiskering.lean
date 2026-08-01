/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGStableConstructions

/-!
# Whiskering the direct integer-module DG mapping complexes

Every bounded chain map determines a tensor-unit-shaped element of the smart-truncated direct
mapping complex. Composition with this element agrees with the direct truncation of ordinary
precomposition and postcomposition on the untruncated Hom cochain complexes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

private lemma boundaryLE_embeddingDownNat_iff_whiskering (n : ℕ) :
    ComplexShape.embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
    ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 n

private lemma truncLEToRestriction_f_zero_whiskering
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
    (H.opcyclesOpIso 0).hom.unop ≫ ((H.op).pOpcycles 0).unop = H.iCycles 0 := hp
    _ = ((H.opcyclesOpIso 0).hom.unop ≫
          (H.opcyclesOpIso 0).inv.unop) ≫ H.iCycles 0 := by
      rw [hcancel, Category.id_comp]
    _ = (H.opcyclesOpIso 0).hom.unop ≫
        ((H.opcyclesOpIso 0).inv.unop ≫ H.iCycles 0) := Category.assoc _ _ _

@[reassoc]
private lemma truncLEIsoCycles_inv_hom_of_proofs_whiskering
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

/-- The raw degree-zero cochain represented by a bounded chain map. -/
def dgMappingDirectZModuleMorphismToCochain {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ (ModuleCat ℤ) ⟶ (dgHomZModuleCochainComplex K L).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
    (CochainComplex.HomComplex.Cochain.ofHom f.hom))

lemma dgMappingDirectZModuleMorphismToCochain_d
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleMorphismToCochain f ≫
      (dgHomZModuleCochainComplex K L).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  change (CochainComplex.HomComplex.δ_hom ℤ K.obj L.obj 0 1).comp
    (LinearMap.toSpanSingleton ℤ _
      (CochainComplex.HomComplex.Cochain.ofHom f.hom)) = 0
  rw [LinearMap.comp_toSpanSingleton]
  simp

/-- A bounded chain map as a degree-zero element of the smart-truncated direct Hom complex. -/
def dgMappingDirectZModuleMorphismDegreeZero {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ (ModuleCat ℤ) ⟶ (dgMappingDirectZModuleChainComplex K L).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff_whiskering 0).2 rfl
  exact
    (dgHomZModuleCochainComplex K L).liftCycles'
        (dgMappingDirectZModuleMorphismToCochain f) 1 rfl
        (dgMappingDirectZModuleMorphismToCochain_d f) ≫
      ((dgHomZModuleCochainComplex K L).truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv

lemma dgMappingDirectZModuleMorphismDegreeZero_toRestriction
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleMorphismDegreeZero f ≫
        ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      dgMappingDirectZModuleMorphismToCochain f := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff_whiskering 0).2 rfl
  rw [truncLEToRestriction_f_zero_whiskering _ hb]
  dsimp [dgMappingDirectZModuleMorphismDegreeZero]
  simp only [Category.assoc]
  erw [truncLEIsoCycles_inv_hom_of_proofs_whiskering_assoc
    (dgHomZModuleCochainComplex K L) 0 0 rfl rfl hb hb]
  simp

@[simp]
theorem dgMappingDirectZModuleMorphismDegreeZero_toRestriction_apply_one
    {K L : ComplexCategory} (f : K ⟶ L) :
    (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom
        ((dgMappingDirectZModuleMorphismDegreeZero f).hom (1 : ℤ)) =
      CochainComplex.HomComplex.Cochain.ofHom f.hom := by
  have h := ConcreteCategory.congr_hom
    (dgMappingDirectZModuleMorphismDegreeZero_toRestriction f) (1 : ℤ)
  change _ = (LinearMap.toSpanSingleton ℤ
    (CochainComplex.HomComplex.Cochain K.obj L.obj 0)
    (CochainComplex.HomComplex.Cochain.ofHom f.hom)) (1 : ℤ) at h
  rw [LinearMap.toSpanSingleton_apply_one] at h
  exact h

/-- A bounded chain map as a tensor-unit-shaped morphism into the direct Hom chain complex. -/
def dgMappingDirectZModuleChainMorphismMap {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ DirectZChain ⟶ dgMappingDirectZModuleChainComplex K L :=
  (ChainComplex.fromSingle₀Equiv
    (dgMappingDirectZModuleChainComplex K L) (𝟙_ (ModuleCat ℤ))).symm
      (dgMappingDirectZModuleMorphismDegreeZero f)

@[simp]
theorem dgMappingDirectZModuleChainMorphismMap_f_zero
    {K L : ComplexCategory} (f : K ⟶ L) :
    (dgMappingDirectZModuleChainMorphismMap f).f 0 =
      dgMappingDirectZModuleMorphismDegreeZero f :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

/-- Postcomposition by a bounded chain map on untruncated DG Hom complexes. -/
def dgHomZModulePostcomposition (K : ComplexCategory)
    {L M : ComplexCategory} (g : L ⟶ M) :
    dgHomZModuleCochainComplex K L ⟶ dgHomZModuleCochainComplex K M where
  f n := ModuleCat.ofHom
    { toFun := fun γ ↦ γ.comp
        (CochainComplex.HomComplex.Cochain.ofHom g.hom) (add_zero n)
      map_add' := fun γ γ' ↦
        CochainComplex.HomComplex.Cochain.add_comp γ γ' _ (add_zero n)
      map_smul' := fun r γ ↦
        CochainComplex.HomComplex.Cochain.smul_comp r γ _ (add_zero n) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro γ
    simp [dgHomZModuleCochainComplex,
      CochainComplex.HomComplex.δ_comp_ofHom]

/-- Postcomposition on the smart-truncated direct mapping chain complexes. -/
def dgMappingDirectZModulePostcomposition (K : ComplexCategory)
    {L M : ComplexCategory} (g : L ⟶ M) :
    dgMappingDirectZModuleChainComplex K L ⟶
      dgMappingDirectZModuleChainComplex K M :=
  HomologicalComplex.truncLE'Map (dgHomZModulePostcomposition K g)
    ComplexShape.embeddingDownNat

/-- Precomposition on the smart-truncated direct mapping chain complexes. -/
def dgMappingDirectZModulePrecomposition (M : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplex L M ⟶
      dgMappingDirectZModuleChainComplex K M :=
  HomologicalComplex.truncLE'Map (dgHomZModulePrecomposition M f)
    ComplexShape.embeddingDownNat

set_option maxHeartbeats 1000000 in
-- Normalizing the smart-truncation restriction through tensor composition needs extra budget.
/-- Chain composition with the tensor-unit representative of `g` is direct
postcomposition. -/
theorem dgMappingDirectZModuleChainMorphismMap_postcomposition
    (K : ComplexCategory) {L M : ComplexCategory} (g : L ⟶ M) :
    (λ_ (dgMappingDirectZModuleChainComplex K L)).inv ≫
        dgMappingDirectZModuleChainMorphismMap g ▷
          dgMappingDirectZModuleChainComplex K L ≫
        dgTruncatedCompositionReversed K L M =
      dgMappingDirectZModulePostcomposition K g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  have hnat := HomologicalComplex.congr_hom
    (HomologicalComplex.truncLE'ToRestriction_naturality
      (dgHomZModulePostcomposition K g) ComplexShape.embeddingDownNat) n
  simp only [HomologicalComplex.comp_f] at hnat
  simp only [HomologicalComplex.comp_f]
  dsimp only [dgMappingDirectZModulePostcomposition]
  rw [hnat]
  change ((((HomologicalComplex.leftUnitor'
      (dgMappingDirectZModuleChainComplex K L)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (dgMappingDirectZModuleChainMorphismMap g)
      (𝟙 (dgMappingDirectZModuleChainComplex K L))).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [dgTruncatedCompositionReversed]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (dgMappingDirectZModuleChainComplex L M)
      (dgMappingDirectZModuleChainComplex K L) 0 n n (zero_add n) ≫
        dgTruncatedCompositionDegreeReversed K L M n
    exact ιTensorObj_dgTruncatedCompositionDegreeReversed K L M (zero_add n)
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply, ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  rw [dgMappingDirectZModuleChainMorphismMap_f_zero]
  erw [dgTruncatedCompositionToCochain_tmul]
  change CochainComplex.HomComplex.Cochain.comp
      (ConcreteCategory.hom
        (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n) x)
      (ConcreteCategory.hom
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0)
        (ConcreteCategory.hom
          (dgMappingDirectZModuleMorphismDegreeZero g) (1 : ℤ)))
      (add_zero (ComplexShape.embeddingDownNat.f n)) =
      ConcreteCategory.hom
        ((HomologicalComplex.restrictionMap (dgHomZModulePostcomposition K g)
          ComplexShape.embeddingDownNat).f n)
        (ConcreteCategory.hom
          (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n) x)
  rw [dgMappingDirectZModuleMorphismDegreeZero_toRestriction_apply_one]
  rfl

set_option maxHeartbeats 1000000 in
-- Normalizing the smart-truncation restriction through tensor composition needs extra budget.
/-- Chain composition with the tensor-unit representative of `f` is direct
precomposition. -/
theorem dgMappingDirectZModuleChainMorphismMap_precomposition
    (M : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (ρ_ (dgMappingDirectZModuleChainComplex L M)).inv ≫
        dgMappingDirectZModuleChainComplex L M ◁
          dgMappingDirectZModuleChainMorphismMap f ≫
        dgTruncatedCompositionReversed K L M =
      dgMappingDirectZModulePrecomposition M f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  have hnat := HomologicalComplex.congr_hom
    (HomologicalComplex.truncLE'ToRestriction_naturality
      (dgHomZModulePrecomposition M f) ComplexShape.embeddingDownNat) n
  simp only [HomologicalComplex.comp_f] at hnat
  simp only [HomologicalComplex.comp_f]
  dsimp only [dgMappingDirectZModulePrecomposition]
  rw [hnat]
  change ((((HomologicalComplex.rightUnitor'
      (dgMappingDirectZModuleChainComplex L M)).inv n ≫ _) ≫ _) ≫ _) = _
  rw [HomologicalComplex.rightUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (𝟙 (dgMappingDirectZModuleChainComplex L M))
      (dgMappingDirectZModuleChainMorphismMap f)).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  dsimp only [dgTruncatedCompositionReversed]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (dgMappingDirectZModuleChainComplex L M)
      (dgMappingDirectZModuleChainComplex K L) n 0 n (add_zero n) ≫
        dgTruncatedCompositionDegreeReversed K L M n
    exact ιTensorObj_dgTruncatedCompositionDegreeReversed K L M (add_zero n)
  erw [dgTruncatedCompositionComponentReversed_toRestriction]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply, ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  rw [dgMappingDirectZModuleChainMorphismMap_f_zero]
  erw [dgTruncatedCompositionToCochain_tmul]
  change CochainComplex.HomComplex.Cochain.comp
      (ConcreteCategory.hom
        (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0)
        (ConcreteCategory.hom
          (dgMappingDirectZModuleMorphismDegreeZero f) (1 : ℤ)))
      (ConcreteCategory.hom
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n) x)
      (zero_add (ComplexShape.embeddingDownNat.f n)) =
      ConcreteCategory.hom
        ((HomologicalComplex.restrictionMap (dgHomZModulePrecomposition M f)
          ComplexShape.embeddingDownNat).f n)
        (ConcreteCategory.hom
          (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n) x)
  rw [dgMappingDirectZModuleMorphismDegreeZero_toRestriction_apply_one]
  rfl

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
