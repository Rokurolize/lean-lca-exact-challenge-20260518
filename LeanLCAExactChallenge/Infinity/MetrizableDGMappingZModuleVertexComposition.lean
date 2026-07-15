/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleVertexTensorator

/-!
# Degree-zero composition for integer-module dg mapping complexes

This file identifies degree-zero transported cochains with bounded-complex morphisms and
proves that the transported dg composition acts as ordinary composition on pure tensors.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

def dgMappingZModuleZeroCochain (K L : ComplexCategory)
    (x : (dgMappingZModuleChainComplex K L).X 0) :
    CochainComplex.HomComplex.Cochain
      (underlyingComplex K) (underlyingComplex L) 0 :=
  ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0
    ((dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 x)

def dgCocycleToCochain (K L : ComplexCategory) :
    AddCommGrpCat.of
        (CochainComplex.HomComplex.Cocycle
          (underlyingComplex K) (underlyingComplex L) 0) ⟶
      AddCommGrpCat.of
        (CochainComplex.HomComplex.Cochain
          (underlyingComplex K) (underlyingComplex L) 0) :=
  AddCommGrpCat.ofHom
    (CochainComplex.HomComplex.Cocycle.toCochainAddMonoidHom
      (underlyingComplex K) (underlyingComplex L) 0)

theorem dgCocycleIsoCycles_inv_comp_toCochain (K L : ComplexCategory) :
    (dgCocycleIsoCycles K L).inv ≫ dgCocycleToCochain K L =
      (CochainComplex.HomComplex
        (underlyingComplex K) (underlyingComplex L)).iCycles 0 := by
  have hcone :
      (dgCocycleIsoCycles K L).hom ≫
          (CochainComplex.HomComplex
            (underlyingComplex K) (underlyingComplex L)).iCycles 0 =
        dgCocycleToCochain K L := by
    simpa [dgCocycleIsoCycles, dgCocycleToCochain,
      HomologicalComplex.cycles, HomologicalComplex.iCycles] using
      CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
        (CochainComplex.HomComplex.Cocycle.isKernel
          (underlyingComplex K) (underlyingComplex L) 0 1 (by omega))
        (HomologicalComplex.cyclesIsKernel
          (CochainComplex.HomComplex (underlyingComplex K) (underlyingComplex L))
          0 1 (CochainComplex.next ℤ 0))
        CategoryTheory.Limits.WalkingParallelPair.zero
  apply (cancel_epi (dgCocycleIsoCycles K L).hom).1
  calc
    (dgCocycleIsoCycles K L).hom ≫
          ((dgCocycleIsoCycles K L).inv ≫ dgCocycleToCochain K L) =
        ((dgCocycleIsoCycles K L).hom ≫
          (dgCocycleIsoCycles K L).inv) ≫ dgCocycleToCochain K L :=
      (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ dgCocycleToCochain K L := congrArg
      (fun f => f ≫ dgCocycleToCochain K L) (Iso.hom_inv_id _)
    _ = dgCocycleToCochain K L := Category.id_comp _
    _ = _ := hcone.symm

theorem addCommGrp_truncLEToRestriction_f_zero
    (H : CochainComplex AddCommGrpCat ℤ)
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
  dsimp [HomologicalComplex.truncLE'XIsoCycles,
    HomologicalComplex.iCycles, HomologicalComplex.pOpcycles]
  rw [Category.assoc]
  congr 1
  dsimp only [HomologicalComplex.cycles]
  have hp : (H.opcyclesOpIso 0).hom.unop ≫
      ((H.op).pOpcycles 0).unop = H.iCycles 0 := by
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

theorem module_truncLEToRestriction_f_zero
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
  dsimp [HomologicalComplex.truncLE'XIsoCycles,
    HomologicalComplex.iCycles, HomologicalComplex.pOpcycles]
  rw [Category.assoc]
  congr 1
  dsimp only [HomologicalComplex.cycles]
  have hp : (H.opcyclesOpIso 0).hom.unop ≫
      ((H.op).pOpcycles 0).unop = H.iCycles 0 := by
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
theorem module_truncLECycles_cancel
    (H : CochainComplex (ModuleCat ℤ) ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom =
      𝟙 _ := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  exact Iso.inv_hom_id _

theorem mapTruncHomIso_toRestriction_zero (K L : ComplexCategory) :
    (mapTruncHomIso K L).hom.f 0 ≫
        (((addCommGrpToZModule.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj)).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f 0 =
      addCommGrpToZModule.map
        (((CochainComplex.HomComplex K.obj L.obj).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0) := by
  let H := CochainComplex.HomComplex K.obj L.obj
  let FH := (addCommGrpToZModule.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj H
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    constructor
    · simp
    · intro k hk
      dsimp [ComplexShape.embeddingDownNat] at hk
      omega
  change ((addCommGrpToZModule.mapIso
      (H.truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb)).hom ≫
      ((H.sc 0).mapCyclesIso addCommGrpToZModule).inv ≫
      (FH.truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv) ≫
      (FH.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 =
    addCommGrpToZModule.map
      ((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0)
  rw [module_truncLEToRestriction_f_zero FH hb]
  simp only [Category.assoc]
  erw [module_truncLECycles_cancel_assoc FH 0 0]
  have hcycles : ((H.sc 0).mapCyclesIso addCommGrpToZModule).inv ≫
        ((H.sc 0).map addCommGrpToZModule).iCycles =
      addCommGrpToZModule.map (H.sc 0).iCycles := by
    rw [← (H.sc 0).mapCyclesIso_hom_iCycles addCommGrpToZModule]
    exact Iso.inv_hom_id_assoc _ _
  have hcycles' : ((H.sc 0).mapCyclesIso addCommGrpToZModule).inv ≫
      FH.iCycles 0 = addCommGrpToZModule.map (H.iCycles 0) := hcycles
  erw [hcycles']
  rw [addCommGrp_truncLEToRestriction_f_zero H hb]
  exact (addCommGrpToZModule.map_comp _ _).symm

theorem dgMappingChainZeroIsoCocycle_comp_toCochain
    (K L : ComplexCategory) :
    (dgMappingChainComplexZeroIsoCocycle K L).hom ≫
        dgCocycleToCochain K L =
      ((CochainComplex.HomComplex
        (underlyingComplex K) (underlyingComplex L)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 := by
  let H := CochainComplex.HomComplex
    (underlyingComplex K) (underlyingComplex L)
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    constructor
    · simp
    · intro k hk
      dsimp [ComplexShape.embeddingDownNat] at hk
      omega
  change ((H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
      (dgCocycleIsoCycles K L).inv) ≫ dgCocycleToCochain K L = _
  let a := (H.truncLE'XIsoCycles
    ComplexShape.embeddingDownNat rfl hb).hom
  let b := (dgCocycleIsoCycles K L).inv
  let c := dgCocycleToCochain K L
  have h₁ : (a ≫ b) ≫ c = a ≫ (b ≫ c) := Category.assoc _ _ _
  have h₂ : a ≫ (b ≫ c) = a ≫ H.iCycles 0 := congrArg
    (fun f => a ≫ f) (dgCocycleIsoCycles_inv_comp_toCochain K L)
  have h₃ : a ≫ H.iCycles 0 =
      (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 :=
    (addCommGrp_truncLEToRestriction_f_zero H hb).symm
  exact h₁.trans (h₂.trans h₃)

theorem dgMappingZModuleZeroCochainMap_eq (K L : ComplexCategory) :
    (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 ≫
        ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      (transportedToCanonicalZModuleIso ((dgMappingChainComplex K L).X 0)).hom ≫
        canonicalZModuleFunctor.map
          ((dgMappingChainComplexZeroIsoCocycle K L).hom ≫
            dgCocycleToCochain K L) := by
  rw [dgMappingChainZeroIsoCocycle_comp_toCochain]
  let H := CochainComplex.HomComplex K.obj L.obj
  let FH := (addCommGrpToZModule.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj H
  let D := dgHomZModuleCochainComplex K L
  let e := ComplexShape.embeddingDownNat
  let r := (H.truncLE'ToRestriction e).f 0
  let t := (transportedHomIsoDirect K L).hom
  have htrunc :
      (HomologicalComplex.truncLE'Map t e).f 0 ≫
          (D.truncLE'ToRestriction e).f 0 =
        (FH.truncLE'ToRestriction e).f 0 ≫ t.f 0 := by
    have h := HomologicalComplex.congr_hom
      (HomologicalComplex.truncLE'ToRestriction_naturality t e) 0
    change
      (HomologicalComplex.truncLE'Map t e).f 0 ≫
          (D.truncLE'ToRestriction e).f 0 =
        (FH.truncLE'ToRestriction e).f 0 ≫ t.f (e.f 0)
    exact h
  have ht : t.f 0 =
      transportedToCanonicalZModuleNatIso.hom.app (H.X 0) := by
    dsimp [t, transportedHomIsoDirect, canonicalMappedHomIsoDirect]
    exact Category.comp_id _
  have hmap : (mapTruncHomIso K L).hom.f 0 ≫
      (FH.truncLE'ToRestriction e).f 0 =
        addCommGrpToZModule.map r := by
    exact mapTruncHomIso_toRestriction_zero K L
  have hmapTail :
      ((mapTruncHomIso K L).hom.f 0 ≫
          (FH.truncLE'ToRestriction e).f 0) ≫ t.f 0 =
        addCommGrpToZModule.map r ≫ t.f 0 :=
    congrArg (fun s => s ≫ t.f 0) hmap
  have hmapMiddle :
      (mapTruncHomIso K L).hom.f 0 ≫
          ((FH.truncLE'ToRestriction e).f 0 ≫ t.f 0) =
        addCommGrpToZModule.map r ≫ t.f 0 := by
    exact (Category.assoc _ _ _).symm.trans hmapTail
  have hnatural :
      addCommGrpToZModule.map r ≫
          transportedToCanonicalZModuleNatIso.hom.app (H.X 0) =
        transportedToCanonicalZModuleNatIso.hom.app
            ((dgMappingChainComplex K L).X 0) ≫
          canonicalZModuleFunctor.map r := by
    change
      addCommGrpToZModule.map r ≫
          transportedToCanonicalZModuleNatIso.hom.app
            ((HomologicalComplex.restriction H e).X 0) =
        transportedToCanonicalZModuleNatIso.hom.app
            ((H.truncLE' e).X 0) ≫
          canonicalZModuleFunctor.map r
    exact transportedToCanonicalZModuleNatIso.hom.naturality r
  change (((mapTruncHomIso K L).hom.f 0 ≫
      (HomologicalComplex.truncLE'Map t e).f 0) ≫
      (D.truncLE'ToRestriction e).f 0) =
    transportedToCanonicalZModuleNatIso.hom.app
        ((dgMappingChainComplex K L).X 0) ≫
      canonicalZModuleFunctor.map r
  have hstart : (((mapTruncHomIso K L).hom.f 0 ≫
        (HomologicalComplex.truncLE'Map t e).f 0) ≫
        (D.truncLE'ToRestriction e).f 0) =
      (mapTruncHomIso K L).hom.f 0 ≫
        ((HomologicalComplex.truncLE'Map t e).f 0 ≫
          (D.truncLE'ToRestriction e).f 0) := Category.assoc _ _ _
  have hstep : (mapTruncHomIso K L).hom.f 0 ≫
        ((HomologicalComplex.truncLE'Map t e).f 0 ≫
          (D.truncLE'ToRestriction e).f 0) =
      (mapTruncHomIso K L).hom.f 0 ≫
        ((FH.truncLE'ToRestriction e).f 0 ≫ t.f 0) :=
    congrArg (fun s => (mapTruncHomIso K L).hom.f 0 ≫ s) htrunc
  have hcanon : addCommGrpToZModule.map r ≫ t.f 0 =
      transportedToCanonicalZModuleNatIso.hom.app
          ((dgMappingChainComplex K L).X 0) ≫
        canonicalZModuleFunctor.map r := by
    exact (congrArg (fun s => addCommGrpToZModule.map r ≫ s) ht).trans
      hnatural
  exact hstart.trans (hstep.trans (hmapMiddle.trans hcanon))

theorem dgMappingZModuleChainComposition_zero_toCochain
    (K L M : ComplexCategory) :
    HomologicalComplex.ιTensorObj
          (dgMappingZModuleChainComplex L M)
          (dgMappingZModuleChainComplex K L) 0 0 0 rfl ≫
        (dgMappingZModuleChainComposition K L M).f 0 ≫
        (dgMappingZModuleChainComplexIsoDirect K M).hom.f 0 ≫
        ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      ((dgMappingZModuleChainComplexIsoDirect L M).hom.f 0 ⊗ₘ
          (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0) ≫
        dgTruncatedCompositionToCochain K L M rfl := by
  let iT := HomologicalComplex.ιTensorObj
    (dgMappingZModuleChainComplex L M)
    (dgMappingZModuleChainComplex K L) 0 0 0 rfl
  let iD := HomologicalComplex.ιTensorObj
    (dgMappingDirectZModuleChainComplex L M)
    (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl
  let fLM := (dgMappingZModuleChainComplexIsoDirect L M).hom.f 0
  let fKL := (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0
  let fKM := (dgMappingZModuleChainComplexIsoDirect K M).hom.f 0
  let rKM := ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f 0
  let t := (HomologicalComplex.tensorHom
    (dgMappingZModuleChainComplexIsoDirect L M).hom
    (dgMappingZModuleChainComplexIsoDirect K L).hom).f 0
  let c := (dgTruncatedCompositionReversed K L M).f 0
  have hι : iT ≫ t = (fLM ⊗ₘ fKL) ≫ iD := by
    exact GradedObject.Monoidal.ι_tensorHom
      (dgMappingZModuleChainComplexIsoDirect L M).hom.f
      (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 0 0 rfl
  have hdeg := ιTensorObj_dgTruncatedCompositionDegreeReversed
    (K := K) (L := L) (M := M) (p := 0) (q := 0) (n := 0) rfl
  have hcomponent :=
    dgTruncatedCompositionComponentReversed_toRestriction
      (K := K) (L := L) (M := M) (p := 0) (q := 0) (n := 0) rfl
  have htrunc : iD ≫ (c ≫ rKM) =
      dgTruncatedCompositionToCochain K L M rfl := by
    calc
      _ = (iD ≫ c) ≫ rKM := (Category.assoc _ _ _).symm
      _ = dgTruncatedCompositionComponentReversed K L M rfl ≫ rKM :=
        congrArg (fun s => s ≫ rKM) hdeg
      _ = _ := hcomponent
  have hOut := HomologicalComplex.congr_hom
    (dgMappingZModuleChainComplexIsoDirect K M).inv_hom_id 0
  have hOut' :
      (dgMappingZModuleChainComplexIsoDirect K M).inv.f 0 ≫ fKM = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f,
      HomologicalComplex.id_f] using hOut
  have hcancel :
      (dgMappingZModuleChainComplexIsoDirect K M).inv.f 0 ≫
          (fKM ≫ rKM) = rKM := by
    calc
      _ = ((dgMappingZModuleChainComplexIsoDirect K M).inv.f 0 ≫ fKM) ≫
          rKM := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ rKM := congrArg (fun s => s ≫ rKM) hOut'
      _ = _ := Category.id_comp _
  have htail :
      (dgMappingZModuleChainComposition K L M).f 0 ≫ (fKM ≫ rKM) =
        t ≫ (c ≫ rKM) := by
    simp only [dgMappingZModuleChainComposition,
      HomologicalComplex.comp_f]
    change t ≫ (c ≫
        ((dgMappingZModuleChainComplexIsoDirect K M).inv.f 0 ≫
          (fKM ≫ rKM))) = t ≫ (c ≫ rKM)
    exact congrArg (fun s => t ≫ (c ≫ s)) hcancel
  calc
    iT ≫ ((dgMappingZModuleChainComposition K L M).f 0 ≫ (fKM ≫ rKM)) =
        iT ≫ (t ≫ (c ≫ rKM)) := congrArg (fun s => iT ≫ s) htail
    _ = (iT ≫ t) ≫ (c ≫ rKM) := (Category.assoc _ _ _).symm
    _ = ((fLM ⊗ₘ fKL) ≫ iD) ≫ (c ≫ rKM) :=
      congrArg (fun s => s ≫ (c ≫ rKM)) hι
    _ = (fLM ⊗ₘ fKL) ≫ (iD ≫ (c ≫ rKM)) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun s => (fLM ⊗ₘ fKL) ≫ s) htrunc

theorem dgMappingZModuleZeroCochain_comp
    (K L M : ComplexCategory)
    (x : (dgMappingZModuleChainComplex K L).X 0)
    (y : (dgMappingZModuleChainComplex L M).X 0) :
    dgMappingZModuleZeroCochain K M
        ((dgMappingZModuleChainComposition K L M).f 0
          (HomologicalComplex.ιTensorObj
            (dgMappingZModuleChainComplex L M)
            (dgMappingZModuleChainComplex K L) 0 0 0 rfl (y ⊗ₜ[ℤ] x))) =
      (dgMappingZModuleZeroCochain K L x).comp
        (dgMappingZModuleZeroCochain L M y) rfl := by
  have h := ConcreteCategory.congr_hom
    (dgMappingZModuleChainComposition_zero_toCochain K L M) (y ⊗ₜ[ℤ] x)
  change
    ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0
      ((dgMappingZModuleChainComplexIsoDirect K M).hom.f 0
        ((dgMappingZModuleChainComposition K L M).f 0
          (HomologicalComplex.ιTensorObj
            (dgMappingZModuleChainComplex L M)
            (dgMappingZModuleChainComplex K L) 0 0 0 rfl (y ⊗ₜ[ℤ] x)))) =
      dgTruncatedCompositionToCochain K L M rfl
        ((dgMappingZModuleChainComplexIsoDirect L M).hom.f 0 y ⊗ₜ[ℤ]
          (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 x)
  simp only [CategoryTheory.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at h
  exact h

theorem dgMappingZModuleZeroCochain_f_eq_boundedHom
    (K L : ComplexCategory)
    (x : (dgMappingZModuleChainComplex K L).X 0) (i : ℤ) :
    (dgMappingZModuleZeroCochain K L x).v i i (add_zero i) =
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map
        (dgMappingZModuleChainComplexZeroEquivBoundedHom K L x)).f i := by
  have h := ConcreteCategory.congr_hom
    (dgMappingZModuleZeroCochainMap_eq K L) x
  simp only [CategoryTheory.comp_apply] at h
  let z := (zModuleAddCommGrpEquivalence.counitIso.app
    ((dgMappingChainComplex K L).X 0)).hom x
  let c := (dgMappingChainComplexZeroIsoCocycle K L).hom z
  have hpreimageApply :
      (transportedToCanonicalZModuleIso
        ((dgMappingChainComplex K L).X 0)).hom x = z := by
    let A := (dgMappingChainComplex K L).X 0
    let q : zModuleAddCommGrpEquivalence.functor.obj
          (zModuleAddCommGrpEquivalence.inverse.obj A) ⟶
        zModuleAddCommGrpEquivalence.functor.obj (ModuleCat.of ℤ A) :=
      zModuleAddCommGrpEquivalence.counitIso.hom.app A
    have hp := zModuleAddCommGrpEquivalence.functor.map_preimage q
    simpa [transportedToCanonicalZModuleIso, A, q, z] using
      ConcreteCategory.congr_hom hp x
  have hright :
      ((transportedToCanonicalZModuleIso
          ((dgMappingChainComplex K L).X 0)).hom ≫
        canonicalZModuleFunctor.map
          ((dgMappingChainComplexZeroIsoCocycle K L).hom ≫
            dgCocycleToCochain K L)) x =
        (c : CochainComplex.HomComplex.Cochain
          (underlyingComplex K) (underlyingComplex L) 0) := by
    rw [CategoryTheory.comp_apply, hpreimageApply]
    simp [canonicalZModuleFunctor, dgCocycleToCochain, z, c]
  have hcochain : dgMappingZModuleZeroCochain K L x =
      (c : CochainComplex.HomComplex.Cochain
        (underlyingComplex K) (underlyingComplex L) 0) := by
    have hleft : dgMappingZModuleZeroCochain K L x =
        ((transportedToCanonicalZModuleIso
            ((dgMappingChainComplex K L).X 0)).hom ≫
          canonicalZModuleFunctor.map
            ((dgMappingChainComplexZeroIsoCocycle K L).hom ≫
              dgCocycleToCochain K L)) x := by
      change
        ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f 0
          ((dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 x) =
            canonicalZModuleFunctor.map
              ((dgMappingChainComplexZeroIsoCocycle K L).hom ≫
                dgCocycleToCochain K L)
              ((transportedToCanonicalZModuleIso
                ((dgMappingChainComplex K L).X 0)).hom x)
      exact h
    exact hleft.trans hright
  have hpreimage :
      dgMappingZModuleChainComplexZeroEquivBoundedHom K L x =
        (boundedCochainComplex MetrizableLCA.{0}).fullyFaithfulι.preimage
          (CochainComplex.HomComplex.Cocycle.homOf c) := by
    simp only [dgMappingZModuleChainComplexZeroEquivBoundedHom,
      dgMappingChainComplexZeroEquivBoundedHom,
      dgMappingChainComplexZeroEquivHom]
    rfl
  have hbounded :
      (boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingZModuleChainComplexZeroEquivBoundedHom K L x) =
        CochainComplex.HomComplex.Cocycle.homOf c := by
    rw [hpreimage]
    exact (boundedCochainComplex MetrizableLCA.{0}).fullyFaithfulι.map_preimage _
  calc
    _ = c.val.v i i (add_zero i) :=
      CochainComplex.HomComplex.Cochain.congr_v hcochain i i (add_zero i)
    _ = (CochainComplex.HomComplex.Cocycle.homOf c).f i := rfl
    _ = _ := congrArg (fun f => f.f i) hbounded.symm

theorem dgMappingZModuleChainComposition_zero_tmul
    (K L M : ComplexCategory)
    (x : (dgMappingZModuleChainComplex K L).X 0)
    (y : (dgMappingZModuleChainComplex L M).X 0) :
    dgMappingZModuleChainComplexZeroEquivBoundedHom K M
        ((dgMappingZModuleChainComposition K L M).f 0
          (HomologicalComplex.ιTensorObj
            (dgMappingZModuleChainComplex L M)
            (dgMappingZModuleChainComplex K L) 0 0 0 rfl (y ⊗ₜ[ℤ] x))) =
      dgMappingZModuleChainComplexZeroEquivBoundedHom K L x ≫
        dgMappingZModuleChainComplexZeroEquivBoundedHom L M y := by
  let w := (dgMappingZModuleChainComposition K L M).f 0
    (HomologicalComplex.ιTensorObj
      (dgMappingZModuleChainComplex L M)
      (dgMappingZModuleChainComplex K L) 0 0 0 rfl (y ⊗ₜ[ℤ] x))
  change dgMappingZModuleChainComplexZeroEquivBoundedHom K M w = _
  apply (boundedCochainComplex MetrizableLCA.{0}).fullyFaithfulι.map_injective
  rw [Functor.map_comp]
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f]
  rw [← dgMappingZModuleZeroCochain_f_eq_boundedHom K M w i]
  rw [← dgMappingZModuleZeroCochain_f_eq_boundedHom K L x i]
  rw [← dgMappingZModuleZeroCochain_f_eq_boundedHom L M y i]
  have h := dgMappingZModuleZeroCochain_comp K L M x y
  have hv := CochainComplex.HomComplex.Cochain.congr_v h i i (add_zero i)
  have hcomp :
      ((dgMappingZModuleZeroCochain K L x).comp
          (dgMappingZModuleZeroCochain L M y) rfl).v i i (add_zero i) =
        (dgMappingZModuleZeroCochain K L x).v i i (add_zero i) ≫
          (dgMappingZModuleZeroCochain L M y).v i i (add_zero i) := by
    exact CochainComplex.HomComplex.Cochain.zero_cochain_comp_v
      (dgMappingZModuleZeroCochain K L x)
      (dgMappingZModuleZeroCochain L M y) i i (add_zero i)
  simpa only [w] using hv.trans hcomp

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
