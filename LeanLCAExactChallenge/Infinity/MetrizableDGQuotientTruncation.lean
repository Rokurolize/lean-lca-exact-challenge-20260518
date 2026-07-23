/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGCategory

/-! # Smart truncation of the corrected quotient DG enrichment -/

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

abbrev QuotientDGChain :=
  ChainComplex (ModuleCat.{1} QuotientCoefficientRing) ℕ

/-- The nonpositive smart truncation of a corrected quotient Hom complex. -/
def quotientDGMappingChain (K L : ComplexCategory) : QuotientDGChain :=
  (quotientCoefficientCochainComplex K L).truncLE'
    ComplexShape.embeddingDownNat

private lemma boundaryLE_embeddingDownNat_iff (n : ℕ) :
    ComplexShape.embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
    ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 n

private lemma truncLE'ToRestriction_f_zero
    (H : QuotientDGCochain)
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
private lemma truncLEIsoCycles_inv_hom_of_proofs
    (H : QuotientDGCochain) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom = 𝟙 _ := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  exact Iso.inv_hom_id _

lemma quotientTruncLEToRestriction_f_zero
    (H : QuotientDGCochain)
    (hb : ComplexShape.embeddingDownNat.BoundaryLE 0) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 =
      (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
        H.iCycles 0 :=
  truncLE'ToRestriction_f_zero H hb

@[reassoc]
lemma quotientTruncLEIsoCycles_inv_hom_of_proofs
    (H : QuotientDGCochain) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom = 𝟙 _ :=
  truncLEIsoCycles_inv_hom_of_proofs H n i hi₁ hi₂ hn₁ hn₂

lemma quotientTruncLEToRestriction_f_zero_d
    (H : QuotientDGCochain) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 ≫ H.d 0 1 = 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff 0).2 rfl
  rw [truncLE'ToRestriction_f_zero H hb]
  simp only [Category.assoc, H.iCycles_d, comp_zero]

private lemma truncLE'ToRestriction_f_succ
    (H : QuotientDGCochain) (n : ℕ)
    (hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1)) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (n + 1) =
      (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).hom := by
  dsimp [HomologicalComplex.truncLE'ToRestriction]
  have hn' : ¬ ComplexShape.embeddingDownNat.op.BoundaryGE (n + 1) := by
    simpa using hn
  rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_iso_inv
    ComplexShape.embeddingDownNat.op rfl hn']
  dsimp [HomologicalComplex.restrictionXIso,
    HomologicalComplex.truncLE'XIso]
  simp

/-- Apply a cochain-level bilinear operation to two smart-truncated inputs. -/
def quotientTruncatedMapToCochain
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C)
    {p q n : ℕ} (h : p + q = n) :
    (A.truncLE' ComplexShape.embeddingDownNat).X p ⊗
        (B.truncLE' ComplexShape.embeddingDownNat).X q ⟶
      C.X (ComplexShape.embeddingDownNat.f n) :=
  (((A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p ⊗ₘ
      (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q) ≫
    HomologicalComplex.ιTensorObj A B
      (ComplexShape.embeddingDownNat.f p)
      (ComplexShape.embeddingDownNat.f q)
      (ComplexShape.embeddingDownNat.f n) (by
        dsimp [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE]
        omega)) ≫
    mu.f (ComplexShape.embeddingDownNat.f n)

/-- The boundary-degree output of a truncated cochain operation is a cocycle. -/
lemma quotientTruncatedMapToCochain_zero_d
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C) :
    quotientTruncatedMapToCochain (A := A) (B := B) (C := C) mu
        (p := 0) (q := 0) (n := 0) rfl ≫ C.d 0 1 = 0 := by
  let a0 : (A.truncLE' ComplexShape.embeddingDownNat).X 0 ⟶ A.X 0 :=
    (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0
  let b0 : (B.truncLE' ComplexShape.embeddingDownNat).X 0 ⟶ B.X 0 :=
    (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0
  change (((a0 ⊗ₘ b0) ≫
      HomologicalComplex.ιTensorObj A B 0 0 0 rfl) ≫ mu.f 0) ≫ C.d 0 1 = 0
  rw [Category.assoc, mu.comm]
  rw [← Category.assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂, Category.assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
    (show (0 : ℤ) + 1 = 1 by omega) 0 1
      (by change (1 : ℤ) + 0 = 1; omega)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0
    (show (0 : ℤ) + 1 = 1 by omega) 1
      (by change (0 : ℤ) + 1 = 1; omega)]
  have he₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((0 : ℤ), (0 : ℤ)) = 1 := rfl
  have he₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ((0 : ℤ), (0 : ℤ)) = 1 := rfl
  rw [he₁, he₂, one_smul, one_smul]
  have ha : a0 ≫ A.d 0 1 = 0 := by
    dsimp [a0]
    exact quotientTruncLEToRestriction_f_zero_d A
  have hb : b0 ≫ B.d 0 1 = 0 := by
    dsimp [b0]
    exact quotientTruncLEToRestriction_f_zero_d B
  simp only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
    curriedTensor_obj_map, curriedTensor_obj_obj, Category.assoc,
    Preadditive.add_comp]
  rw [MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, ha]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hb]
  simp

/-- The component of a truncated cochain operation in total chain degree `n`. -/
def quotientTruncatedMapComponent
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C)
    {p q n : ℕ} (h : p + q = n) :
    (A.truncLE' ComplexShape.embeddingDownNat).X p ⊗
        (B.truncLE' ComplexShape.embeddingDownNat).X q ⟶
      (C.truncLE' ComplexShape.embeddingDownNat).X n := by
  obtain rfl | n := n
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
      (boundaryLE_embeddingDownNat_iff 0).2 rfl
    exact C.liftCycles'
        (quotientTruncatedMapToCochain mu rfl) 1 (by simp)
        (quotientTruncatedMapToCochain_zero_d mu) ≫
      (C.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).inv
  · have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1) := fun hn =>
      Nat.succ_ne_zero n ((boundaryLE_embeddingDownNat_iff (n + 1)).1 hn)
    exact quotientTruncatedMapToCochain mu h ≫
      (C.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).inv

@[reassoc]
lemma quotientTruncatedMapComponent_toRestriction
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C)
    {p q n : ℕ} (h : p + q = n) :
    quotientTruncatedMapComponent mu h ≫
        (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f n =
      quotientTruncatedMapToCochain mu h := by
  obtain rfl | n := n
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
      (boundaryLE_embeddingDownNat_iff 0).2 rfl
    dsimp [quotientTruncatedMapComponent]
    rw [truncLE'ToRestriction_f_zero _ hb]
    simp only [Category.assoc]
    erw [truncLEIsoCycles_inv_hom_of_proofs_assoc C 0 0 rfl rfl hb hb]
    simp
  · have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1) := fun hn =>
      Nat.succ_ne_zero n ((boundaryLE_embeddingDownNat_iff (n + 1)).1 hn)
    rw [truncLE'ToRestriction_f_succ _ n hn]
    simp [quotientTruncatedMapComponent]

/-- The degreewise map induced by a cochain-level pairing after smart truncation. -/
def quotientTruncatedMapDegree
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C) (n : ℕ) :
    (HomologicalComplex.tensorObj
        (A.truncLE' ComplexShape.embeddingDownNat)
        (B.truncLE' ComplexShape.embeddingDownNat)).X n ⟶
      (C.truncLE' ComplexShape.embeddingDownNat).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h ↦
    quotientTruncatedMapComponent mu h

/-- The degreewise map viewed in the unrestricted target complex. -/
def quotientTruncatedMapToRestrictionDegree
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C) (n : ℕ) :
    (HomologicalComplex.tensorObj
        (A.truncLE' ComplexShape.embeddingDownNat)
        (B.truncLE' ComplexShape.embeddingDownNat)).X n ⟶
      (C.restriction ComplexShape.embeddingDownNat).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h ↦
    quotientTruncatedMapToCochain mu h

@[reassoc (attr := simp)]
lemma ιTensorObj_quotientTruncatedMapDegree
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C)
    {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj
          (A.truncLE' ComplexShape.embeddingDownNat)
          (B.truncLE' ComplexShape.embeddingDownNat) p q n h ≫
        quotientTruncatedMapDegree mu n =
      quotientTruncatedMapComponent mu h := by
  apply HomologicalComplex.ι_mapBifunctorDesc

@[reassoc]
lemma quotientTruncatedMapDegree_toRestriction
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C) (n : ℕ) :
    quotientTruncatedMapDegree mu n ≫
        (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f n =
      quotientTruncatedMapToRestrictionDegree mu n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hleft := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := A.truncLE' ComplexShape.embeddingDownNat)
    (K₂ := B.truncLE' ComplexShape.embeddingDownNat)
    (F := curriedTensor (ModuleCat.{1} QuotientCoefficientRing))
    (c := ComplexShape.down ℕ)
    (fun _ _ h ↦ quotientTruncatedMapComponent mu h) p q h
  have hright := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := A.truncLE' ComplexShape.embeddingDownNat)
    (K₂ := B.truncLE' ComplexShape.embeddingDownNat)
    (F := curriedTensor (ModuleCat.{1} QuotientCoefficientRing))
    (c := ComplexShape.down ℕ)
    (fun _ _ h ↦ quotientTruncatedMapToCochain mu h) p q h
  rw [← Category.assoc]
  dsimp [quotientTruncatedMapDegree, quotientTruncatedMapToRestrictionDegree]
  exact (congrArg (fun t ↦ t ≫
        (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f n) hleft).trans
    ((quotientTruncatedMapComponent_toRestriction mu h).trans hright.symm)

lemma quotientTruncatedMapToRestrictionDegree_comm
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C)
    {n m : ℕ} (hnm : (ComplexShape.down ℕ).Rel n m) :
    quotientTruncatedMapToRestrictionDegree mu n ≫
        (C.restriction ComplexShape.embeddingDownNat).d n m =
      (HomologicalComplex.tensorObj
        (A.truncLE' ComplexShape.embeddingDownNat)
        (B.truncLE' ComplexShape.embeddingDownNat)).d n m ≫
          quotientTruncatedMapToRestrictionDegree mu m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hraw := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := A.truncLE' ComplexShape.embeddingDownNat)
    (K₂ := B.truncLE' ComplexShape.embeddingDownNat)
    (F := curriedTensor (ModuleCat.{1} QuotientCoefficientRing))
    (c := ComplexShape.down ℕ)
    (fun _ _ h ↦ quotientTruncatedMapToCochain mu h) p q hpq
  rw [← Category.assoc]
  dsimp [quotientTruncatedMapToRestrictionDegree]
  refine (congrArg (fun t ↦ t ≫ C.d (-n) (-m)) hraw).trans ?_
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := A.truncLE' ComplexShape.embeddingDownNat)
    (K₂ := B.truncLE' ComplexShape.embeddingDownNat)
    (F := curriedTensor (ModuleCat.{1} QuotientCoefficientRing))
    (c := ComplexShape.down ℕ) n m p q hpq
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := A.truncLE' ComplexShape.embeddingDownNat)
    (K₂ := B.truncLE' ComplexShape.embeddingDownNat)
    (F := curriedTensor (ModuleCat.{1} QuotientCoefficientRing))
    (c := ComplexShape.down ℕ) n m p q hpq
  have hD₁assoc := congrArg (fun t ↦ t ≫
    HomologicalComplex.mapBifunctorDesc
      (fun _ _ h ↦ quotientTruncatedMapToCochain mu h)) hD₁
  have hD₂assoc := congrArg (fun t ↦ t ≫
    HomologicalComplex.mapBifunctorDesc
      (fun _ _ h ↦ quotientTruncatedMapToCochain mu h)) hD₂
  rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc,
    Preadditive.comp_add, Preadditive.add_comp]
  refine Eq.trans ?_ (congrArg₂ (fun a b ↦ a + b) hD₁assoc hD₂assoc).symm
  change p + q = n at hpq
  change m + 1 = n at hnm
  obtain rfl | p := p <;> obtain rfl | q := q
  · omega
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 (q + 1) m
      (by simp [ComplexShape.down])]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down]) m
      (by change 0 + q = m; omega)]
    simp only [zero_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    have heps : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, q + 1) = 1 := rfl
    simp only [heps, one_smul]
    refine Eq.trans ?_ (zero_add _).symm
    dsimp [quotientTruncatedMapToCochain]
    rw [Category.assoc, mu.comm]
    simp only [← Category.assoc]
    congr 1
    rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂, Category.assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 by simp [ComplexShape.up])
      (-((q : ℤ) + 1)) (-m : ℤ) (by
        change (1 : ℤ) + (-((q : ℤ) + 1)) = -(m : ℤ)
        omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (0 : ℤ)
      (show (ComplexShape.up ℤ).Rel (-((q : ℤ) + 1)) (-q : ℤ) by
        simp [ComplexShape.up]) (-m : ℤ) (by
          change (0 : ℤ) + (-(q : ℤ)) = -(m : ℤ)
          omega)]
    have he₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((0 : ℤ), (-((q : ℤ) + 1))) = 1 := rfl
    have he₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((0 : ℤ), (-((q : ℤ) + 1))) = 1 := rfl
    rw [he₁, he₂, one_smul, one_smul]
    simp only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
      curriedTensor_obj_map, curriedTensor_obj_obj, Category.assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc,
      quotientTruncLEToRestriction_f_zero_d A]
    simp only [MonoidalPreadditive.zero_whiskerRight, zero_comp, zero_add]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    have hB := (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm
      (q + 1) q
    change (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (q + 1) ≫
        B.d (-((q : ℤ) + 1)) (-(q : ℤ)) =
      (B.truncLE' ComplexShape.embeddingDownNat).d (q + 1) q ≫
        (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q at hB
    rw [hB]
    rw [MonoidalCategory.whisker_exchange_assoc]
    simp
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      0 m (by change p + 0 = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ (p + 1) 0 m
      (by simp [ComplexShape.down])]
    simp only [zero_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    have heps : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p + 1, 0) = 1 := rfl
    simp only [heps, one_smul]
    refine Eq.trans ?_ (add_zero _).symm
    dsimp [quotientTruncatedMapToCochain]
    rw [Category.assoc, mu.comm]
    simp only [← Category.assoc]
    congr 1
    rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂, Category.assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℤ).Rel (-((p : ℤ) + 1)) (-p : ℤ) by
        simp [ComplexShape.up]) (0 : ℤ) (-m : ℤ) (by
          change (-(p : ℤ)) + (0 : ℤ) = -(m : ℤ)
          omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _
      (-((p : ℤ) + 1))
      (show (ComplexShape.up ℤ).Rel (0 : ℤ) 1 by simp [ComplexShape.up])
      (-m : ℤ) (by
        change (-((p : ℤ) + 1)) + (1 : ℤ) = -(m : ℤ)
        omega)]
    have he₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((-((p : ℤ) + 1)), (0 : ℤ)) = 1 := rfl
    rw [he₁, one_smul]
    simp only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
      curriedTensor_obj_map, curriedTensor_obj_obj, Category.assoc]
    rw [MonoidalCategory.whisker_exchange_assoc]
    simp only [Linear.comp_units_smul]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      quotientTruncLEToRestriction_f_zero_d B]
    simp only [neg_add_rev, Int.reduceNeg, ComplexShape.ε₂_def,
      ComplexShape.ε_up_ℤ, MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      comp_zero, smul_zero, add_zero]
    rw [← MonoidalCategory.comp_whiskerRight_assoc]
    have hA := (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm
      (p + 1) p
    change (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (p + 1) ≫
        A.d (-((p : ℤ) + 1)) (-(p : ℤ)) =
      (A.truncLE' ComplexShape.embeddingDownNat).d (p + 1) p ≫
        (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p at hA
    rw [hA]
    rw [MonoidalCategory.comp_whiskerRight_assoc]
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      (q + 1) m (by change p + (q + 1) = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
      m (by change p + 1 + q = m; omega)]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [Units.smul_def, Units.smul_def]
    change _ = (1 : ℤ) • _ + ((-1 : ℤ) ^ (p + 1)) • _
    rw [one_smul]
    dsimp [quotientTruncatedMapToCochain]
    rw [Category.assoc, mu.comm]
    simp only [← Category.assoc]
    rw [← Preadditive.zsmul_comp, ← Preadditive.add_comp]
    congr 1
    rw [Category.assoc, HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂, Category.assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℤ).Rel (-((p : ℤ) + 1)) (-p : ℤ) by
        simp [ComplexShape.up]) (-((q : ℤ) + 1)) (-m : ℤ) (by
          change (-(p : ℤ)) + (-((q : ℤ) + 1)) = -(m : ℤ)
          omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _
      (-((p : ℤ) + 1))
      (show (ComplexShape.up ℤ).Rel (-((q : ℤ) + 1)) (-q : ℤ) by
        simp [ComplexShape.up]) (-m : ℤ) (by
          change (-((p : ℤ) + 1)) + (-(q : ℤ)) = -(m : ℤ)
          omega)]
    have he₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) ((-((p : ℤ) + 1)), (-((q : ℤ) + 1))) = 1 := rfl
    rw [he₁, one_smul]
    simp only [MonoidalCategory.tensorHom_def, curriedTensor_map_app,
      curriedTensor_obj_map, curriedTensor_obj_obj, Category.assoc,
      Linear.comp_units_smul]
    rw [Units.smul_def]
    change _ + ((-((p : ℤ) + 1)).negOnePow : ℤ) • _ =
      _ + ((-1 : ℤ) ^ (p + 1)) • _
    have hsign : ((-((p : ℤ) + 1)).negOnePow : ℤ) =
        (-1 : ℤ) ^ (p + 1) := by
      rw [Int.negOnePow_neg]
      exact Int.coe_negOnePow_natCast (p + 1)
    rw [hsign]
    refine congrArg₂ (fun f g ↦ f + g) ?_ ?_
    · rw [MonoidalCategory.whisker_exchange_assoc]
      rw [← MonoidalCategory.comp_whiskerRight_assoc]
      have hA := (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm
        (p + 1) p
      change (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (p + 1) ≫
          A.d (-((p : ℤ) + 1)) (-(p : ℤ)) =
        (A.truncLE' ComplexShape.embeddingDownNat).d (p + 1) p ≫
          (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p at hA
      rw [hA]
      rw [MonoidalCategory.comp_whiskerRight_assoc]
    · congr 1
      rw [← MonoidalCategory.whiskerLeft_comp_assoc]
      have hB := (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm
        (q + 1) q
      change (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (q + 1) ≫
          B.d (-((q : ℤ) + 1)) (-(q : ℤ)) =
        (B.truncLE' ComplexShape.embeddingDownNat).d (q + 1) q ≫
          (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q at hB
      rw [hB]
      simp only [MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc]


/-- A cochain-level bilinear map induces a chain map after nonpositive smart truncation. -/
def quotientTruncatedMap
    {A B C : QuotientDGCochain}
    (mu : HomologicalComplex.tensorObj A B ⟶ C) :
    HomologicalComplex.tensorObj
        (A.truncLE' ComplexShape.embeddingDownNat)
        (B.truncLE' ComplexShape.embeddingDownNat) ⟶
      C.truncLE' ComplexShape.embeddingDownNat where
  f n := quotientTruncatedMapDegree mu n
  comm' n m hnm := by
    apply (cancel_mono
      ((C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f m)).1
    calc
      (quotientTruncatedMapDegree mu n ≫
            (C.truncLE' ComplexShape.embeddingDownNat).d n m) ≫
          (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f m =
        quotientTruncatedMapDegree mu n ≫
          ((C.truncLE' ComplexShape.embeddingDownNat).d n m ≫
            (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f m) :=
          Category.assoc _ _ _
      _ = quotientTruncatedMapDegree mu n ≫
          ((C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f n ≫
            (C.restriction ComplexShape.embeddingDownNat).d n m) := by
        exact congrArg (fun t ↦ quotientTruncatedMapDegree mu n ≫ t)
          ((C.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm n m).symm
      _ = (quotientTruncatedMapDegree mu n ≫
            (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f n) ≫
          (C.restriction ComplexShape.embeddingDownNat).d n m :=
          (Category.assoc _ _ _).symm
      _ = quotientTruncatedMapToRestrictionDegree mu n ≫
          (C.restriction ComplexShape.embeddingDownNat).d n m := by
        rw [quotientTruncatedMapDegree_toRestriction]
      _ = (HomologicalComplex.tensorObj
            (A.truncLE' ComplexShape.embeddingDownNat)
            (B.truncLE' ComplexShape.embeddingDownNat)).d n m ≫
          quotientTruncatedMapToRestrictionDegree mu m :=
        quotientTruncatedMapToRestrictionDegree_comm mu hnm
      _ = (HomologicalComplex.tensorObj
            (A.truncLE' ComplexShape.embeddingDownNat)
            (B.truncLE' ComplexShape.embeddingDownNat)).d n m ≫
          (quotientTruncatedMapDegree mu m ≫
            (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f m) := by
        rw [quotientTruncatedMapDegree_toRestriction]
      _ = ((HomologicalComplex.tensorObj
              (A.truncLE' ComplexShape.embeddingDownNat)
              (B.truncLE' ComplexShape.embeddingDownNat)).d n m ≫
            quotientTruncatedMapDegree mu m) ≫
          (C.truncLE'ToRestriction ComplexShape.embeddingDownNat).f m :=
          (Category.assoc _ _ _).symm

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
