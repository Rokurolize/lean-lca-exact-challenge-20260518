/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedExtension
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainEnrichedCategory
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientSimplicialCategory
import LeanLCAExactChallenge.Infinity.EnrichedFunctorTransport
import LeanLCAExactChallenge.Infinity.EnrichedNaturalTransformationHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Enriched shifts of bounded DG complexes

The simultaneous shift of source and target cochain complexes is a map of DG Hom complexes
after multiplication in degree `n` by `(-1)^(a * n)`.  This file constructs that signed map
before coefficient change.  It is the chain-level input for enriched shift and unshift
functors on the corrected Drinfeld quotient.
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

/-- A bounded complex shifted using the concrete cochain shift.  Unlike the abstract shift on
the full subcategory, its underlying cochain complex is definitionally the shifted complex. -/
abbrev dgEnrichedShiftObject (K : ComplexCategory) (a : ℤ) : ComplexCategory :=
  ⟨K.obj⟦a⟧, (boundedCochainComplex MetrizableLCA.{0}).le_shift a K.obj K.property⟩

@[simp]
theorem dgEnrichedShiftObject_obj (K : ComplexCategory) (a : ℤ) :
    (dgEnrichedShiftObject K a).obj = K.obj⟦a⟧ :=
  rfl

/-- The signed simultaneous shift on homogeneous cochains.  The sign is forced by
`Cochain.δ_shift`: shifting both endpoints multiplies the Hom differential by `(-1)^a`. -/
def dgEnrichedShiftCochainLinearMap (K L : ComplexCategory) (a n : ℤ) :
    CochainComplex.HomComplex.Cochain K.obj L.obj n →ₗ[ℤ]
      CochainComplex.HomComplex.Cochain
        (dgEnrichedShiftObject K a).obj (dgEnrichedShiftObject L a).obj n where
  toFun γ := (a * n).negOnePow • γ.shift a
  map_add' γ δ := by
    simp only [CochainComplex.HomComplex.Cochain.shift_add, smul_add]
  map_smul' r γ := by
    simp only [CochainComplex.HomComplex.Cochain.shift_smul]
    exact smul_comm _ _ _

@[simp]
theorem dgEnrichedShiftCochainLinearMap_apply
    (K L : ComplexCategory) (a n : ℤ)
    (γ : CochainComplex.HomComplex.Cochain K.obj L.obj n) :
    dgEnrichedShiftCochainLinearMap K L a n γ =
      (a * n).negOnePow • γ.shift a :=
  rfl

/-- The signed simultaneous shift is a morphism of untruncated DG Hom complexes. -/
def dgEnrichedShiftCochainMap (K L : ComplexCategory) (a : ℤ) :
    dgHomZModuleCochainComplex K L ⟶
      dgHomZModuleCochainComplex
        (dgEnrichedShiftObject K a) (dgEnrichedShiftObject L a) where
  f n := ModuleCat.ofHom (dgEnrichedShiftCochainLinearMap K L a n)
  comm' n m hnm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro γ
    change CochainComplex.HomComplex.δ n m
        ((a * n).negOnePow • γ.shift a) =
      (a * m).negOnePow •
        (CochainComplex.HomComplex.δ n m γ).shift a
    rw [CochainComplex.HomComplex.δ_units_smul,
      CochainComplex.HomComplex.Cochain.δ_shift]
    rw [smul_smul, ← Int.negOnePow_add]
    congr 2
    simp only [ComplexShape.up_Rel] at hnm
    rw [← hnm]
    ring

@[simp]
theorem dgEnrichedShiftCochainMap_f_apply
    (K L : ComplexCategory) (a n : ℤ)
    (γ : (dgHomZModuleCochainComplex K L).X n) :
    (dgEnrichedShiftCochainMap K L a).f n γ =
      (a * n).negOnePow • γ.shift a :=
  rfl

/-- Simultaneous enriched shift preserves the identity cochain. -/
theorem dgEnrichedShiftCochainLinearMap_identity
    (K : ComplexCategory) (a : ℤ) :
    dgEnrichedShiftCochainLinearMap K K a 0
        (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj)) =
      CochainComplex.HomComplex.Cochain.ofHom
        (𝟙 (dgEnrichedShiftObject K a).obj) := by
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro i
  change (((a * 0).negOnePow •
    (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj)).shift a).v
      i i (add_zero i)) = _
  simp only [mul_zero, Int.negOnePow_zero, one_smul,
    CochainComplex.HomComplex.Cochain.shift_v',
    CochainComplex.HomComplex.Cochain.ofHom_v, CochainComplex.shiftFunctor_obj_X',
    HomologicalComplex.id_f]

/-- Simultaneous shift commutes with composition of homogeneous cochains. -/
theorem dgEnrichedShiftCochain_shift_comp
    (K L M : ComplexCategory) (a : ℤ) {p q r : ℤ} (h : q + p = r)
    (x : CochainComplex.HomComplex.Cochain K.obj L.obj q)
    (y : CochainComplex.HomComplex.Cochain L.obj M.obj p) :
    (x.shift a).comp (y.shift a) h = (x.comp y h).shift a := by
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  rw [CochainComplex.HomComplex.Cochain.comp_v _ _ h
      i (i + q) j rfl (by omega),
    CochainComplex.HomComplex.Cochain.shift_v x a
      i (i + q) rfl (i + a) (i + q + a) rfl rfl,
    CochainComplex.HomComplex.Cochain.shift_v y a
      (i + q) j (by omega) (i + q + a) (j + a) rfl rfl,
    CochainComplex.HomComplex.Cochain.shift_v (x.comp y h) a
      i j hij (i + a) (j + a) rfl rfl,
    CochainComplex.HomComplex.Cochain.comp_v _ _ h
      (i + a) (i + q + a) (j + a) (by omega) (by omega)]
  simp only [Category.assoc, CategoryTheory.Iso.inv_hom_id_assoc]

/-- Simultaneous enriched shift preserves homogeneous composition, including the degree
signs required to make it a DG map. -/
theorem dgEnrichedShiftCochainLinearMap_comp
    (K L M : ComplexCategory) (a : ℤ) {p q r : ℤ} (h : q + p = r)
    (x : CochainComplex.HomComplex.Cochain K.obj L.obj q)
    (y : CochainComplex.HomComplex.Cochain L.obj M.obj p) :
    (dgEnrichedShiftCochainLinearMap K L a q x).comp
        (dgEnrichedShiftCochainLinearMap L M a p y) h =
      dgEnrichedShiftCochainLinearMap K M a r (x.comp y h) := by
  change (((a * q).negOnePow • x.shift a).comp
      ((a * p).negOnePow • y.shift a) h) =
    (a * r).negOnePow • (x.comp y h).shift a
  rw [CochainComplex.HomComplex.Cochain.units_smul_comp,
    CochainComplex.HomComplex.Cochain.comp_units_smul,
    dgEnrichedShiftCochain_shift_comp, smul_smul]
  congr 1
  rw [← Int.negOnePow_add]
  congr 1
  rw [← h]
  ring

namespace DrinfeldWord

open QuotientDoldKanMonoidal

/-- Coefficient change of the signed simultaneous shift on DG Hom complexes. -/
def originalCoefficientDGShiftMap (K L : ComplexCategory) (a : ℤ) :
    OriginalCoefficientCochainComplex K L ⟶
      OriginalCoefficientCochainComplex
        (dgEnrichedShiftObject K a) (dgEnrichedShiftObject L a) :=
  (quotientCoefficientChange.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((ModuleCat.uliftFunctor.{1} ℤ).mapHomologicalComplex
      (ComplexShape.up ℤ) |>.map (dgEnrichedShiftCochainMap K L a))

@[simp]
theorem originalCoefficientDGShiftMap_f_apply
    (K L : ComplexCategory) (a n : ℤ)
    (γ : (dgHomZModuleCochainComplex K L).X n) :
    (originalCoefficientDGShiftMap K L a).f n
        (ULift.up (ULift.up γ)) =
      ULift.up (ULift.up
        (dgEnrichedShiftCochainLinearMap K L a n γ)) :=
  rfl

/-- The coefficient-changed simultaneous shift preserves the enriched identity. -/
theorem originalCoefficientDGShiftMap_identity
    (K : ComplexCategory) (a : ℤ) :
    OriginalCoefficientDGIdentity K ≫
        originalCoefficientDGShiftMap K K a =
      OriginalCoefficientDGIdentity (dgEnrichedShiftObject K a) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  rw [OriginalCoefficientDGIdentity_f_zero,
    OriginalCoefficientDGIdentity_f_zero]
  simp only [Category.assoc]
  rw [cancel_epi]
  apply ModuleCat.hom_ext
  change (ConcreteCategory.hom
      ((originalCoefficientDGShiftMap K K a).f 0)).comp
      (LinearMap.toSpanSingleton QuotientCoefficientRing _
        (ULift.up (ULift.up (identityCochain K)))) =
    LinearMap.toSpanSingleton QuotientCoefficientRing _
      (ULift.up (ULift.up
        (identityCochain (dgEnrichedShiftObject K a))))
  rw [LinearMap.comp_toSpanSingleton]
  congr 1
  change ULift.up (ULift.up
      (dgEnrichedShiftCochainLinearMap K K a 0 (identityCochain K))) =
    ULift.up (ULift.up (identityCochain (dgEnrichedShiftObject K a)))
  exact congrArg (fun γ ↦ ULift.up (ULift.up γ))
    (dgEnrichedShiftCochainLinearMap_identity K a)

/-- One homogeneous component of original composition commutes with simultaneous shift. -/
theorem originalDGCompositionComponent_shift
    (K L M : ComplexCategory) (a : ℤ) {p q n : ℤ} (h : p + q = n) :
    originalDGCompositionComponent K L M h ≫
        (originalCoefficientDGShiftMap K M a).f n =
      ((originalCoefficientDGShiftMap L M a).f p ⊗ₘ
          (originalCoefficientDGShiftMap K L a).f q) ≫
        originalDGCompositionComponent
          (dgEnrichedShiftObject K a)
          (dgEnrichedShiftObject L a)
          (dgEnrichedShiftObject M a) h := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext y x
  rcases y with ⟨y⟩
  rcases y with ⟨y⟩
  rcases x with ⟨x⟩
  rcases x with ⟨x⟩
  change CochainComplex.HomComplex.Cochain
    (underlyingComplex L) (underlyingComplex M) p at y
  change CochainComplex.HomComplex.Cochain
    (underlyingComplex K) (underlyingComplex L) q at x
  change (originalDGCompositionComponent K L M h ≫
      (originalCoefficientDGShiftMap K M a).f n).hom
        (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
          ULift.up (ULift.up x)) =
    ((((originalCoefficientDGShiftMap L M a).f p ⊗ₘ
        (originalCoefficientDGShiftMap K L a).f q) ≫
      originalDGCompositionComponent
        (dgEnrichedShiftObject K a)
        (dgEnrichedShiftObject L a)
        (dgEnrichedShiftObject M a) h).hom
          (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
            ULift.up (ULift.up x)))
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  change ULift.up (ULift.up
      (dgEnrichedShiftCochainLinearMap K M a n
        ((dgCochainCompTensorReversed K L M h).hom (y ⊗ₜ[ℤ] x)))) =
    ULift.up (ULift.up
      ((dgCochainCompTensorReversed
        (dgEnrichedShiftObject K a)
        (dgEnrichedShiftObject L a)
        (dgEnrichedShiftObject M a) h).hom
        (dgEnrichedShiftCochainLinearMap L M a p y ⊗ₜ[ℤ]
          dgEnrichedShiftCochainLinearMap K L a q x)))
  apply ULift.down_injective
  apply ULift.down_injective
  change dgEnrichedShiftCochainLinearMap K M a n
      ((dgCochainCompTensorReversed K L M h).hom (y ⊗ₜ[ℤ] x)) =
    (dgCochainCompTensorReversed
      (dgEnrichedShiftObject K a)
      (dgEnrichedShiftObject L a)
      (dgEnrichedShiftObject M a) h).hom
      (dgEnrichedShiftCochainLinearMap L M a p y ⊗ₜ[ℤ]
        dgEnrichedShiftCochainLinearMap K L a q x)
  rw [dgCochainCompTensorReversed_tmul,
    dgCochainCompTensorReversed_tmul]
  exact (dgEnrichedShiftCochainLinearMap_comp K L M a
    (p := p) (q := q) (r := n) (by omega) x y).symm

/-- The coefficient-changed simultaneous shift preserves enriched composition. -/
theorem originalCoefficientDGShiftMap_comp
    (K L M : ComplexCategory) (a : ℤ) :
    OriginalCoefficientDGComposition K L M ≫
        originalCoefficientDGShiftMap K M a =
      (originalCoefficientDGShiftMap L M a ⊗ₘ
          originalCoefficientDGShiftMap K L a) ≫
        OriginalCoefficientDGComposition
          (dgEnrichedShiftObject K a)
          (dgEnrichedShiftObject L a)
          (dgEnrichedShiftObject M a) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  simp only [HomologicalComplex.comp_f]
  change HomologicalComplex.ιTensorObj
      (OriginalMappingCochain L M) (OriginalMappingCochain K L)
        p q n hpq ≫
      (OriginalCoefficientDGComposition K L M).f n ≫
        (originalCoefficientDGShiftMap K M a).f n =
    HomologicalComplex.ιTensorObj
      (OriginalMappingCochain L M) (OriginalMappingCochain K L)
        p q n hpq ≫
      (HomologicalComplex.tensorHom
        (originalCoefficientDGShiftMap L M a)
        (originalCoefficientDGShiftMap K L a)).f n ≫
      (OriginalCoefficientDGComposition
        (dgEnrichedShiftObject K a)
        (dgEnrichedShiftObject L a)
        (dgEnrichedShiftObject M a)).f n
  have hleft₀ := ιTensorObj_originalDGComposition K L M hpq
  have hleft := congrArg
    (fun f ↦ f ≫ (originalCoefficientDGShiftMap K M a).f n) hleft₀
  simp only [Category.assoc] at hleft
  rw [hleft, originalDGCompositionComponent_shift K L M a hpq]
  have hright₀ := GradedObject.Monoidal.ι_tensorHom
    (originalCoefficientDGShiftMap L M a).f
    (originalCoefficientDGShiftMap K L a).f p q n hpq
  have hright := congrArg
    (fun f ↦ f ≫
      (OriginalCoefficientDGComposition
        (dgEnrichedShiftObject K a)
        (dgEnrichedShiftObject L a)
        (dgEnrichedShiftObject M a)).f n) hright₀
  simp only [Category.assoc] at hright
  rw [← ιTensorObj_originalDGComposition
    (dgEnrichedShiftObject K a)
    (dgEnrichedShiftObject L a)
    (dgEnrichedShiftObject M a) hpq]
  exact hright.symm

/-- Simultaneous cochain shift as a genuine enriched endofunctor of the
coefficient-changed original DG category. -/
noncomputable def originalCoefficientDGEnrichedShift (a : ℤ) :
    EnrichedFunctor QuotientDGCochain
      OriginalCoefficientDGCategory OriginalCoefficientDGCategory where
  obj K := Opposite.op (dgEnrichedShiftObject K.unop a)
  map K L := originalCoefficientDGShiftMap L.unop K.unop a
  map_id K := originalCoefficientDGShiftMap_identity K.unop a
  map_comp K L M :=
    originalCoefficientDGShiftMap_comp M.unop L.unop K.unop a

@[simp]
theorem originalCoefficientDGEnrichedShift_obj
    (a : ℤ) (K : OriginalCoefficientDGCategory) :
    (originalCoefficientDGEnrichedShift a).obj K =
      Opposite.op (dgEnrichedShiftObject K.unop a) :=
  rfl

@[simp]
theorem originalCoefficientDGEnrichedShift_map
    (a : ℤ) (K L : OriginalCoefficientDGCategory) :
    (originalCoefficientDGEnrichedShift a).map K L =
      originalCoefficientDGShiftMap L.unop K.unop a :=
  rfl

/-- Corrected acyclic complexes remain corrected acyclic after cochain shift. -/
def correctedAcyclicEnrichedShift
    (A : CorrectedAcyclicComplexCategory) (a : ℤ) :
    CorrectedAcyclicComplexCategory :=
  ⟨dgEnrichedShiftObject A.obj a,
    exactAcyclicWithCycles_shift MetrizableLCA.{0} A.obj.obj a A.property⟩

@[simp]
theorem correctedAcyclicEnrichedShift_obj
    (A : CorrectedAcyclicComplexCategory) (a : ℤ) :
    (correctedAcyclicEnrichedShift A a).obj =
      dgEnrichedShiftObject A.obj a :=
  rfl

/-- The original enriched shift, followed by zero-word inclusion, annihilates every corrected
acyclic object using the formal contraction of its shifted complex. -/
noncomputable def correctedQuotientDGShiftAnnihilatingData (a : ℤ) :
    AnnihilatingEnrichedFunctorData CorrectedQuotientDGCategory where
  functor := EnrichedFunctor.comp QuotientDGCochain
    (originalCoefficientDGEnrichedShift a) originalToCorrectedQuotientDG
  contraction A :=
    ULift.up (quotientContractingElement (correctedAcyclicEnrichedShift A a))
  contraction_d A := by
    let G := EnrichedFunctor.id QuotientDGCochain CorrectedQuotientDGCategory
    let E := AnnihilatingEnrichedFunctorData.restriction G
    exact E.contraction_d (correctedAcyclicEnrichedShift A a)

/-- Genuine enriched simultaneous shift on the corrected Drinfeld quotient, obtained from
the quotient's enriched universal property. -/
noncomputable def correctedQuotientDGEnrichedShift (a : ℤ) :
    EnrichedFunctor QuotientDGCochain
      CorrectedQuotientDGCategory CorrectedQuotientDGCategory :=
  (correctedQuotientDGShiftAnnihilatingData a).enrichedExtension

@[simp]
theorem correctedQuotientDGEnrichedShift_obj
    (a : ℤ) (K : CorrectedQuotientDGCategory) :
    (correctedQuotientDGEnrichedShift a).obj K =
      Opposite.op (dgEnrichedShiftObject K.unop a) :=
  rfl

/-- Smart truncation of the enriched quotient shift on one Hom complex. -/
def correctedQuotientDGChainShiftMap
    (a : ℤ) (K L : CorrectedQuotientDGCategory) :
    quotientDGChainEnrichedHom K L ⟶
      quotientDGChainEnrichedHom
        ((correctedQuotientDGEnrichedShift a).obj K)
        ((correctedQuotientDGEnrichedShift a).obj L) :=
  HomologicalComplex.truncLE'Map
    ((correctedQuotientDGEnrichedShift a).map K L)
    ComplexShape.embeddingDownNat

lemma correctedQuotientDGChainShiftMap_toRestriction
    (a : ℤ) (K L : CorrectedQuotientDGCategory) (n : ℕ) :
    (correctedQuotientDGChainShiftMap a K L).f n ≫
        ((quotientDGEnrichedHom
          ((correctedQuotientDGEnrichedShift a).obj K)
          ((correctedQuotientDGEnrichedShift a).obj L)).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n =
      ((quotientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n ≫
        (HomologicalComplex.restrictionMap
          ((correctedQuotientDGEnrichedShift a).map K L)
          ComplexShape.embeddingDownNat).f n := by
  have hnat := congrArg (fun t ↦ t.f n)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      ((correctedQuotientDGEnrichedShift a).map K L)
      ComplexShape.embeddingDownNat)
  simp only [HomologicalComplex.comp_f] at hnat
  change (HomologicalComplex.truncLE'Map
        ((correctedQuotientDGEnrichedShift a).map K L)
        ComplexShape.embeddingDownNat).f n ≫
      ((quotientDGEnrichedHom
        ((correctedQuotientDGEnrichedShift a).obj K)
        ((correctedQuotientDGEnrichedShift a).obj L)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
    ((quotientDGEnrichedHom K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n ≫
      (HomologicalComplex.restrictionMap
        ((correctedQuotientDGEnrichedShift a).map K L)
        ComplexShape.embeddingDownNat).f n
  exact hnat

@[simp]
lemma correctedQuotientDGEnrichedShift_restrictionMap_f
    (a : ℤ) (K L : CorrectedQuotientDGCategory) (n : ℕ) :
    (HomologicalComplex.restrictionMap
      ((correctedQuotientDGEnrichedShift a).map K L)
      ComplexShape.embeddingDownNat).f n =
        ((correctedQuotientDGEnrichedShift a).map K L).f (-(n : ℤ)) :=
  rfl

lemma correctedQuotientDGChainShiftMap_tensor_toRestriction
    (a : ℤ) (K L M : CorrectedQuotientDGCategory) (p q : ℕ) :
    ((correctedQuotientDGChainShiftMap a K L).f p ⊗ₘ
        (correctedQuotientDGChainShiftMap a L M).f q) ≫
      (((quotientDGEnrichedHom
          ((correctedQuotientDGEnrichedShift a).obj K)
          ((correctedQuotientDGEnrichedShift a).obj L)).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((quotientDGEnrichedHom
          ((correctedQuotientDGEnrichedShift a).obj L)
          ((correctedQuotientDGEnrichedShift a).obj M)).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f q) =
    (((quotientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
      ((quotientDGEnrichedHom L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) ≫
        (((correctedQuotientDGEnrichedShift a).map K L).f (-(p : ℤ)) ⊗ₘ
          ((correctedQuotientDGEnrichedShift a).map L M).f (-(q : ℤ))) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    correctedQuotientDGChainShiftMap_toRestriction,
    correctedQuotientDGChainShiftMap_toRestriction,
    correctedQuotientDGEnrichedShift_restrictionMap_f,
    correctedQuotientDGEnrichedShift_restrictionMap_f]
  exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-- Smart truncation of enriched shift preserves the quotient chain identity. -/
theorem correctedQuotientDGChainShiftMap_identity
    (a : ℤ) (K : CorrectedQuotientDGCategory) :
    quotientDGChainEnrichedId K ≫
        correctedQuotientDGChainShiftMap a K K =
      quotientDGChainEnrichedId
        ((correctedQuotientDGEnrichedShift a).obj K) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  rw [quotientDGChainEnrichedId_f_zero,
    quotientDGChainEnrichedId_f_zero]
  apply (cancel_mono
    (((quotientDGEnrichedHom
      ((correctedQuotientDGEnrichedShift a).obj K)
      ((correctedQuotientDGEnrichedShift a).obj K)).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0)).1
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [correctedQuotientDGChainShiftMap_toRestriction]
  slice_lhs 1 2 =>
    rw [quotientDGChainIdentityDegreeZero_toRestriction]
  rw [quotientDGChainIdentityDegreeZero_toRestriction]
  have hid := (correctedQuotientDGEnrichedShift a).map_id K
  change quotientDGIdentity K.unop ≫
      (correctedQuotientDGEnrichedShift a).map K K =
    quotientDGIdentity
      ((correctedQuotientDGEnrichedShift a).obj K).unop at hid
  have hid0 := congrArg (fun f ↦ f.f 0) hid
  simp only [HomologicalComplex.comp_f] at hid0
  rw [quotientDGIdentity_f_zero, quotientDGIdentity_f_zero] at hid0
  change quotientIdentitySpan K.unop ≫
      ((correctedQuotientDGEnrichedShift a).map K K).f 0 =
    quotientIdentitySpan
      ((correctedQuotientDGEnrichedShift a).obj K).unop
  exact hid0

/-- Homogeneous quotient composition commutes with the enriched shift map. -/
theorem correctedQuotientDGEnrichedShift_component
    (a : ℤ) (K L M : CorrectedQuotientDGCategory)
    {p q n : ℤ} (h : p + q = n) :
    quotientDGCompositionComponent M.unop L.unop K.unop h ≫
        ((correctedQuotientDGEnrichedShift a).map K M).f n =
      (((correctedQuotientDGEnrichedShift a).map K L).f p ⊗ₘ
          ((correctedQuotientDGEnrichedShift a).map L M).f q) ≫
        quotientDGCompositionComponent
          ((correctedQuotientDGEnrichedShift a).obj M).unop
          ((correctedQuotientDGEnrichedShift a).obj L).unop
          ((correctedQuotientDGEnrichedShift a).obj K).unop h := by
  change ComplexCategoryᵒᵖ at K L M
  have hcomp := (correctedQuotientDGEnrichedShift a).map_comp K L M
  change quotientDGEnrichedComp K L M ≫
      (correctedQuotientDGEnrichedShift a).map K M =
    ((correctedQuotientDGEnrichedShift a).map K L ⊗ₘ
      (correctedQuotientDGEnrichedShift a).map L M) ≫
        quotientDGEnrichedComp
          ((correctedQuotientDGEnrichedShift a).obj K)
          ((correctedQuotientDGEnrichedShift a).obj L)
          ((correctedQuotientDGEnrichedShift a).obj M) at hcomp
  have hcompn := congrArg (fun f ↦ f.f n) hcomp
  simp only [HomologicalComplex.comp_f] at hcompn
  change (quotientDGComposition M.unop L.unop K.unop).f n ≫
      ((correctedQuotientDGEnrichedShift a).map K M).f n =
    (HomologicalComplex.tensorHom
      ((correctedQuotientDGEnrichedShift a).map K L)
      ((correctedQuotientDGEnrichedShift a).map L M)).f n ≫
        (quotientDGComposition
          ((correctedQuotientDGEnrichedShift a).obj M).unop
          ((correctedQuotientDGEnrichedShift a).obj L).unop
          ((correctedQuotientDGEnrichedShift a).obj K).unop).f n at hcompn
  have hpre := congrArg
    (fun f ↦ HomologicalComplex.ιTensorObj
      (quotientDGEnrichedHom K L) (quotientDGEnrichedHom L M)
      p q n h ≫ f) hcompn
  change HomologicalComplex.ιTensorObj
      (QuotientMappingCochain L.unop K.unop)
      (QuotientMappingCochain M.unop L.unop) p q n h ≫
        (quotientDGComposition M.unop L.unop K.unop).f n ≫
          ((correctedQuotientDGEnrichedShift a).map K M).f n =
    HomologicalComplex.ιTensorObj
      (QuotientMappingCochain L.unop K.unop)
      (QuotientMappingCochain M.unop L.unop) p q n h ≫
        (HomologicalComplex.tensorHom
          ((correctedQuotientDGEnrichedShift a).map K L)
          ((correctedQuotientDGEnrichedShift a).map L M)).f n ≫
            (quotientDGComposition
              ((correctedQuotientDGEnrichedShift a).obj M).unop
              ((correctedQuotientDGEnrichedShift a).obj L).unop
              ((correctedQuotientDGEnrichedShift a).obj K).unop).f n at hpre
  rw [ιTensorObj_quotientDGComposition_assoc
    M.unop L.unop K.unop h] at hpre
  rw [← Category.assoc] at hpre
  change quotientDGCompositionComponent M.unop L.unop K.unop h ≫
      ((correctedQuotientDGEnrichedShift a).map K M).f n =
    (HomologicalComplex.ιTensorObj
        (quotientDGEnrichedHom K L) (quotientDGEnrichedHom L M)
        p q n h ≫
      (HomologicalComplex.tensorHom
        ((correctedQuotientDGEnrichedShift a).map K L)
        ((correctedQuotientDGEnrichedShift a).map L M)).f n) ≫
          (quotientDGComposition
            ((correctedQuotientDGEnrichedShift a).obj M).unop
            ((correctedQuotientDGEnrichedShift a).obj L).unop
            ((correctedQuotientDGEnrichedShift a).obj K).unop).f n at hpre
  have htensor :
      HomologicalComplex.ιTensorObj
          (quotientDGEnrichedHom K L) (quotientDGEnrichedHom L M)
          p q n h ≫
        (HomologicalComplex.tensorHom
          ((correctedQuotientDGEnrichedShift a).map K L)
          ((correctedQuotientDGEnrichedShift a).map L M)).f n =
      (((correctedQuotientDGEnrichedShift a).map K L).f p ⊗ₘ
        ((correctedQuotientDGEnrichedShift a).map L M).f q) ≫
          HomologicalComplex.ιTensorObj
            (quotientDGEnrichedHom
              ((correctedQuotientDGEnrichedShift a).obj K)
              ((correctedQuotientDGEnrichedShift a).obj L))
            (quotientDGEnrichedHom
              ((correctedQuotientDGEnrichedShift a).obj L)
              ((correctedQuotientDGEnrichedShift a).obj M))
            p q n h := by
    exact GradedObject.Monoidal.ι_tensorHom
      ((correctedQuotientDGEnrichedShift a).map K L).f
      ((correctedQuotientDGEnrichedShift a).map L M).f p q n h
  rw [htensor] at hpre
  rw [Category.assoc] at hpre
  have htarget :
      HomologicalComplex.ιTensorObj
          (quotientDGEnrichedHom
            ((correctedQuotientDGEnrichedShift a).obj K)
            ((correctedQuotientDGEnrichedShift a).obj L))
          (quotientDGEnrichedHom
            ((correctedQuotientDGEnrichedShift a).obj L)
            ((correctedQuotientDGEnrichedShift a).obj M))
          p q n h ≫
        (quotientDGComposition
          ((correctedQuotientDGEnrichedShift a).obj M).unop
          ((correctedQuotientDGEnrichedShift a).obj L).unop
          ((correctedQuotientDGEnrichedShift a).obj K).unop).f n =
      quotientDGCompositionComponent
        ((correctedQuotientDGEnrichedShift a).obj M).unop
        ((correctedQuotientDGEnrichedShift a).obj L).unop
        ((correctedQuotientDGEnrichedShift a).obj K).unop h := by
    change HomologicalComplex.ιTensorObj
        (QuotientMappingCochain
          ((correctedQuotientDGEnrichedShift a).obj L).unop
          ((correctedQuotientDGEnrichedShift a).obj K).unop)
        (QuotientMappingCochain
          ((correctedQuotientDGEnrichedShift a).obj M).unop
          ((correctedQuotientDGEnrichedShift a).obj L).unop)
        p q n h ≫
      (quotientDGComposition
        ((correctedQuotientDGEnrichedShift a).obj M).unop
        ((correctedQuotientDGEnrichedShift a).obj L).unop
        ((correctedQuotientDGEnrichedShift a).obj K).unop).f n = _
    exact ιTensorObj_quotientDGComposition
      ((correctedQuotientDGEnrichedShift a).obj M).unop
      ((correctedQuotientDGEnrichedShift a).obj L).unop
      ((correctedQuotientDGEnrichedShift a).obj K).unop h
  rw [htarget] at hpre
  exact hpre

/-- Smart truncation of enriched shift preserves quotient chain composition. -/
theorem correctedQuotientDGChainShiftMap_comp
    (a : ℤ) (K L M : CorrectedQuotientDGCategory) :
    quotientDGChainEnrichedComp K L M ≫
        correctedQuotientDGChainShiftMap a K M =
      (correctedQuotientDGChainShiftMap a K L ⊗ₘ
          correctedQuotientDGChainShiftMap a L M) ≫
        quotientDGChainEnrichedComp
          ((correctedQuotientDGEnrichedShift a).obj K)
          ((correctedQuotientDGEnrichedShift a).obj L)
          ((correctedQuotientDGEnrichedShift a).obj M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((quotientDGEnrichedHom
      ((correctedQuotientDGEnrichedShift a).obj K)
      ((correctedQuotientDGEnrichedShift a).obj M)).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n)).1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  simp only [HomologicalComplex.comp_f, Category.assoc]
  dsimp only [quotientDGChainEnrichedComp]
  slice_lhs 1 2 =>
    change HomologicalComplex.ιTensorObj
      (quotientDGChainEnrichedHom K L)
      (quotientDGChainEnrichedHom L M) p q n hpq ≫
        quotientTruncatedMapDegree (quotientDGEnrichedComp K L M) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp K L M) hpq
  slice_lhs 2 3 =>
    rw [correctedQuotientDGChainShiftMap_toRestriction]
  slice_lhs 1 2 =>
    rw [quotientTruncatedCompositionComponent_to_raw]
  change ((((quotientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((quotientDGEnrichedHom L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) ≫
      quotientDGCompositionComponent M.unop L.unop K.unop (by
        change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
        omega)) ≫
      ((correctedQuotientDGEnrichedShift a).map K M).f (-(n : ℤ)) = _
  slice_lhs 2 3 =>
    rw [correctedQuotientDGEnrichedShift_component a K L M]
  slice_rhs 1 2 =>
    change HomologicalComplex.ιTensorObj
      (quotientDGChainEnrichedHom K L)
      (quotientDGChainEnrichedHom L M) p q n hpq ≫
        (HomologicalComplex.tensorHom
          (correctedQuotientDGChainShiftMap a K L)
          (correctedQuotientDGChainShiftMap a L M)).f n
    exact quotientChain_ιTensorObj_tensorHom
      (correctedQuotientDGChainShiftMap a K L)
      (correctedQuotientDGChainShiftMap a L M) hpq
  slice_rhs 2 3 =>
    change HomologicalComplex.ιTensorObj
      (quotientDGChainEnrichedHom
        ((correctedQuotientDGEnrichedShift a).obj K)
        ((correctedQuotientDGEnrichedShift a).obj L))
      (quotientDGChainEnrichedHom
        ((correctedQuotientDGEnrichedShift a).obj L)
        ((correctedQuotientDGEnrichedShift a).obj M))
      p q n hpq ≫
        quotientTruncatedMapDegree
          (quotientDGEnrichedComp
            ((correctedQuotientDGEnrichedShift a).obj K)
            ((correctedQuotientDGEnrichedShift a).obj L)
            ((correctedQuotientDGEnrichedShift a).obj M)) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp
        ((correctedQuotientDGEnrichedShift a).obj K)
        ((correctedQuotientDGEnrichedShift a).obj L)
        ((correctedQuotientDGEnrichedShift a).obj M)) hpq
  slice_rhs 2 3 =>
    rw [quotientTruncatedCompositionComponent_to_raw]
  slice_rhs 1 2 =>
    rw [correctedQuotientDGChainShiftMap_tensor_toRestriction]
  let x := (((quotientDGEnrichedHom K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f p ⊗ₘ
    ((quotientDGEnrichedHom L M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f q)
  let y := (((correctedQuotientDGEnrichedShift a).map K L).f (-(p : ℤ)) ⊗ₘ
    ((correctedQuotientDGEnrichedShift a).map L M).f (-(q : ℤ)))
  let z := quotientDGCompositionComponent
    ((correctedQuotientDGEnrichedShift a).obj M).unop
    ((correctedQuotientDGEnrichedShift a).obj L).unop
    ((correctedQuotientDGEnrichedShift a).obj K).unop
    (p := -(p : ℤ)) (q := -(q : ℤ)) (n := -(n : ℤ)) (by omega)
  change x ≫ (y ≫ z) = (x ≫ y) ≫ z
  exact (Category.assoc x y z).symm

/-- The corrected quotient shift after smart truncation, as an actual chain-enriched functor. -/
noncomputable def correctedQuotientDGChainEnrichedShift (a : ℤ) :
    EnrichedFunctor QuotientDGChain
      CorrectedQuotientDGCategory CorrectedQuotientDGCategory where
  obj := (correctedQuotientDGEnrichedShift a).obj
  map := correctedQuotientDGChainShiftMap a
  map_id := correctedQuotientDGChainShiftMap_identity a
  map_comp := correctedQuotientDGChainShiftMap_comp a

/-- Transport the quotient shift through Dold--Kan. -/
noncomputable def correctedQuotientDGSimplicialModuleShift (a : ℤ) :
    EnrichedFunctor CorrectedQuotientDGSimp
      CorrectedQuotientDGSimplicialModuleCategory
      CorrectedQuotientDGSimplicialModuleCategory :=
  CategoryTheory.EnrichedFunctor.transport
    quotientModuleDoldKanEquivalence.inverse
    (correctedQuotientDGChainEnrichedShift a)

/-- Restore geometric arrow orientation on the transported shift. -/
noncomputable def correctedQuotientDGSimplicialModuleShiftOp (a : ℤ) :
    EnrichedFunctor CorrectedQuotientDGSimp
      CorrectedQuotientDGSimplicialModuleCategoryOp
      CorrectedQuotientDGSimplicialModuleCategoryOp :=
  CategoryTheory.EnrichedFunctor.op
    (correctedQuotientDGSimplicialModuleShift a)

/-- Forget module structure from the transported shift. -/
noncomputable def correctedQuotientDGSSetEnrichedShift (a : ℤ) :
    EnrichedFunctor SSet
      CorrectedQuotientDGSSetEnrichedCategory
      CorrectedQuotientDGSSetEnrichedCategory :=
  CategoryTheory.EnrichedFunctor.transport
    quotientCoefficientSimplicialForget
    (correctedQuotientDGSimplicialModuleShiftOp a)

/-- The simultaneous shift as an enriched functor of the underlying simplicial category. -/
noncomputable def correctedQuotientDGSimplicialCategoryShift (a : ℤ) :
    EnrichedFunctor SSet
      CorrectedQuotientDGSimplicialCategory
      CorrectedQuotientDGSimplicialCategory :=
  correctedQuotientDGSSetEnrichedShift a

/-- The simultaneous shift map of the corrected quotient coherent nerve. -/
def correctedQuotientDGShiftNerveMap (a : ℤ) :
    correctedQuotientDGHomotopyCoherentNerve ⟶
      correctedQuotientDGHomotopyCoherentNerve :=
  simplicialNerveMap (correctedQuotientDGSimplicialCategoryShift a)

/-- The degree-one shift as an actual endomorphism of the corrected quotient quasicategory. -/
def correctedQuotientDGShiftQCatMap :
    correctedQuotientDGQCat ⟶ correctedQuotientDGQCat :=
  ObjectProperty.homMk (correctedQuotientDGShiftNerveMap 1)

/-- The degree-minus-one unshift as an actual endomorphism of the corrected quotient
quasicategory. -/
def correctedQuotientDGUnshiftQCatMap :
    correctedQuotientDGQCat ⟶ correctedQuotientDGQCat :=
  ObjectProperty.homMk (correctedQuotientDGShiftNerveMap (-1))

end DrinfeldWord

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
