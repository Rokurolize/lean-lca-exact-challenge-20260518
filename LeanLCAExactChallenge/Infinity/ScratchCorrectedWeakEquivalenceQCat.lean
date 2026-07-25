/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.ScratchCorrectedWeakEquivalenceInQuotient
import LeanLCAExactChallenge.Infinity.ScratchOriginalCoefficientOrdinaryNerve
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeCoherentSimplex
import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial
open QuotientDoldKanMonoidal

/-- The tensor-unit map represented by one degree-zero quotient element. -/
def quotientDGElementSpan (K L : ComplexCategory)
    (x : quotientGradedModule K L 0) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (quotientCoefficientCochainComplex K L).X 0 :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton QuotientCoefficientRing _ (ULift.up x))

@[simp]
theorem quotientDGElementSpan_apply_one (K L : ComplexCategory)
    (x : quotientGradedModule K L 0) :
    (quotientDGElementSpan K L x).hom (1 : QuotientCoefficientRing) = ULift.up x :=
  LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ (ULift.up x)

lemma quotientDGElementSpan_d (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    quotientDGElementSpan K L x ≫
      (quotientCoefficientCochainComplex K L).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply ULift.down_injective
  change (quotientTotalDifferential K L 0).hom (r.down • x) = 0
  rw [map_zsmul, hx, zsmul_zero]

/-- A closed degree-zero quotient element, as a tensor-unit map into smart truncation. -/
def quotientDGChainZeroMapOfClosed (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (quotientDGMappingChain K L).X 0 := by
  let H := quotientCoefficientCochainComplex K L
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  exact H.liftCycles' (quotientDGElementSpan K L x) 1
      (show (ComplexShape.up ℤ).Rel 0 1 by rfl)
      (quotientDGElementSpan_d K L x hx) ≫
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).inv

/-- A closed degree-zero quotient element, lifted to smart-truncation degree zero. -/
def quotientDGChainZeroOfClosed (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    (quotientDGMappingChain K L).X 0 :=
  (quotientDGChainZeroMapOfClosed K L x hx).hom
    (1 : QuotientCoefficientRing)

lemma quotientDGChainZeroMapOfClosed_toRestriction
    (K L : ComplexCategory) (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    quotientDGChainZeroMapOfClosed K L x hx ≫
        ((quotientCoefficientCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      quotientDGElementSpan K L x := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [quotientTruncLEToRestriction_f_zero
    (quotientCoefficientCochainComplex K L) hb]
  dsimp [quotientDGChainZeroMapOfClosed]
  simp only [Category.assoc]
  erw [quotientTruncLEIsoCycles_inv_hom_of_proofs_assoc
    (quotientCoefficientCochainComplex K L) 0 0 rfl rfl hb hb]
  simp

lemma quotientDGChainZeroOfClosed_toRestriction
    (K L : ComplexCategory) (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    (((quotientCoefficientCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom
        (quotientDGChainZeroOfClosed K L x hx) = ULift.up x := by
  have h := ConcreteCategory.congr_hom
    (quotientDGChainZeroMapOfClosed_toRestriction K L x hx)
    (1 : QuotientCoefficientRing)
  change (((quotientCoefficientCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom
        (quotientDGChainZeroOfClosed K L x hx) =
      (quotientDGElementSpan K L x).hom (1 : QuotientCoefficientRing) at h
  exact h.trans (quotientDGElementSpan_apply_one K L x)

/-- A degree-minus-one quotient element, lifted to smart-truncation degree one. -/
def quotientDGChainOneOfDegreeNegOne (K L : ComplexCategory)
    (h : quotientGradedModule K L (-1)) :
    (quotientDGMappingChain K L).X 1 := by
  let H := quotientCoefficientCochainComplex K L
  have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE 1 := by
    rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
    omega
  exact (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).inv.hom (ULift.up h)

lemma quotientTruncLEToRestriction_f_one
    (H : QuotientDGCochain)
    (hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE 1) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1 =
      (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).hom := by
  dsimp [HomologicalComplex.truncLE'ToRestriction]
  have hn' : ¬ ComplexShape.embeddingDownNat.op.BoundaryGE 1 := by
    simpa using hn
  rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_iso_inv
    ComplexShape.embeddingDownNat.op rfl hn']
  dsimp [HomologicalComplex.restrictionXIso,
    HomologicalComplex.truncLE'XIso]
  simp

lemma quotientDGChainOneOfDegreeNegOne_toRestriction
    (K L : ComplexCategory) (h : quotientGradedModule K L (-1)) :
    (((quotientCoefficientCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 1).hom
        (quotientDGChainOneOfDegreeNegOne K L h) = ULift.up h := by
  let H := quotientCoefficientCochainComplex K L
  have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE 1 := by
    rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
    omega
  rw [quotientTruncLEToRestriction_f_one H hn]
  dsimp [quotientDGChainOneOfDegreeNegOne]
  exact (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).inv_hom_id_apply
    (ULift.up h)

lemma quotientDGChainOneBoundary_closed
    (K L : ComplexCategory) (h : quotientGradedModule K L (-1)) :
    (quotientTotalDifferential K L 0).hom
      ((quotientTotalDifferential K L (-1)).hom h) = 0 := by
  have hs := ConcreteCategory.congr_hom
    (quotientTotalDifferential_square K L (-1)) h
  change (quotientTotalDifferential K L 0).hom
      ((quotientTotalDifferential K L (-1)).hom h) =
    (0 : quotientGradedModule K L (-1) ⟶
      quotientGradedModule K L (0 + 1)).hom h at hs
  simpa using hs

lemma quotientDGChainOneOfDegreeNegOne_boundary
    (K L : ComplexCategory) (h : quotientGradedModule K L (-1)) :
    ((quotientDGMappingChain K L).d 1 0).hom
        (quotientDGChainOneOfDegreeNegOne K L h) =
      quotientDGChainZeroOfClosed K L
        ((quotientTotalDifferential K L (-1)).hom h)
        (quotientDGChainOneBoundary_closed K L h) := by
  let H := quotientCoefficientCochainComplex K L
  let r := H.truncLE'ToRestriction ComplexShape.embeddingDownNat
  have hmono : Mono (r.f 0) := by
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
    rw [quotientTruncLEToRestriction_f_zero H hb]
    infer_instance
  apply (ModuleCat.mono_iff_injective (r.f 0)).mp hmono
  have hcomm := ConcreteCategory.congr_hom (r.comm 1 0)
    (quotientDGChainOneOfDegreeNegOne K L h)
  change ((H.restriction ComplexShape.embeddingDownNat).d 1 0).hom
      ((r.f 1).hom (quotientDGChainOneOfDegreeNegOne K L h)) =
    (r.f 0).hom
      (((quotientDGMappingChain K L).d 1 0).hom
        (quotientDGChainOneOfDegreeNegOne K L h)) at hcomm
  have hzero := quotientDGChainZeroOfClosed_toRestriction K L
    ((quotientTotalDifferential K L (-1)).hom h)
    (quotientDGChainOneBoundary_closed K L h)
  have hone := quotientDGChainOneOfDegreeNegOne_toRestriction K L h
  change (r.f 0).hom
      (((quotientDGMappingChain K L).d 1 0).hom
        (quotientDGChainOneOfDegreeNegOne K L h)) =
    (r.f 0).hom
      (quotientDGChainZeroOfClosed K L
        ((quotientTotalDifferential K L (-1)).hom h)
        (quotientDGChainOneBoundary_closed K L h))
  calc
    _ = ((H.restriction ComplexShape.embeddingDownNat).d 1 0).hom
        ((r.f 1).hom (quotientDGChainOneOfDegreeNegOne K L h)) := by
      simpa only [ModuleCat.comp_apply] using hcomm.symm
    _ = ((H.restriction ComplexShape.embeddingDownNat).d 1 0).hom (ULift.up h) := by
      rw [hone]
    _ = ULift.up ((quotientTotalDifferential K L (-1)).hom h) := by
      rfl
    _ = _ := hzero.symm

/-- The explicit Dold--Kan one-simplex determined by degree-zero and degree-one quotient-chain elements. -/
def quotientDoldKanGammaOneSimplex (T : QuotientChain) (x : T.X 0) (h : T.X 1) :
    (quotientModuleDoldKanEquivalence.inverse.obj T).obj (op ⦋1⦌) := by
  let x' : (quotientModuleDoldKanEquivalence.inverse.obj T).obj (op ⦋0⦌) :=
    ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x
  let h' : (quotientModuleDoldKanEquivalence.inverse.obj T).obj (op ⦋1⦌) :=
    ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h
  exact ((quotientModuleDoldKanEquivalence.inverse.obj T).σ 0).hom x' + h'

/-- The final face of the explicit quotient Dold--Kan one-simplex is `x + d(h)`. -/
theorem quotientDoldKanGammaOneSimplex_delta_zero
    (T : QuotientChain) (x : T.X 0) (h : T.X 1) :
    ((quotientModuleDoldKanEquivalence.inverse.obj T).δ 0).hom
        (quotientDoldKanGammaOneSimplex T x h) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom
        (x + (T.d 1 0).hom h) := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 0).hom
      (quotientDoldKanGammaOneSimplex T x h) = _
  dsimp [quotientDoldKanGammaOneSimplex]
  erw [map_add]
  erw [map_add]
  apply congrArg₂ (· + ·)
  · have hcat := SimplicialObject.δ_comp_σ_self'
      (X := AlgebraicTopology.DoldKan.Γ₀.obj T)
      (j := (0 : Fin 2)) (i := (0 : Fin 1)) (by decide)
    exact congrArg (fun q ↦ q.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) hcat
  · erw [← ConcreteCategory.comp_apply]
    rw [← (AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 1]
    change ConcreteCategory.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan (op ⦋1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋1⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.obj T).map (SimplexCategory.δ 0).op) h = _
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id]
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀]
    rw [(AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 0]
    erw [ConcreteCategory.comp_apply]

/-- The initial face of the explicit quotient Dold--Kan one-simplex is `x`. -/
theorem quotientDoldKanGammaOneSimplex_delta_one
    (T : QuotientChain) (x : T.X 0) (h : T.X 1) :
    ((quotientModuleDoldKanEquivalence.inverse.obj T).δ 1).hom
        (quotientDoldKanGammaOneSimplex T x h) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
      (quotientDoldKanGammaOneSimplex T x h) = _
  dsimp [quotientDoldKanGammaOneSimplex]
  erw [map_add]
  have hx :
      ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.obj T).σ 0).hom
            (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) =
        ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x := by
    have hcat := SimplicialObject.δ_comp_σ_succ'
      (X := AlgebraicTopology.DoldKan.Γ₀.obj T)
      (j := (1 : Fin 2)) (i := (0 : Fin 1)) (by decide)
    exact congrArg (fun q ↦ q.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) hcat
  have hh :
      ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h) = 0 := by
    erw [← ConcreteCategory.comp_apply]
    rw [← (AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 1]
    change ConcreteCategory.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan (op ⦋1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋1⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.obj T).map (SimplexCategory.δ 1).op) h = 0
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id]
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero]
    · simp
    · intro hEq
      have hlen : 1 = 0 := by simpa using congrArg SimplexCategory.len hEq
      omega
    · simpa only [AlgebraicTopology.DoldKan.Isδ₀.iff] using (by omega : (1 : Fin 2) ≠ 0)
  calc
    _ = ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x +
        ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h) :=
      congrArg (fun z ↦ z + _) hx
    _ = _ := by simp only [hh, add_zero]; rfl

/-- The composition of two closed quotient-element spans is the span of their quotient composition. -/
theorem quotientDGElementSpan_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0) :
    (λ_ (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv ≫
        (quotientDGElementSpan L M y ⊗ₘ quotientDGElementSpan K L x) ≫
        quotientDGCompositionComponent K L M rfl =
      quotientDGElementSpan K M (quotientCompose x y) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change QuotientCoefficientRing at r
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [quotientDGElementSpan_apply_one]
  change (quotientDGCompositionComponent K L M rfl).hom
      (ULift.up y ⊗ₜ[QuotientCoefficientRing]
        (quotientDGElementSpan K L x).hom r) =
    (quotientDGElementSpan K M (quotientCompose x y)).hom r
  rw [show (quotientDGElementSpan K L x).hom r =
      r • (ULift.up x : quotientCoefficientModule
        (quotientGradedModule K L 0)) by
    exact LinearMap.toSpanSingleton_apply _ _ _ _]
  rw [TensorProduct.tmul_smul, map_smul]
  unfold quotientDGCompositionComponent quotientDGElementSpan quotientCompose
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  rfl

/-- The quotient composition of two closed degree-zero elements is closed. -/
theorem quotientCompose_closed
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    (quotientTotalDifferential K M 0).hom (quotientCompose x y) = 0 := by
  have h := quotientCompositionMap_d K L M 0 0 x y
  change (quotientTotalDifferential K M 0).hom (quotientCompose x y) = _ at h
  rw [hx, hy] at h
  simp only [map_zero, LinearMap.zero_apply, Int.negOnePow_zero,
    one_smul, zero_add] at h
  exact h

/-- Smart-truncation degree-zero composition agrees with raw quotient composition on closed elements. -/
theorem quotientDGChainZeroMapOfClosed_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    (λ_ (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv ≫
        (quotientDGChainZeroMapOfClosed L M y hy ⊗ₘ
          quotientDGChainZeroMapOfClosed K L x hx) ≫
        quotientTruncatedMapComponent
          (quotientDGEnrichedComp (Opposite.op M) (Opposite.op L) (Opposite.op K)) rfl =
      quotientDGChainZeroMapOfClosed K M (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) := by
  apply (cancel_mono
    (((quotientCoefficientCochainComplex K M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0)).1
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    change quotientTruncatedMapComponent
        (quotientDGEnrichedComp
          (show CorrectedQuotientDGCategory from Opposite.op M)
          (show CorrectedQuotientDGCategory from Opposite.op L)
          (show CorrectedQuotientDGCategory from Opposite.op K)) rfl ≫
      ((quotientDGEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op K)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0
    exact quotientTruncatedCompositionComponent_to_raw
      (show CorrectedQuotientDGCategory from Opposite.op M)
      (show CorrectedQuotientDGCategory from Opposite.op L)
      (show CorrectedQuotientDGCategory from Opposite.op K) rfl
  slice_lhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  have hyR := quotientDGChainZeroMapOfClosed_toRestriction L M y hy
  change quotientDGChainZeroMapOfClosed L M y hy ≫
      ((quotientDGEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op L)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    quotientDGElementSpan L M y at hyR
  have hxR := quotientDGChainZeroMapOfClosed_toRestriction K L x hx
  change quotientDGChainZeroMapOfClosed K L x hx ≫
      ((quotientDGEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op L)
        (show CorrectedQuotientDGCategory from Opposite.op K)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    quotientDGElementSpan K L x at hxR
  have hxyR := quotientDGChainZeroMapOfClosed_toRestriction K M
    (quotientCompose x y) (quotientCompose_closed K L M x y hx hy)
  change quotientDGChainZeroMapOfClosed K M (quotientCompose x y)
      (quotientCompose_closed K L M x y hx hy) ≫
      ((quotientDGEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op K)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    quotientDGElementSpan K M (quotientCompose x y) at hxyR
  rw [hyR, hxR]
  change (λ_ (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv ≫
      (quotientDGElementSpan L M y ⊗ₘ quotientDGElementSpan K L x) ≫
      quotientDGCompositionComponent K L M rfl =
    quotientDGChainZeroMapOfClosed K M (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) ≫
      ((quotientDGEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op K)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0
  rw [hxyR]
  exact quotientDGElementSpan_comp K L M x y

/-- Dold--Kan identifies the ordinary categories underlying the smart-truncated corrected quotient and its simplicial-module enrichment. -/
noncomputable def correctedQuotientDGDoldKanUnderlyingEquivalence :
    ForgetEnrichment QuotientDGChain CorrectedQuotientDGCategory ≌
      ForgetEnrichment CorrectedQuotientDGSimp
        CorrectedQuotientDGSimplicialModuleCategory :=
  (TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv
      (ForgetEnrichment QuotientDGChain CorrectedQuotientDGCategory)
      quotientModuleDoldKanEquivalence.inverse).symm.trans
    (TransportEnrichment.forgetEnrichmentEquiv
      quotientModuleDoldKanEquivalence.inverse
      CorrectedQuotientDGCategory
      (fun T ↦ quotientDoldKanInverseUnitHomEquiv T)
      (fun T f ↦ quotientDoldKanInverseUnitHomEquiv_apply T f))

/-- Forgetting quotient-coefficient module structure induces the underlying corrected simplicial functor. -/
noncomputable def correctedQuotientDGForgetModuleOrdinaryFunctor :
    ForgetEnrichment CorrectedQuotientDGSimp
        CorrectedQuotientDGSimplicialModuleCategoryOp ⥤
      CorrectedQuotientDGSimplicialCategory where
  obj X := ForgetEnrichment.of SSet X
  map f := ForgetEnrichment.homOf SSet
    (Functor.LaxMonoidal.ε quotientCoefficientSimplicialForget ≫
      quotientCoefficientSimplicialForget.map
        (ForgetEnrichment.homTo CorrectedQuotientDGSimp f))
  map_id X := by
    rw [ForgetEnrichment.homTo_id, ← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [ForgetEnrichment.homTo_comp,
      quotientCoefficientSimplicialForget.map_comp,
      quotientCoefficientSimplicialForget.map_comp,
      ← Category.assoc,
      ← Functor.LaxMonoidal.left_unitality_inv,
      Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_assoc,
      ← TransportEnrichment.eComp_eq,
      ← ForgetEnrichment.homOf_comp,
      leftUnitor_inv_naturality_assoc,
      ← tensorHom_def'_assoc,
      tensorHom_comp_tensorHom_assoc]
    rfl

/-- Transport the opposite ordinary category of smart-truncated quotient morphisms to the corrected simplicial category. -/
noncomputable def correctedQuotientDGChainToSimplicialCategory :
    (ForgetEnrichment QuotientDGChain CorrectedQuotientDGCategory)ᵒᵖ ⥤
      CorrectedQuotientDGSimplicialCategory :=
  correctedQuotientDGDoldKanUnderlyingEquivalence.functor.op ⋙
    (forgetEnrichmentOppositeEquivalence CorrectedQuotientDGSimp
      CorrectedQuotientDGSimplicialModuleCategory).inverse ⋙
    correctedQuotientDGForgetModuleOrdinaryFunctor

/-- A closed degree-zero quotient element as a tensor-unit-shaped chain-enriched morphism. -/
def quotientDGChainMorphismMapOfClosed {K L : ComplexCategory}
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    𝟙_ QuotientDGChain ⟶
      quotientDGChainEnrichedHom (Opposite.op L) (Opposite.op K) :=
  (ChainComplex.fromSingle₀Equiv
    (quotientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).symm
      (quotientDGChainZeroMapOfClosed K L x hx)

/-- A closed quotient element as a morphism in the ordinary category underlying the smart truncation. -/
def quotientDGChainMorphismOfClosed {K L : ComplexCategory}
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    (ForgetEnrichment.of QuotientDGChain (Opposite.op L) :
      ForgetEnrichment QuotientDGChain CorrectedQuotientDGCategory) ⟶
      ForgetEnrichment.of QuotientDGChain (Opposite.op K) :=
  ForgetEnrichment.homOf QuotientDGChain
    (quotientDGChainMorphismMapOfClosed x hx)

/-- The Dold--Kan map carries the degree-zero identity summand by the chain-map component. -/
theorem quotientGammaZero_map_on_identity_summand
    {A B : QuotientChain} (f : A ⟶ B) :
    ((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌) =
      f.f 0 ≫
        ((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) := by
  change _ ≫ (AlgebraicTopology.DoldKan.Γ₀.splitting A).desc (op ⦋0⦌) _ = _
  erw [(AlgebraicTopology.DoldKan.Γ₀.splitting A).ι_desc]
  rfl

/-- The degree-zero Dold--Kan projection is inverse to the identity-summand inclusion. -/
theorem quotientModuleDoldKanInverseZeroIso_inv_on_identity_summand
    (A : QuotientChain) :
    ((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
        (quotientModuleDoldKanInverseZeroIso A).inv =
      𝟙 (A.X 0) := by
  dsimp [quotientModuleDoldKanInverseZeroIso]
  erw [(AlgebraicTopology.DoldKan.Γ₀.splitting A).ι_desc]
  apply eqToHom_refl

/-- The degree-zero Dold--Kan projection is the splitting projection. -/
theorem quotientGammaZero_projection_eq_zeroIso_inv (A : QuotientChain) :
    (AlgebraicTopology.DoldKan.Γ₀.splitting A).πSummand
        (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) =
      (quotientModuleDoldKanInverseZeroIso A).inv := by
  apply (AlgebraicTopology.DoldKan.Γ₀.splitting A).hom_ext'
  intro I
  have hI := doldKanIndexSet_zero_eq_id I
  subst I
  rw [SimplicialObject.Splitting.cofan_inj_πSummand_eq_id]
  change 𝟙 (A.X 0) = _
  exact (quotientModuleDoldKanInverseZeroIso_inv_on_identity_summand A).symm

/-- Naturality of the degree-zero quotient Dold--Kan projection. -/
theorem quotientModuleDoldKanInverseZeroIso_inv_naturality
    {A B : QuotientChain} (f : A ⟶ B) :
    (quotientModuleDoldKanEquivalence.inverse.map f).app (op ⦋0⦌) ≫
        (quotientModuleDoldKanInverseZeroIso B).inv =
      (quotientModuleDoldKanInverseZeroIso A).inv ≫ f.f 0 := by
  change (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌) ≫
      (quotientModuleDoldKanInverseZeroIso B).inv =
    (quotientModuleDoldKanInverseZeroIso A).inv ≫ f.f 0
  apply (AlgebraicTopology.DoldKan.Γ₀.splitting A).hom_ext'
  intro I
  have hI := doldKanIndexSet_zero_eq_id I
  subst I
  calc
    _ = (((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
            (AlgebraicTopology.DoldKan.Γ₀.map f).app (op ⦋0⦌)) ≫
          (quotientModuleDoldKanInverseZeroIso B).inv :=
      (Category.assoc _ _ _).symm
    _ = (f.f 0 ≫
          ((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan (op ⦋0⦌)).inj
            (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌))) ≫
          (quotientModuleDoldKanInverseZeroIso B).inv := by
      rw [quotientGammaZero_map_on_identity_summand f]
    _ = f.f 0 ≫
          (((AlgebraicTopology.DoldKan.Γ₀.splitting B).cofan (op ⦋0⦌)).inj
            (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
              (quotientModuleDoldKanInverseZeroIso B).inv) :=
      Category.assoc _ _ _
    _ = f.f 0 := by
      exact (congrArg (fun t ↦ f.f 0 ≫ t)
        (quotientModuleDoldKanInverseZeroIso_inv_on_identity_summand B)).trans
          (Category.comp_id _)
    _ = _ := by
      symm
      calc
        _ = ((((AlgebraicTopology.DoldKan.Γ₀.splitting A).cofan (op ⦋0⦌)).inj
              (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
                (quotientModuleDoldKanInverseZeroIso A).inv) ≫ f.f 0) :=
          (Category.assoc _ _ _).symm
        _ = 𝟙 (A.X 0) ≫ f.f 0 := congrArg (fun t ↦ t ≫ f.f 0)
          (quotientModuleDoldKanInverseZeroIso_inv_on_identity_summand A)
        _ = _ := Category.id_comp _

/-- The corrected-coefficient Dold--Kan counit before removing the Karoubi wrapper. -/
def quotientDoldKanCounitKaroubiMap (T : QuotientChain) :
    (CategoryTheory.Idempotents.toKaroubi _).obj
          ((AlgebraicTopology.normalizedMooreComplex QuotientModule).obj
            (AlgebraicTopology.DoldKan.Γ₀.obj T)) ⟶
      (CategoryTheory.Idempotents.toKaroubi _).obj T :=
  (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
      QuotientModule).inv.app (AlgebraicTopology.DoldKan.Γ₀.obj T) ≫
    AlgebraicTopology.DoldKan.N₁Γ₀.hom.app T

set_option linter.flexible false in
theorem quotientDoldKanCounit_eq_preimage (T : QuotientChain) :
    quotientModuleDoldKanEquivalence.counitIso.hom.app T =
      (CategoryTheory.Idempotents.fullyFaithfulToKaroubi _).preimage
        (quotientDoldKanCounitKaroubiMap T) := by
  simp [CategoryTheory.Abelian.DoldKan.equivalence,
    CategoryTheory.Abelian.DoldKan.comparisonN,
    CategoryTheory.Idempotents.DoldKan.equivalence_counitIso,
    CategoryTheory.Idempotents.DoldKan.η,
    quotientDoldKanCounitKaroubiMap]
  let e := CategoryTheory.Idempotents.toKaroubiEquivalence QuotientChain
  let a := (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
      QuotientModule).inv.app (AlgebraicTopology.DoldKan.Γ₀.obj T)
  let b := AlgebraicTopology.DoldKan.N₁Γ₀.hom.app T
  change (e.unitIso.hom.app _ ≫ e.inverse.map a) ≫
      (e.inverse.map b ≫ e.unitIso.inv.app T) =
    (CategoryTheory.Idempotents.fullyFaithfulToKaroubi _).preimage (a ≫ b)
  exact toKaroubiEquivalence_preimage_comp_eq_direct a b

/-- Degree zero of the corrected-coefficient Dold--Kan counit. -/
theorem quotientDoldKanCounit_f_zero (T : QuotientChain) :
    (quotientModuleDoldKanEquivalence.counitIso.hom.app T).f 0 =
      (NormalizedMooreComplex.objX
          (quotientModuleDoldKanEquivalence.inverse.obj T) 0).arrow ≫
        (quotientModuleDoldKanInverseZeroIso T).inv := by
  rw [quotientDoldKanCounit_eq_preimage]
  change (quotientDoldKanCounitKaroubiMap T).f.f 0 = _
  simp [quotientDoldKanCounitKaroubiMap,
    AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi,
    quotientGammaZero_projection_eq_zeroIso_inv]

/-- Naturality of the degree-zero quotient Dold--Kan inclusion. -/
theorem quotientModuleDoldKanInverseZeroIso_hom_naturality
    {A B : QuotientChain} (f : A ⟶ B) :
    (quotientModuleDoldKanInverseZeroIso A).hom ≫
        (quotientModuleDoldKanEquivalence.inverse.map f).app (op ⦋0⦌) =
      f.f 0 ≫ (quotientModuleDoldKanInverseZeroIso B).hom := by
  apply (cancel_mono (quotientModuleDoldKanInverseZeroIso B).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [quotientModuleDoldKanInverseZeroIso_inv_naturality]
  simp

/-- The Dold--Kan inverse lax unit is the degree-zero identity-summand inclusion. -/
theorem quotientDoldKanInverseLaxUnit_f_zero :
    (Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse).app
        (op ⦋0⦌) =
      (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).hom := by
  let adj := quotientModuleDoldKanEquivalence.toAdjunction
  let u := Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse
  let X : QuotientSimplicialModule := 𝟙_ QuotientSimplicialModule
  let Y := quotientModuleDoldKanEquivalence.inverse.obj (𝟙_ QuotientChain)
  let qX := (NormalizedMooreComplex.objX X 0).arrow
  let qY := (NormalizedMooreComplex.objX Y 0).arrow
  have hadj :
      quotientModuleDoldKanEquivalence.functor.map u ≫
          quotientModuleDoldKanEquivalence.counitIso.hom.app (𝟙_ QuotientChain) =
        QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit := by
    change quotientModuleDoldKanEquivalence.functor.map
        (adj.homEquiv _ _ QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit) ≫
      adj.counit.app (𝟙_ QuotientChain) =
        QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit
    exact (adj.homEquiv_counit _ _
      (adj.homEquiv _ _ QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit)).symm.trans
        (Equiv.symm_apply_apply _ QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit)
  have hchain := HomologicalComplex.congr_hom hadj 0
  have hincRaw := HomologicalComplex.congr_hom
    ((inclusionOfMooreComplex QuotientModule).naturality u) 0
  have hqX :
      ((inclusionOfMooreComplex QuotientModule).app X).f 0 = qX := by
    dsimp only [qX]
    exact inclusionOfMooreComplexMap_f _ 0
  have hqY :
      ((inclusionOfMooreComplex QuotientModule).app Y).f 0 = qY := by
    dsimp only [qY]
    exact inclusionOfMooreComplexMap_f _ 0
  have hinc :
      ((normalizedMooreComplex QuotientModule).map u).f 0 ≫ qY =
        qX ≫ u.app (op ⦋0⦌) := by
    rw [← hqY, ← hqX]
    exact hincRaw
  have hcounit :
      qY ≫ (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv =
        (quotientModuleDoldKanEquivalence.counitIso.hom.app
          (𝟙_ QuotientChain)).f 0 := by
    change (NormalizedMooreComplex.objX Y 0).arrow ≫
        (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv = _
    rw [quotientDoldKanCounit_f_zero]
  have huinv :
      u.app (op ⦋0⦌) ≫
          (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv = 𝟙 _ := by
    letI : IsIso qX := by
      change IsIso (⊤ : Subobject (X.obj (op ⦋0⦌))).arrow
      infer_instance
    letI : Epi qX := IsIso.epi_of_iso qX
    apply (cancel_epi qX).1
    calc
      qX ≫ (u.app (op ⦋0⦌) ≫
          (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv) =
        (qX ≫ u.app (op ⦋0⦌)) ≫
          (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv :=
        (Category.assoc _ _ _).symm
      _ = (((normalizedMooreComplex QuotientModule).map u).f 0 ≫ qY) ≫
          (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv :=
        congrArg (fun t ↦ t ≫
          (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv) hinc.symm
      _ = ((normalizedMooreComplex QuotientModule).map u).f 0 ≫
          (qY ≫ (quotientModuleDoldKanInverseZeroIso
            (𝟙_ QuotientChain)).inv) := Category.assoc _ _ _
      _ = ((normalizedMooreComplex QuotientModule).map u).f 0 ≫
          (quotientModuleDoldKanEquivalence.counitIso.hom.app
            (𝟙_ QuotientChain)).f 0 := congrArg _ hcounit
      _ = QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit.f 0 := hchain
      _ = qX := QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit_f_zero
      _ = qX ≫ 𝟙 _ := (Category.comp_id _).symm
  apply (cancel_mono
    (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).inv).1
  rw [huinv, Iso.hom_inv_id]

/-- The Dold--Kan inverse lax unit is the degree-zero identity-summand inclusion on `1`. -/
theorem quotientDoldKanInverseLaxUnit_f_zero_apply_one :
    ((Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse).app
      (op ⦋0⦌)).hom
        (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing)) =
      (quotientModuleDoldKanInverseZeroIso (𝟙_ QuotientChain)).hom.hom
        (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing)) := by
  exact ConcreteCategory.congr_hom quotientDoldKanInverseLaxUnit_f_zero _

/-- The module-forgetful lax unit sends the unique type-level unit point to the ring unit. -/
@[simp]
theorem quotientCoefficientForgetLaxUnit_apply_unit :
    Functor.LaxMonoidal.ε (forget (ModuleCat.{1} QuotientCoefficientRing))
        PUnit.unit = (1 : QuotientCoefficientRing) := by
  change ((ModuleCat.adj QuotientCoefficientRing).homEquiv _ _
    (Functor.OplaxMonoidal.η (ModuleCat.free QuotientCoefficientRing)))
      PUnit.unit = 1
  rw [ModuleCat.adj_homEquiv]
  exact ModuleCat.free_η_freeMk QuotientCoefficientRing PUnit.unit

/-- Forgetting a tensor-unit map of simplicial modules and taking its vertex evaluates it at `1`. -/
@[simp]
theorem quotientCoefficientSimplicialForget_unitHom_vertex
    (X : CorrectedQuotientDGSimp)
    (φ : 𝟙_ CorrectedQuotientDGSimp ⟶ X) :
    SSet.unitHomEquiv (quotientCoefficientSimplicialForget.obj X)
        (Functor.LaxMonoidal.ε quotientCoefficientSimplicialForget ≫
          quotientCoefficientSimplicialForget.map φ) =
      (φ.app (op ⦋0⦌)).hom
        (show (𝟙_ CorrectedQuotientDGSimp).obj (op ⦋0⦌) from
          (1 : QuotientCoefficientRing)) := by
  change ((Functor.LaxMonoidal.ε
      (forget (ModuleCat.{1} QuotientCoefficientRing))) ≫
        (forget (ModuleCat.{1} QuotientCoefficientRing)).map
          (φ.app (op ⦋0⦌))) PUnit.unit = _
  change (φ.app (op ⦋0⦌)).hom
      (Functor.LaxMonoidal.ε (forget (ModuleCat.{1} QuotientCoefficientRing))
        PUnit.unit) = (φ.app (op ⦋0⦌)).hom
      (show (𝟙_ CorrectedQuotientDGSimp).obj (op ⦋0⦌) from
        (1 : QuotientCoefficientRing))
  rw [quotientCoefficientForgetLaxUnit_apply_unit]

/-- A tensor-unit chain map has the expected degree-zero Dold--Kan vertex. -/
@[simp]
theorem quotientDoldKanInverseUnitHomEquiv_vertex
    (T : QuotientChain) (f : 𝟙_ QuotientChain ⟶ T) :
    ((quotientDoldKanInverseUnitHomEquiv T f).app (op ⦋0⦌)).hom
        (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing)) =
      (quotientModuleDoldKanInverseZeroIso T).hom.hom
        ((f.f 0).hom
          (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing))) := by
  rw [quotientDoldKanInverseUnitHomEquiv_apply]
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  rw [quotientDoldKanInverseLaxUnit_f_zero_apply_one]
  exact ConcreteCategory.congr_hom
    (quotientModuleDoldKanInverseZeroIso_hom_naturality f)
    (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing))

/-- The mapping-space vertex represented by a closed degree-zero quotient element. -/
def correctedQuotientDGMappingVertexOfClosed (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    correctedQuotientDGMappingSSet K L _⦋0⦌ :=
  (quotientModuleDoldKanInverseZeroIso (quotientDGMappingChain K L)).hom.hom
    (quotientDGChainZeroOfClosed K L x hx)

/-- A closed degree-zero quotient element as an actual morphism of the corrected quotient simplicial category. -/
noncomputable def correctedQuotientDGMorphismOfClosed {K L : ComplexCategory}
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    correctedQuotientDGObject K ⟶ correctedQuotientDGObject L :=
  correctedQuotientDGChainToSimplicialCategory.map
    (Opposite.op (quotientDGChainMorphismOfClosed x hx))

@[simp]
theorem correctedQuotientDGMorphismOfClosed_homEquiv
    (K L : ComplexCategory) (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    SimplicialCategory.homEquiv'
        (correctedQuotientDGObject K) (correctedQuotientDGObject L)
        (correctedQuotientDGMorphismOfClosed x hx) =
      correctedQuotientDGMappingVertexOfClosed K L x hx := by
  change SSet.unitHomEquiv (correctedQuotientDGMappingSSet K L)
      (Functor.LaxMonoidal.ε quotientCoefficientSimplicialForget ≫
        quotientCoefficientSimplicialForget.map
          (quotientDoldKanInverseUnitHomEquiv
            (quotientDGMappingChain K L)
            (quotientDGChainMorphismMapOfClosed x hx))) =
    correctedQuotientDGMappingVertexOfClosed K L x hx
  rw [quotientCoefficientSimplicialForget_unitHom_vertex]
  change (((quotientDoldKanInverseUnitHomEquiv
      (quotientDGMappingChain K L)
      (quotientDGChainMorphismMapOfClosed x hx)).app (op ⦋0⦌)).hom
        (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing))) = _
  rw [quotientDoldKanInverseUnitHomEquiv_vertex]
  rw [show (quotientDGChainMorphismMapOfClosed x hx).f 0 =
      quotientDGChainZeroMapOfClosed K L x hx by
    exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _]
  rfl

@[simp]
theorem quotientDGChainMorphismMapOfClosed_f_zero
    {K L : ComplexCategory} (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0) :
    (quotientDGChainMorphismMapOfClosed x hx).f 0 =
      quotientDGChainZeroMapOfClosed K L x hx := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

set_option maxHeartbeats 4000000 in
-- Reducing the degree-zero tensor-unit transports requires extra elaboration budget.
theorem quotientDGChainMorphismMapOfClosed_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    (λ_ (𝟙_ QuotientDGChain)).inv ≫
        (quotientDGChainMorphismMapOfClosed y hy ⊗ₘ
          quotientDGChainMorphismMapOfClosed x hx) ≫
        quotientDGChainEnrichedComp
          (show CorrectedQuotientDGCategory from Opposite.op M)
          (show CorrectedQuotientDGCategory from Opposite.op L)
          (show CorrectedQuotientDGCategory from Opposite.op K) =
      quotientDGChainMorphismMapOfClosed (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  have hunit : (λ_ (𝟙_ QuotientDGChain)).inv.f 0 =
      (HomologicalComplex.leftUnitor' (𝟙_ QuotientDGChain)).inv 0 := rfl
  rw [hunit, HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (quotientDGChainMorphismMapOfClosed y hy)
      (quotientDGChainMorphismMapOfClosed x hx)).f 0
    rw [quotientChain_ιTensorObj_tensorHom]
  simp only [Category.assoc, quotientDGChainMorphismMapOfClosed_f_zero]
  dsimp only [quotientDGChainEnrichedComp]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (quotientDGChainEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op L))
      (quotientDGChainEnrichedHom
        (show CorrectedQuotientDGCategory from Opposite.op L)
        (show CorrectedQuotientDGCategory from Opposite.op K)) 0 0 0 rfl ≫
      quotientTruncatedMapDegree
        (quotientDGEnrichedComp
          (show CorrectedQuotientDGCategory from Opposite.op M)
          (show CorrectedQuotientDGCategory from Opposite.op L)
          (show CorrectedQuotientDGCategory from Opposite.op K)) 0
    exact ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op L)
        (show CorrectedQuotientDGCategory from Opposite.op K)) rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change QuotientCoefficientRing at r
  simp only [ModuleCat.comp_apply]
  rw [ChainComplex.single₀ObjXSelf]
  simp only [Iso.refl_inv]
  exact ConcreteCategory.congr_hom
    (quotientDGChainZeroMapOfClosed_comp K L M x y hx hy) r

/-- Ordinary composition in the smart-truncated quotient category agrees with raw quotient composition. -/
theorem quotientDGChainMorphismOfClosed_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    quotientDGChainMorphismOfClosed y hy ≫
        quotientDGChainMorphismOfClosed x hx =
      quotientDGChainMorphismOfClosed (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) := by
  change (λ_ (𝟙_ QuotientDGChain)).inv ≫
      (quotientDGChainMorphismMapOfClosed y hy ⊗ₘ
        quotientDGChainMorphismMapOfClosed x hx) ≫
      quotientDGChainEnrichedComp
        (show CorrectedQuotientDGCategory from Opposite.op M)
        (show CorrectedQuotientDGCategory from Opposite.op L)
        (show CorrectedQuotientDGCategory from Opposite.op K) =
    quotientDGChainMorphismMapOfClosed (quotientCompose x y)
      (quotientCompose_closed K L M x y hx hy)
  exact quotientDGChainMorphismMapOfClosed_comp K L M x y hx hy

/-- The smart-truncated identity element is the enriched identity in degree zero. -/
@[simp]
theorem quotientDGChainZeroMapOfClosed_identity (K : ComplexCategory) :
    quotientDGChainZeroMapOfClosed K K (quotientIdentityElement K)
        (quotientIdentityElement_closed K) =
      quotientDGChainIdentityDegreeZero
        (show CorrectedQuotientDGCategory from Opposite.op K) := by
  apply (cancel_mono
    (((quotientCoefficientCochainComplex K K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0)).1
  rw [quotientDGChainZeroMapOfClosed_toRestriction]
  have h := quotientDGChainIdentityDegreeZero_toRestriction
    (show CorrectedQuotientDGCategory from Opposite.op K)
  change quotientDGChainIdentityDegreeZero
      (show CorrectedQuotientDGCategory from Opposite.op K) ≫
        ((quotientCoefficientCochainComplex K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      quotientIdentitySpan K at h
  rw [h]
  rfl

/-- The chain-enriched morphism represented by the quotient identity is the enriched identity. -/
@[simp]
theorem quotientDGChainMorphismMapOfClosed_identity (K : ComplexCategory) :
    quotientDGChainMorphismMapOfClosed (quotientIdentityElement K)
        (quotientIdentityElement_closed K) =
      quotientDGChainEnrichedId
        (show CorrectedQuotientDGCategory from Opposite.op K) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [quotientDGChainMorphismMapOfClosed_f_zero,
    quotientDGChainEnrichedId_f_zero,
    quotientDGChainZeroMapOfClosed_identity]

/-- The ordinary smart-truncated morphism represented by the quotient identity is the identity. -/
@[simp]
theorem quotientDGChainMorphismOfClosed_identity (K : ComplexCategory) :
    quotientDGChainMorphismOfClosed (quotientIdentityElement K)
        (quotientIdentityElement_closed K) =
      𝟙 (ForgetEnrichment.of QuotientDGChain
        (show CorrectedQuotientDGCategory from Opposite.op K)) := by
  change quotientDGChainMorphismMapOfClosed (quotientIdentityElement K)
      (quotientIdentityElement_closed K) =
    quotientDGChainEnrichedId
      (show CorrectedQuotientDGCategory from Opposite.op K)
  exact quotientDGChainMorphismMapOfClosed_identity K

/-- Actual corrected simplicial morphisms preserve raw quotient composition. -/
theorem correctedQuotientDGMorphismOfClosed_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    correctedQuotientDGMorphismOfClosed x hx ≫
        correctedQuotientDGMorphismOfClosed y hy =
      correctedQuotientDGMorphismOfClosed (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) := by
  unfold correctedQuotientDGMorphismOfClosed
  rw [← correctedQuotientDGChainToSimplicialCategory.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simpa using quotientDGChainMorphismOfClosed_comp K L M x y hx hy

/-- The actual corrected simplicial morphism represented by the quotient identity is the identity. -/
@[simp]
theorem correctedQuotientDGMorphismOfClosed_identity (K : ComplexCategory) :
    correctedQuotientDGMorphismOfClosed (quotientIdentityElement K)
        (quotientIdentityElement_closed K) =
      𝟙 (correctedQuotientDGObject K) := by
  unfold correctedQuotientDGMorphismOfClosed
  rw [quotientDGChainMorphismOfClosed_identity]
  change correctedQuotientDGChainToSimplicialCategory.map (𝟙 _) = 𝟙 _
  exact correctedQuotientDGChainToSimplicialCategory.map_id _

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
