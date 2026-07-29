/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationDifferentialInduction

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- The tensor product of the factors strictly after the first two arrows. -/
abbrev headContractionRemainderModule
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    ModuleCat.{0} ℤ :=
  tensorModuleList (finFamilyList
    (fun q : Fin (k + 1) ↦ factorModule d q.succ.succ))

/-- The first factor of the tail word is the second factor of the full word. -/
def tailHeadFactorEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (tailDegreeProfile d) 0 = factorModule d 1 :=
  tailFactorModule d 0

def tailRemainderFactorFamilyEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (tailDegreeProfile (tailDegreeProfile d)) =
      fun q : Fin (k + 1) ↦ factorModule d q.succ.succ := by
  funext q
  exact (tailFactorModule (tailDegreeProfile d) q).trans
    (tailFactorModule d q.succ)

def tailRemainderModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (tailDegreeProfile (tailDegreeProfile d)) =
      headContractionRemainderModule d :=
  congrArg tensorModuleList
    (congrArg finFamilyList (tailRemainderFactorFamilyEq d))

/-- The first factor after contracting the head is the raw adjacent-composition target. -/
def contractZeroHeadFactorEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (d.contract 0) 0 = rawContractionFactor d 0 := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  calc
    factorModule (d.contract 0) 0 =
        factorModule (d.contract 0) (erasePosition w 0) := by
      congr 1
    _ = rawContractionFactor d 0 := by
      unfold factorModule rawContractionFactor
      rw [eraseIntermediate_arrowSource_at w 0,
        eraseIntermediate_arrowTarget_at w 0,
        contract_arrowDegree_at d 0]

/-- Every factor after a head contraction is the corresponding factor two places later. -/
def contractZeroTailFactorEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (q : Fin (k + 1)) :
    factorModule (tailDegreeProfile (d.contract 0)) q =
      factorModule d q.succ.succ := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  calc
    factorModule (tailDegreeProfile (d.contract 0)) q =
        factorModule (d.contract 0) q.succ := tailFactorModule (d.contract 0) q
    _ = factorModule d q.succ.succ := by
      have hafter : (0 : Fin (k + 2)) < eraseFactorIndex w 0 q.succ := by
        change 0 < q.val + 1
        omega
      have hindex : (eraseFactorIndex w 0 q.succ).succ = q.succ.succ := by
        apply Fin.ext
        rfl
      unfold factorModule
      rw [eraseIntermediate_arrowSource_of_after w 0 q.succ hafter,
        eraseIntermediate_arrowTarget_of_after w 0 q.succ hafter,
        contract_arrowDegree_of_after d 0 q.succ hafter,
        hindex]

def contractZeroRemainderModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (tailDegreeProfile (d.contract 0)) =
      headContractionRemainderModule d :=
  congrArg tensorModuleList
    (congrArg finFamilyList (funext (contractZeroTailFactorEq d)))

/-- The raw head merge composes the first two factors and leaves the remainder fixed. -/
theorem rawContractionAdjacentMergeData_zero_apply
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ)
    (r : headContractionRemainderModule d) :
    (rawContractionAdjacentMergeData d (0 : Fin (k + 2))).tensorMap.hom
        (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
      (adjacentFactorComposition d (0 : Fin (k + 2))).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] r := by
  let f : factorModule d (0 : Fin (k + 2)).castSucc ⊗
      factorModule d (0 : Fin (k + 2)).succ ⟶
        rawContractionFactor d (0 : Fin (k + 2)) :=
    adjacentFactorComposition d (0 : Fin (k + 2))
  change (@AdjacentMergeData.head
    (factorModule d (0 : Fin (k + 2)).castSucc)
    (factorModule d (0 : Fin (k + 2)).succ)
    (rawContractionFactor d (0 : Fin (k + 2)))
    (finFamilyList (fun q : Fin (k + 1) ↦ factorModule d q.succ.succ))
    f).tensorMap.hom (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
      f.hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] r
  change (f ⊗ₘ 𝟙 (headContractionRemainderModule d)).hom
      ((α_ (factorModule d (0 : Fin (k + 2)).castSucc)
        (factorModule d (0 : Fin (k + 2)).succ)
        (headContractionRemainderModule d)).inv.hom
          (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))) = _
  rw [ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]

/-- The actual head-contraction map is the raw merged tensor followed by target transport. -/
theorem contractionTensorMap_zero_apply_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ)
    (r : headContractionRemainderModule d) :
    (contractionTensorMap d (0 : Fin (k + 2))).hom
        (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
      (eqToHom (rawContractionTargetEq d (0 : Fin (k + 2))).symm).hom
        ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
          (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] r) := by
  rw [contractionTensorMap_raw_normal_form]
  simp only [ModuleCat.comp_apply]
  rw [rawContractionAdjacentMergeData_zero_apply]

def contractZeroCoordinateEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (d.contract 0) =
      rawContractionFactor d 0 ⊗ headContractionRemainderModule d :=
  (summandModule_succ (d.contract 0)).trans
    (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
      (contractZeroHeadFactorEq d) (contractZeroRemainderModuleEq d))

theorem rawContractionTargetEq_zero_eq_coordinates
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    rawContractionTargetEq d (0 : Fin (k + 2)) =
      contractZeroCoordinateEq d :=
  Subsingleton.elim _ _

def tailRawCoordinateEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (tailDegreeProfile d) =
      factorModule d 1 ⊗ headContractionRemainderModule d :=
  (summandModule_succ (tailDegreeProfile d)).trans
    (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
      (tailHeadFactorEq d) (tailRemainderModuleEq d))

/-- Tail-word evaluation on raw successor-factor coordinates. -/
theorem evaluateWord_tail_apply_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (y : factorModule d 1) (r : headContractionRemainderModule d) :
    E.evaluateWord (tailWord (Y := Y) intermediate) (tailDegreeProfile d)
        ((eqToHom (tailRawCoordinateEq d).symm).hom (y ⊗ₜ[ℤ] r)) =
      E.composeElement (intermediate 0).obj (intermediate 1).obj Y
        (-1 + (tailDegreeProfile d).arrowDegree 0)
        (tailDegree (tailDegreeProfile d)) (tailDegree d)
        (tailDegree_add_neg_one_add_head (tailDegreeProfile d))
        (E.firstContractionMap (tailDegreeProfile d)
          ((eqToHom (tailHeadFactorEq d).symm).hom y))
        (E.evaluateWord
          (tailWord (Y := Y) (fun q : Fin (k + 1) ↦ intermediate q.succ))
          (tailDegreeProfile (tailDegreeProfile d))
          ((eqToHom (tailRemainderModuleEq d).symm).hom r)) := by
  simpa [tailRawCoordinateEq, tailWord, tailDegree] using
    E.evaluateWord_succ_apply_tensor_of_coordinates
      (tailDegreeProfile d) (tailHeadFactorEq d)
      (tailRemainderModuleEq d) y r

/-- Evaluation of the head-contracted word on raw merged coordinates. -/
theorem evaluateWord_contract_zero_apply_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (z : rawContractionFactor d 0)
    (r : headContractionRemainderModule d) :
    E.evaluateWord
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) 0)
        (d.contract 0)
        ((eqToHom (contractZeroCoordinateEq d).symm).hom (z ⊗ₜ[ℤ] r)) =
      E.composeElement X (intermediate 1).obj Y
        (-1 + (d.contract 0).arrowDegree 0)
        (tailDegree (d.contract 0)) (n + 1)
        (tailDegree_add_neg_one_add_head (d.contract 0))
        (E.firstContractionMap (d.contract 0)
          ((eqToHom (contractZeroHeadFactorEq d).symm).hom z))
        (E.evaluateWord
          (tailWord (Y := Y)
            (eraseIntermediate
              ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
              0).intermediate)
          (tailDegreeProfile (d.contract 0))
          ((eqToHom (contractZeroRemainderModuleEq d).symm).hom r)) := by
  simpa [contractZeroCoordinateEq, eraseIntermediate, tailDegree] using
    E.evaluateWord_succ_apply_tensor_of_coordinates
      (d.contract 0) (contractZeroHeadFactorEq d)
      (contractZeroRemainderModuleEq d) z r

def headSecondFactorEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 1 =
      (dgHomZModuleCochainComplex (intermediate 0).obj (intermediate 1).obj).X
        (d.arrowDegree 1) :=
  (tailHeadFactorEq d).symm.trans (factorModule_zero_succ (tailDegreeProfile d))

def headCompositionSourceEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 ⊗ factorModule d 1 =
      (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) ⊗
        (dgHomZModuleCochainComplex (intermediate 0).obj (intermediate 1).obj).X
          (d.arrowDegree 1) :=
  congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
    (factorModule_zero_succ d) (headSecondFactorEq d)

def headFirstFactorDirectEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d (0 : Fin (k + 2)).castSucc =
      (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) := by
  have hzero : (0 : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  exact (congrArg (factorModule d) hzero).trans (factorModule_zero_succ d)

def headSecondFactorDirectEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d (0 : Fin (k + 2)).succ =
      (dgHomZModuleCochainComplex (intermediate 0).obj (intermediate 1).obj).X
        (d.arrowDegree 1) := by
  have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  exact (congrArg (factorModule d) hone).trans (headSecondFactorEq d)

def headCompositionSourceDirectEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d (0 : Fin (k + 2)).castSucc ⊗
        factorModule d (0 : Fin (k + 2)).succ =
      (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) ⊗
        (dgHomZModuleCochainComplex (intermediate 0).obj (intermediate 1).obj).X
          (d.arrowDegree 1) :=
  congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
    (headFirstFactorDirectEq d) (headSecondFactorDirectEq d)

def headCompositionTargetEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    rawContractionFactor d 0 =
      (dgHomZModuleCochainComplex X (intermediate 1).obj).X
        (d.arrowDegree 0 + d.arrowDegree 1) := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  have hs : w.arrowSource (0 : Fin (k + 2)).castSucc = X := by rfl
  have ht : w.arrowTarget (0 : Fin (k + 2)).succ = (intermediate 1).obj := by
    have hindex : (0 : Fin (k + 2)).succ = (1 : Fin (k + 2)).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    unfold arrowTarget vertex
    rw [Fin.cases_succ, Fin.lastCases_castSucc]
    rfl
  have hzero : (0 : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  unfold rawContractionFactor
  rw [hs, ht, hzero, hone]

def headCompositionTargetDirectEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    ((dgHomZModuleCochainComplex
      (({ length := k + 2, intermediate := intermediate } :
        DrinfeldWord X Y).arrowSource (0 : Fin (k + 2)).castSucc)
      (({ length := k + 2, intermediate := intermediate } :
        DrinfeldWord X Y).arrowTarget (0 : Fin (k + 2)).succ)).X
        (d.arrowDegree (0 : Fin (k + 2)).castSucc +
          d.arrowDegree (0 : Fin (k + 2)).succ)) =
      (dgHomZModuleCochainComplex X (intermediate 1).obj).X
        (d.arrowDegree 0 + d.arrowDegree 1) := by
  have h : rawContractionFactor d (0 : Fin (k + 2)) =
      ((dgHomZModuleCochainComplex
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowSource (0 : Fin (k + 2)).castSucc)
        (({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord X Y).arrowTarget (0 : Fin (k + 2)).succ)).X
          (d.arrowDegree (0 : Fin (k + 2)).castSucc +
            d.arrowDegree (0 : Fin (k + 2)).succ)) := rfl
  exact h.symm.trans (headCompositionTargetEq d)

/-- The raw head adjacent composition is the transported standard original composition. -/
theorem headAdjacentComposition_map
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    adjacentFactorComposition d (0 : Fin (k + 2)) ≫
        eqToHom (headCompositionTargetDirectEq d) =
      eqToHom (headCompositionSourceDirectEq d) ≫
        dgCochainCompTensorOfEq X (intermediate 0).obj
          (intermediate 0).obj (intermediate 1).obj rfl rfl := by
  let f := adjacentFactorComposition d (0 : Fin (k + 2))
  let g := dgCochainCompTensorOfEq X (intermediate 0).obj
    (intermediate 0).obj (intermediate 1).obj rfl
    (show d.arrowDegree 0 + d.arrowDegree 1 =
      d.arrowDegree 0 + d.arrowDegree 1 by rfl)
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  have hzero : (0 : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  have ht : w.arrowTarget (0 : Fin (k + 2)).succ = (intermediate 1).obj := by
    have hindex : (0 : Fin (k + 2)).succ = (1 : Fin (k + 2)).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    unfold arrowTarget vertex
    rw [Fin.cases_succ, Fin.lastCases_castSucc]
    rfl
  have hK : w.arrowSource (0 : Fin (k + 2)).castSucc = X := by
    rw [hzero]
    exact arrowSource_zero_eq_source w
  have hL : w.arrowTarget (0 : Fin (k + 2)).castSucc =
      (intermediate 0).obj := by
    unfold arrowTarget vertex
    rw [Fin.cases_succ, Fin.lastCases_castSucc]
    rfl
  have hL' : w.arrowSource (0 : Fin (k + 2)).succ =
      (intermediate 0).obj :=
    (arrowTarget_castSucc_eq_arrowSource_succ w 0).symm.trans hL
  have hp : d.arrowDegree (0 : Fin (k + 2)).castSucc = d.arrowDegree 0 :=
    congrArg d.arrowDegree hzero
  have hq : d.arrowDegree (0 : Fin (k + 2)).succ = d.arrowDegree 1 :=
    congrArg d.arrowDegree hone
  have hr : d.arrowDegree (0 : Fin (k + 2)).castSucc +
      d.arrowDegree (0 : Fin (k + 2)).succ =
        d.arrowDegree 0 + d.arrowDegree 1 := congrArg₂ (· + ·) hp hq
  have hfg : HEq f g := by
    unfold f g adjacentFactorComposition
    exact dgCochainCompTensorOfEq_heq hK hL hL' ht
      (arrowTarget_castSucc_eq_arrowSource_succ w 0) rfl
      hp hq hr rfl rfl
  have htransport := map_eq_transport_comp_of_heq
    (headCompositionSourceDirectEq d) (headCompositionTargetDirectEq d) f g hfg
  calc
    f ≫ eqToHom (headCompositionTargetDirectEq d) =
        (eqToHom (headCompositionSourceDirectEq d) ≫ g ≫
          eqToHom (headCompositionTargetDirectEq d).symm) ≫
            eqToHom (headCompositionTargetDirectEq d) := by rw [htransport]
    _ = eqToHom (headCompositionSourceDirectEq d) ≫ g := by simp

private theorem head_eqToHom_tensor_apply
    {M M' N N' : ModuleCat.{0} ℤ}
    (hM : M = M') (hN : N = N') (x : M) (y : N) :
    (eqToHom (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hM hN)).hom
        (x ⊗ₜ[ℤ] y) =
      (eqToHom hM).hom x ⊗ₜ[ℤ] (eqToHom hN).hom y := by
  subst M'
  subst N'
  rfl

/-- The normalized head composition applies the standard original cochain composition. -/
theorem headAdjacentComposition_apply
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    (eqToHom (headCompositionTargetDirectEq d)).hom
        ((adjacentFactorComposition d (0 : Fin (k + 2))).hom (x ⊗ₜ[ℤ] y)) =
      (dgCochainCompTensorOfEq X (intermediate 0).obj
        (intermediate 0).obj (intermediate 1).obj rfl rfl).hom
        ((eqToHom (headFirstFactorDirectEq d)).hom x ⊗ₜ[ℤ]
          (eqToHom (headSecondFactorDirectEq d)).hom y) := by
  have happ := ConcreteCategory.congr_hom (headAdjacentComposition_map d)
    (x ⊗ₜ[ℤ] y)
  simp only [ModuleCat.comp_apply] at happ
  have hsource : headCompositionSourceDirectEq d =
      congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
        (headFirstFactorDirectEq d) (headSecondFactorDirectEq d) :=
    Subsingleton.elim _ _
  rw [hsource, head_eqToHom_tensor_apply] at happ
  exact happ

/-- Applying the original enriched functor to the head composition gives target composition. -/
theorem factorMap_headAdjacentComposition
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    E.factorMap X (intermediate 1).obj (d.arrowDegree 0 + d.arrowDegree 1)
        ((eqToHom (headCompositionTargetDirectEq d)).hom
          ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
            (x ⊗ₜ[ℤ] y))) =
      E.composeElement X (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 0) (d.arrowDegree 1)
        (d.arrowDegree 0 + d.arrowDegree 1) (by omega)
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.factorMap (intermediate 0).obj (intermediate 1).obj
          (d.arrowDegree 1)
          ((eqToHom (headSecondFactorDirectEq d)).hom y)) := by
  rw [headAdjacentComposition_apply, E.factorMap_compose]

/-- The contracted head degree is the sum of the first two original arrow degrees. -/
def contractZeroHeadDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (d.contract 0).arrowDegree 0 = d.arrowDegree 0 + d.arrowDegree 1 := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  have hzero :
      (0 : Fin ((eraseIntermediate w 0).length + 1)) = erasePosition w 0 := by
    apply Fin.ext
    rfl
  have hleft : (0 : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  have hright : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  calc
    (d.contract 0).arrowDegree 0 =
        (d.contract 0).arrowDegree (erasePosition w 0) := by rw [← hzero]
    _ = d.arrowDegree (0 : Fin (k + 2)).castSucc +
        d.arrowDegree (0 : Fin (k + 2)).succ := contract_arrowDegree_at d 0
    _ = d.arrowDegree 0 + d.arrowDegree 1 := by rw [hleft, hright]

def contractZeroHeadIntermediateEq
    {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory) :
    intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1))) =
      intermediate 1 := by
  congr 1

def contractZeroOriginalHeadModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (dgHomZModuleCochainComplex X
      (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj).X
        ((d.contract 0).arrowDegree 0) =
      (dgHomZModuleCochainComplex X (intermediate 1).obj).X
        (d.arrowDegree 0 + d.arrowDegree 1) :=
  dgHomModuleTransportEq X X _ _ rfl
    (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate))
    (contractZeroHeadDegreeEq d)

def contractZeroTargetHeadModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (E.hom X
      (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj).X
        ((d.contract 0).arrowDegree 0) =
      (E.hom X (intermediate 1).obj).X
        (d.arrowDegree 0 + d.arrowDegree 1) :=
  targetHomModuleTransportEq E X X _ _ rfl
    (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate))
    (contractZeroHeadDegreeEq d)

/-- The first-factor map of the head-contracted word is the original functor applied to the
raw adjacent composition. -/
theorem firstFactorMap_contract_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (z : rawContractionFactor d 0) :
    (eqToHom (contractZeroTargetHeadModuleEq E d)).hom
        (E.firstFactorMap (d.contract 0)
          ((eqToHom (contractZeroHeadFactorEq d).symm).hom z)) =
      E.factorMap X (intermediate 1).obj
        (d.arrowDegree 0 + d.arrowDegree 1)
        ((eqToHom (headCompositionTargetEq d)).hom z) := by
  let B : CorrectedAcyclicComplexCategory :=
    intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))
  let hB : B.obj = (intermediate 1).obj :=
    congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate)
  let hdeg := contractZeroHeadDegreeEq d
  let hFactor := contractZeroHeadFactorEq d
  let hZero := factorModule_zero_succ (d.contract 0)
  have hcast := E.factorMap_transport X X B.obj (intermediate 1).obj
    rfl hB hdeg
    ((eqToHom hZero).hom ((eqToHom hFactor.symm).hom z))
  have hsourceProof :
      dgHomModuleTransportEq X X B.obj (intermediate 1).obj rfl hB hdeg =
        contractZeroOriginalHeadModuleEq d := Subsingleton.elim _ _
  have htargetProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 1).obj rfl hB hdeg =
        contractZeroTargetHeadModuleEq E d := Subsingleton.elim _ _
  rw [hsourceProof, htargetProof] at hcast
  have hx :
      (eqToHom (contractZeroOriginalHeadModuleEq d)).hom
          ((eqToHom hZero).hom ((eqToHom hFactor.symm).hom z)) =
        (eqToHom (headCompositionTargetEq d)).hom z := by
    change ((eqToHom hFactor.symm ≫ eqToHom hZero ≫
      eqToHom (contractZeroOriginalHeadModuleEq d)).hom z) = _
    simp only [eqToHom_trans]
  rw [hx] at hcast
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  exact hcast

/-- The full-word first-factor map on the exact raw head index. -/
theorem firstFactorMap_raw_head
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc) :
    E.firstFactorMap d
        ((eqToHom (congrArg (factorModule d)
          (show (0 : Fin (k + 2)).castSucc = (0 : Fin (k + 3)) by
            apply Fin.ext
            rfl))).hom x) =
      E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
        ((eqToHom (headFirstFactorDirectEq d)).hom x) := by
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  congr 1

/-- The tail-word first-factor map on the raw second full-word factor. -/
theorem firstFactorMap_raw_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    E.firstFactorMap (tailDegreeProfile d)
        ((eqToHom (tailHeadFactorEq d).symm).hom
          ((eqToHom (congrArg (factorModule d)
            (show (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) by
              apply Fin.ext
              rfl))).hom y)) =
      E.factorMap (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 1)
        ((eqToHom (headSecondFactorDirectEq d)).hom y) := by
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  congr 1
  let hindex : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  change ((eqToHom (congrArg (factorModule d) hindex) ≫
    eqToHom (tailHeadFactorEq d).symm ≫
    eqToHom (factorModule_zero_succ (tailDegreeProfile d))).hom y) =
      (eqToHom (headSecondFactorDirectEq d)).hom y
  simp only [eqToHom_trans]
  have htotal :
      ((congrArg (factorModule d) hindex).trans
        (tailHeadFactorEq d).symm).trans
          (factorModule_zero_succ (tailDegreeProfile d)) =
        headSecondFactorDirectEq d := Subsingleton.elim _ _
  rw [htotal]
  congr 1

/-- Head composition in the degree order used by target associativity. -/
theorem factorMap_headAdjacentComposition_assoc
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 1).obj).X q)
      (add_comm (d.arrowDegree 0) (d.arrowDegree 1)))).hom
        (E.factorMap X (intermediate 1).obj
          (d.arrowDegree 0 + d.arrowDegree 1)
          ((eqToHom (headCompositionTargetDirectEq d)).hom
            ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
              (x ⊗ₜ[ℤ] y)))) =
      E.composeElement X (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 0) (d.arrowDegree 1)
        (d.arrowDegree 1 + d.arrowDegree 0) rfl
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.factorMap (intermediate 0).obj (intermediate 1).obj
          (d.arrowDegree 1)
          ((eqToHom (headSecondFactorDirectEq d)).hom y)) := by
  rw [factorMap_headAdjacentComposition]
  simpa using E.composeElement_cast_output X (intermediate 0).obj
    (intermediate 1).obj (d.arrowDegree 0) (d.arrowDegree 1)
    (d.arrowDegree 0 + d.arrowDegree 1)
    (d.arrowDegree 1 + d.arrowDegree 0) (by omega)
    (add_comm (d.arrowDegree 0) (d.arrowDegree 1))
    (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
      ((eqToHom (headFirstFactorDirectEq d)).hom x))
    (E.factorMap (intermediate 0).obj (intermediate 1).obj
      (d.arrowDegree 1)
      ((eqToHom (headSecondFactorDirectEq d)).hom y))

/-- The tail first-contraction map on the raw second full-word factor. -/
theorem firstContractionMap_raw_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    E.firstContractionMap (tailDegreeProfile d)
        ((eqToHom (tailHeadFactorEq d).symm).hom
          ((eqToHom (congrArg (factorModule d)
            (show (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) by
              apply Fin.ext
              rfl))).hom y)) =
      E.composeElement (intermediate 0).obj (intermediate 1).obj
        (intermediate 1).obj (d.arrowDegree 1) (-1)
        (-1 + d.arrowDegree 1) rfl
        (E.factorMap (intermediate 0).obj (intermediate 1).obj
          (d.arrowDegree 1) ((eqToHom (headSecondFactorDirectEq d)).hom y))
        (E.contraction (intermediate 1)) := by
  have hfirst := E.firstFactorMap_raw_tail d y
  unfold firstContractionMap composeFirstMap
  simp only [LinearMap.comp_apply]
  have happ := congrArg
    (fun z ↦ E.composeElement (intermediate 0).obj (intermediate 1).obj
      (intermediate 1).obj (d.arrowDegree 1) (-1)
      (-1 + d.arrowDegree 1) rfl z (E.contraction (intermediate 1))) hfirst
  simpa using happ

/-- The first-contraction output degree after a head contraction, in associative order. -/
def contractZeroFirstContractionDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    -1 + (d.contract 0).arrowDegree 0 =
      -1 + d.arrowDegree 1 + d.arrowDegree 0 := by
  rw [contractZeroHeadDegreeEq d]
  omega

def contractZeroFirstContractionTargetEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (E.hom X
      (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj).X
        (-1 + (d.contract 0).arrowDegree 0) =
      (E.hom X (intermediate 1).obj).X
        (-1 + d.arrowDegree 1 + d.arrowDegree 0) :=
  targetHomModuleTransportEq E X X _ _ rfl
    (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate))
    (contractZeroFirstContractionDegreeEq d)

/-- The first-factor map of the contracted word, transported directly to associative degree
order, is target composition of the two original factor images. -/
theorem firstFactorMap_contract_zero_assoc
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    (eqToHom (targetHomModuleTransportEq E X X
      (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj
      (intermediate 1).obj rfl
      (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
        (contractZeroHeadIntermediateEq intermediate))
      ((contractZeroHeadDegreeEq d).trans
        (add_comm (d.arrowDegree 0) (d.arrowDegree 1))))).hom
        (E.firstFactorMap (d.contract 0)
          ((eqToHom (contractZeroHeadFactorEq d).symm).hom
            ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
              (x ⊗ₜ[ℤ] y)))) =
      E.composeElement X (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 0) (d.arrowDegree 1)
        (d.arrowDegree 1 + d.arrowDegree 0) rfl
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.factorMap (intermediate 0).obj (intermediate 1).obj
          (d.arrowDegree 1)
          ((eqToHom (headSecondFactorDirectEq d)).hom y)) := by
  let h01 := contractZeroTargetHeadModuleEq E d
  let hcast := congrArg (fun q ↦ (E.hom X (intermediate 1).obj).X q)
    (add_comm (d.arrowDegree 0) (d.arrowDegree 1))
  let h10 := targetHomModuleTransportEq E X X
    (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj
    (intermediate 1).obj rfl
    (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate))
    ((contractZeroHeadDegreeEq d).trans
      (add_comm (d.arrowDegree 0) (d.arrowDegree 1)))
  let z := (adjacentFactorComposition d (0 : Fin (k + 2))).hom (x ⊗ₜ[ℤ] y)
  have hfirst := E.firstFactorMap_contract_zero d z
  have hassoc := E.factorMap_headAdjacentComposition_assoc d x y
  have hproof : h10 = h01.trans hcast := Subsingleton.elim _ _
  have hcomp := ConcreteCategory.congr_hom (eqToHom_trans h01 hcast)
    (E.firstFactorMap (d.contract 0)
      ((eqToHom (contractZeroHeadFactorEq d).symm).hom z))
  simp only [ModuleCat.comp_apply] at hcomp
  have hcastFirst := congrArg (fun q ↦ (eqToHom hcast).hom q) hfirst
  change (eqToHom h10).hom
      (E.firstFactorMap (d.contract 0)
        ((eqToHom (contractZeroHeadFactorEq d).symm).hom z)) = _
  rw [hproof]
  exact hcomp.symm.trans (hcastFirst.trans hassoc)

set_option maxHeartbeats 4000000 in
-- Reassociating the transported head contraction maps produces a large normalization goal.
/-- The first contraction of the head-contracted word reassociates to the original head
factor followed by the tail first contraction. -/
theorem firstContractionMap_contract_zero_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ) :
    (eqToHom (contractZeroFirstContractionTargetEq E d)).hom
        (E.firstContractionMap (d.contract 0)
          ((eqToHom (contractZeroHeadFactorEq d).symm).hom
            ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
              (x ⊗ₜ[ℤ] y)))) =
      E.composeElement X (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 0) (-1 + d.arrowDegree 1)
        (-1 + d.arrowDegree 1 + d.arrowDegree 0) rfl
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.firstContractionMap (tailDegreeProfile d)
          ((eqToHom (tailHeadFactorEq d).symm).hom
            ((eqToHom (congrArg (factorModule d)
              (show (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) by
                apply Fin.ext
                rfl))).hom y))) := by
  let B : CorrectedAcyclicComplexCategory :=
    intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))
  let hB : B = intermediate 1 := contractZeroHeadIntermediateEq intermediate
  let hObj := congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj) hB
  let hp := (contractZeroHeadDegreeEq d).trans
    (add_comm (d.arrowDegree 0) (d.arrowDegree 1))
  let hout := contractZeroFirstContractionDegreeEq d
  have hcompose := E.composeElement_transport
    X X B.obj (intermediate 1).obj B.obj (intermediate 1).obj
    rfl hObj hObj hp rfl hout rfl (by omega)
    (E.firstFactorMap (d.contract 0)
      ((eqToHom (contractZeroHeadFactorEq d).symm).hom
        ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
          (x ⊗ₜ[ℤ] y))))
    (E.contraction B)
  have hOutProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 1).obj rfl hObj hout =
        contractZeroFirstContractionTargetEq E d := Subsingleton.elim _ _
  rw [hOutProof] at hcompose
  have hfirst := E.firstFactorMap_contract_zero_assoc d x y
  have hcontr := E.contraction_transport hB
  rw [hfirst, hcontr] at hcompose
  unfold firstContractionMap composeFirstMap
  change (eqToHom (contractZeroFirstContractionTargetEq E d)).hom
      (E.composeElement X B.obj B.obj ((d.contract 0).arrowDegree 0) (-1)
        (-1 + (d.contract 0).arrowDegree 0) rfl
        (E.firstFactorMap (d.contract 0)
          ((eqToHom (contractZeroHeadFactorEq d).symm).hom
            ((adjacentFactorComposition d (0 : Fin (k + 2))).hom
              (x ⊗ₜ[ℤ] y)))) (E.contraction B)) = _
  have hnormalized := hcompose
  have hassoc := E.composeElement_assoc X (intermediate 0).obj
    (intermediate 1).obj (intermediate 1).obj
    (d.arrowDegree 0) (d.arrowDegree 1) (-1)
    (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
      ((eqToHom (headFirstFactorDirectEq d)).hom x))
    (E.factorMap (intermediate 0).obj (intermediate 1).obj
      (d.arrowDegree 1) ((eqToHom (headSecondFactorDirectEq d)).hom y))
    (E.contraction (intermediate 1))
  have hresult := hnormalized.trans hassoc
  have htailFactor := E.firstFactorMap_raw_tail d y
  have hinner := congrArg
    (fun z ↦ E.composeElement (intermediate 0).obj (intermediate 1).obj
      (intermediate 1).obj (d.arrowDegree 1) (-1)
      (-1 + d.arrowDegree 1) rfl z (E.contraction (intermediate 1)))
    htailFactor.symm
  have houter := congrArg
    (fun z ↦ E.composeElement X (intermediate 0).obj (intermediate 1).obj
      (d.arrowDegree 0) (-1 + d.arrowDegree 1)
      (-1 + d.arrowDegree 1 + d.arrowDegree 0) rfl
      (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
        ((eqToHom (headFirstFactorDirectEq d)).hom x)) z) hinner
  convert hresult.trans houter using 1
  all_goals rfl

/-- The tail degree of the head-contracted word is the degree of the tail of the original
tail word. -/
def contractZeroTailDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tailDegree (d.contract 0) = tailDegree (tailDegreeProfile d) := by
  unfold tailDegree
  rw [contractZeroHeadDegreeEq d, tailDegreeProfile_arrowDegree]
  have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  rw [hone]
  omega

/-- The arrow degrees of the remainder after a head contraction are the corresponding
arrow degrees two positions later in the original word. -/
theorem contractZeroTailArrowDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (q : Fin (k + 1)) :
    (tailDegreeProfile (d.contract 0)).arrowDegree q =
      (tailDegreeProfile (tailDegreeProfile d)).arrowDegree q := by
  simp only [tailDegreeProfile_arrowDegree]
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  have hafter : (0 : Fin (k + 2)) < eraseFactorIndex w 0 q.succ := by
    change 0 < q.val + 1
    omega
  have hindex : (eraseFactorIndex w 0 q.succ).succ = q.succ.succ := by
    apply Fin.ext
    rfl
  rw [contract_arrowDegree_of_after d 0 q.succ hafter, hindex]

/-- Output transport for evaluation of the remainder after contracting the head. -/
def contractZeroRemainderTargetEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (E.hom
      (intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))).obj Y).X
        (tailDegree (d.contract 0)) =
      (E.hom (intermediate 1).obj Y).X
        (tailDegree (tailDegreeProfile d)) :=
  targetHomModuleTransportEq E _ _ Y Y
    (congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
      (contractZeroHeadIntermediateEq intermediate)) rfl
    (contractZeroTailDegreeEq d)

set_option maxHeartbeats 4000000 in
-- Comparing the recursively evaluated remainder requires normalizing all canonical transports.
/-- Evaluation of the remainder after a head contraction is the evaluation of the tail of the
original tail word, after canonical word, profile, input, and output transport. -/
theorem evaluateWord_contract_zero_remainder
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (r : headContractionRemainderModule d) :
    (eqToHom (contractZeroRemainderTargetEq E d)).hom
        (E.evaluateWord
          (tailWord (Y := Y)
            (eraseIntermediate
              ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
              0).intermediate)
          (tailDegreeProfile (d.contract 0))
          ((eqToHom (contractZeroRemainderModuleEq d).symm).hom r)) =
      E.evaluateWord
        (tailWord (Y := Y) (fun q : Fin (k + 1) ↦ intermediate q.succ))
        (tailDegreeProfile (tailDegreeProfile d))
        ((eqToHom (tailRemainderModuleEq d).symm).hom r) := by
  let B : CorrectedAcyclicComplexCategory :=
    intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))
  have hB : B = intermediate 1 := contractZeroHeadIntermediateEq intermediate
  subst B
  let wSource : DrinfeldWord (intermediate 1).obj Y :=
    tailWord (Y := Y)
      (eraseIntermediate
        ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
        0).intermediate
  let wTarget : DrinfeldWord (intermediate 1).obj Y :=
    tailWord (Y := Y) (fun q : Fin (k + 1) ↦ intermediate q.succ)
  have hword : wSource = wTarget := by
    rfl
  let hdeg := contractZeroTailDegreeEq d
  let dSource := tailDegreeProfile (d.contract 0)
  let dTransport := dSource.transport hword hdeg
  have hwordRefl : hword = rfl := Subsingleton.elim _ _
  have hprofile : dTransport = tailDegreeProfile (tailDegreeProfile d) := by
    apply DegreeProfile.ext
    funext q
    dsimp only [dTransport, dSource]
    rw [hwordRefl]
    simpa only [DegreeProfile.transport_arrowDegree, Fin.cast_eq_self] using
      contractZeroTailArrowDegreeEq d q
  let xSource := (eqToHom (contractZeroRemainderModuleEq d).symm).hom r
  have htransport := E.evaluateWord_transport_apply hword hdeg dSource xSource
  have hprofileEval := E.evaluateWord_profile_eq_apply hprofile
    ((eqToHom (summandModuleTransportEq hword hdeg dSource)).hom xSource)
  have hinput :
      (eqToHom (congrArg summandModule hprofile)).hom
          ((eqToHom (summandModuleTransportEq hword hdeg dSource)).hom xSource) =
        (eqToHom (tailRemainderModuleEq d).symm).hom r := by
    change ((eqToHom (contractZeroRemainderModuleEq d).symm ≫
      eqToHom (summandModuleTransportEq hword hdeg dSource) ≫
      eqToHom (congrArg summandModule hprofile)).hom r) =
        (eqToHom (tailRemainderModuleEq d).symm).hom r
    simp only [eqToHom_trans]
  rw [hinput] at hprofileEval
  have hresult := htransport.symm.trans hprofileEval.symm
  convert hresult using 1
  · dsimp only [wSource, dSource, xSource]
    congr 1
  · rfl

/-- The normalized head-contraction and remainder degrees add to the full differential target. -/
def contractZeroEvaluationDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tailDegree (tailDegreeProfile d) +
        (-1 + d.arrowDegree 1 + d.arrowDegree 0) = n + 1 := by
  have htail := tailDegree_add_neg_one_add_head (tailDegreeProfile d)
  have hfull := headContractionOutputDegreeEq d
  have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
    apply Fin.ext
    rfl
  have hhead : (tailDegreeProfile d).arrowDegree 0 = d.arrowDegree 1 := by
    rw [tailDegreeProfile_arrowDegree, hone]
  rw [hhead] at htail
  omega

set_option maxHeartbeats 4000000 in
-- The raw head-contraction formula combines the preceding transport and associativity proofs.
/-- Evaluation of a raw pure tensor after contracting the head is the original first-factor
image composed with evaluation of the raw tail tensor. -/
theorem evaluateWord_head_contraction_apply_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d (0 : Fin (k + 2)).castSucc)
    (y : factorModule d (0 : Fin (k + 2)).succ)
    (r : headContractionRemainderModule d) :
    E.evaluateWord
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) 0)
        (d.contract 0)
        ((contractionTensorMap d (0 : Fin (k + 2))).hom
          (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))) =
      E.composeElement X (intermediate 0).obj Y
        (d.arrowDegree 0) (tailDegree d) (n + 1)
        (headContractionOutputDegreeEq d)
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.evaluateWord (tailWord (Y := Y) intermediate) (tailDegreeProfile d)
          ((eqToHom (tailRawCoordinateEq d).symm).hom (y ⊗ₜ[ℤ] r))) := by
  rw [contractionTensorMap_zero_apply_raw]
  have hcoordinate :
      (rawContractionTargetEq d (0 : Fin (k + 2))).symm =
        (contractZeroCoordinateEq d).symm :=
    congrArg Eq.symm (rawContractionTargetEq_zero_eq_coordinates d)
  have hcoordinateMap := congrArg eqToHom hcoordinate
  rw [hcoordinateMap]
  change E.evaluateWord
      (eraseIntermediate
        ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) 0)
      (d.contract 0)
      ((eqToHom (contractZeroCoordinateEq d).symm).hom
        (((adjacentFactorComposition d (0 : Fin (k + 2))).hom
          (x ⊗ₜ[ℤ] y)) ⊗ₜ[ℤ] r)) = _
  rw [E.evaluateWord_contract_zero_apply_raw]
  let B : CorrectedAcyclicComplexCategory :=
    intermediate ((0 : Fin (k + 2)).succAbove (0 : Fin (k + 1)))
  let hB : B = intermediate 1 := contractZeroHeadIntermediateEq intermediate
  let hObj := congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj) hB
  let hp := contractZeroFirstContractionDegreeEq d
  let hq := contractZeroTailDegreeEq d
  let z := (adjacentFactorComposition d (0 : Fin (k + 2))).hom (x ⊗ₜ[ℤ] y)
  let u := E.evaluateWord
    (tailWord (Y := Y)
      (eraseIntermediate
        ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
        0).intermediate)
    (tailDegreeProfile (d.contract 0))
    ((eqToHom (contractZeroRemainderModuleEq d).symm).hom r)
  have hcompose := E.composeElement_transport
    X X B.obj (intermediate 1).obj Y Y rfl hObj rfl hp hq rfl
    (tailDegree_add_neg_one_add_head (d.contract 0))
    (contractZeroEvaluationDegreeEq d)
    (E.firstContractionMap (d.contract 0)
      ((eqToHom (contractZeroHeadFactorEq d).symm).hom z)) u
  have hFirstProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 1).obj rfl hObj hp =
        contractZeroFirstContractionTargetEq E d := Subsingleton.elim _ _
  have hTailProof :
      targetHomModuleTransportEq E B.obj (intermediate 1).obj Y Y hObj rfl hq =
        contractZeroRemainderTargetEq E d := Subsingleton.elim _ _
  rw [hFirstProof, hTailProof] at hcompose
  simp only [eqToHom_refl, CategoryTheory.id_apply] at hcompose
  have hfirst := E.firstContractionMap_contract_zero_raw d x y
  have htail := E.evaluateWord_contract_zero_remainder d r
  have hfirstCompose := congrArg
    (fun v ↦ E.composeElement X (intermediate 1).obj Y
      (-1 + d.arrowDegree 1 + d.arrowDegree 0)
      (tailDegree (tailDegreeProfile d)) (n + 1)
      (contractZeroEvaluationDegreeEq d) v
      ((eqToHom (contractZeroRemainderTargetEq E d)).hom u)) hfirst
  have htailCompose := congrArg
    (fun v ↦ E.composeElement X (intermediate 1).obj Y
      (-1 + d.arrowDegree 1 + d.arrowDegree 0)
      (tailDegree (tailDegreeProfile d)) (n + 1)
      (contractZeroEvaluationDegreeEq d)
      (E.composeElement X (intermediate 0).obj (intermediate 1).obj
        (d.arrowDegree 0) (-1 + d.arrowDegree 1)
        (-1 + d.arrowDegree 1 + d.arrowDegree 0) rfl
        (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
          ((eqToHom (headFirstFactorDirectEq d)).hom x))
        (E.firstContractionMap (tailDegreeProfile d)
          ((eqToHom (tailHeadFactorEq d).symm).hom
            ((eqToHom (congrArg (factorModule d)
              (show (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) by
                apply Fin.ext
                rfl))).hom y)))) v) htail
  have hnormalized := hcompose.trans (hfirstCompose.trans htailCompose)
  let fx := E.factorMap X (intermediate 0).obj (d.arrowDegree 0)
    ((eqToHom (headFirstFactorDirectEq d)).hom x)
  let fy := E.firstContractionMap (tailDegreeProfile d)
    ((eqToHom (tailHeadFactorEq d).symm).hom y)
  let te := E.evaluateWord
    (tailWord (Y := Y) (fun q : Fin (k + 1) ↦ intermediate q.succ))
    (tailDegreeProfile (tailDegreeProfile d))
    ((eqToHom (tailRemainderModuleEq d).symm).hom r)
  have htailHead : (tailDegreeProfile d).arrowDegree 0 = d.arrowDegree 1 := by
    have hone : (0 : Fin (k + 2)).succ = (1 : Fin (k + 3)) := by
      apply Fin.ext
      rfl
    rw [tailDegreeProfile_arrowDegree, hone]
  have htailDegree :
      tailDegree (tailDegreeProfile d) + (-1 + d.arrowDegree 1) = tailDegree d := by
    have h := tailDegree_add_neg_one_add_head (tailDegreeProfile d)
    rw [htailHead] at h
    exact h
  have hassoc' := E.composeElement_assoc_of_degree_eq X (intermediate 0).obj
    (intermediate 1).obj Y
    (show (-1 + d.arrowDegree 1) + d.arrowDegree 0 =
      -1 + d.arrowDegree 1 + d.arrowDegree 0 by rfl)
    (contractZeroEvaluationDegreeEq d) htailDegree
    (headContractionOutputDegreeEq d) fx fy te
  have htailEval := E.evaluateWord_tail_apply_raw d y r
  have houter := congrArg
    (fun v ↦ E.composeElement X (intermediate 0).obj Y
      (d.arrowDegree 0) (tailDegree d) (n + 1)
      (headContractionOutputDegreeEq d) fx v) htailEval.symm
  have houter' :
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d) fx
          (E.composeElement (intermediate 0).obj (intermediate 1).obj Y
            (-1 + d.arrowDegree 1) (tailDegree (tailDegreeProfile d))
            (tailDegree d) htailDegree fy te) =
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d) fx
          (E.evaluateWord (tailWord (Y := Y) intermediate) (tailDegreeProfile d)
            ((eqToHom (tailRawCoordinateEq d).symm).hom (y ⊗ₜ[ℤ] r))) := by
    exact houter
  have hresult := hnormalized.trans (hassoc'.trans houter')
  convert hresult using 1
  all_goals rfl

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
