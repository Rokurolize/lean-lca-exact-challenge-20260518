/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationPositive

/-! # Differential normal forms for corrected Drinfeld word evaluation

This file identifies the head and tail internal differential maps in recursive positive-word
coordinates and proves that erasing a non-head intermediate object commutes with taking the tail.
-/

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

def tailRaiseZeroFactorFamilyEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (fun i : Fin (k + 1) ↦ factorModule d i.succ) =
      (fun i : Fin (k + 1) ↦ factorModule (d.raise 0) i.succ) := by
  funext i
  simp [factorModule, DegreeProfile.raise]

def tailRaiseZeroSummandModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule (tailDegreeProfile d) =
      summandModule (tailDegreeProfile (d.raise 0)) :=
  (congrArg summandModule (tailDegreeProfile_raise_zero d)).symm.trans
    (summandModule_castTotal_eq (tailDegree_raise_zero_eq d)
      (tailDegreeProfile (d.raise 0)))

/-- The non-head factors of the head internal differential are pure transports. -/
theorem tailInternalZeroTensorMap_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (TensorMapData.ofFn
      (fun i : Fin (k + 1) ↦ factorModule d i.succ)
      (fun i : Fin (k + 1) ↦ factorModule (d.raise 0) i.succ)
      (fun i ↦ factorDifferential d 0 i.succ)).tensorMap =
        eqToHom (congrArg tensorModuleList
          (congrArg finFamilyList (tailRaiseZeroFactorFamilyEq d))) := by
  apply tensorMapData_ofFn_eqToHom_of_family_eq _ _
    (tailRaiseZeroFactorFamilyEq d)
  intro i
  obtain ⟨hM, hmap⟩ := factorDifferential_eqToHom_of_ne
    d 0 i.succ (Fin.succ_ne_zero i).symm
  rw [hmap]

/-- After identifying successor factors with tail factors, the head-internal tail map is
transport. -/
theorem tailInternalZeroTransport_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail d).symm) ≫
      (TensorMapData.ofFn
        (fun i : Fin (k + 1) ↦ factorModule d i.succ)
        (fun i : Fin (k + 1) ↦ factorModule (d.raise 0) i.succ)
        (fun i ↦ factorDifferential d 0 i.succ)).tensorMap ≫
      eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail (d.raise 0))) =
      eqToHom (tailRaiseZeroSummandModuleEq d) := by
  rw [tailInternalZeroTensorMap_eq]
  simp only [eqToHom_trans]

/-- In raw successor-factor coordinates, the head-internal tail map is the same transport. -/
theorem tailInternalZeroRaw_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (TensorMapData.ofFn
      (fun i : Fin (k + 1) ↦ factorModule d i.succ)
      (fun i : Fin (k + 1) ↦ factorModule (d.raise 0) i.succ)
      (fun i ↦ factorDifferential d 0 i.succ)).tensorMap =
      eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail d)) ≫
      eqToHom (tailRaiseZeroSummandModuleEq d) ≫
      eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail (d.raise 0)).symm) := by
  rw [tailInternalZeroTensorMap_eq]
  simp only [eqToHom_trans]

/-- The positive-word coordinate transport acts only on the tail tensor factor. -/
theorem summandModule_succ_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (summandModule_succ d) =
      𝟙 (factorModule d 0) ⊗ₘ
        eqToHom (congrArg tensorModuleList
          (finFamilyList_factorModule_tail d)) := by
  let h := congrArg tensorModuleList
    (congrArg (factorModule d 0 :: ·) (finFamilyList_factorModule_tail d))
  rw [Subsingleton.elim (summandModule_succ d) h]
  exact tensorModuleList_eqToHom_cons
    (factorModule d 0) (finFamilyList_factorModule_tail d)

/-- Positive-word evaluation on canonical head/tail coordinates is recursive target composition. -/
theorem evaluateSucc_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (tailEval : summandModule (tailDegreeProfile d) →ₗ[ℤ]
      (E.hom (intermediate 0).obj Y).X (tailDegree d))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateSucc d tailEval
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d) n
        (tailDegree_add_neg_one_add_head d)
        (E.firstContractionMap d x) (tailEval t) := by
  unfold evaluateSucc
  simp only [LinearMap.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (summandModule_succ d)).inv_hom_id (x ⊗ₜ[ℤ] t)
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  have hcancel' :
      (ConcreteCategory.hom (eqToHom (summandModule_succ d)))
          ((ConcreteCategory.hom (eqToHom (summandModule_succ d).symm))
            (x ⊗ₜ[ℤ] t)) = x ⊗ₜ[ℤ] t := by
    simpa only [eqToIso.hom, eqToIso.inv] using hcancel
  change (TensorProduct.lift (E.evaluateSuccBilinear d tailEval))
      ((ConcreteCategory.hom (eqToHom (summandModule_succ d)))
        ((ConcreteCategory.hom (eqToHom (summandModule_succ d).symm))
          (x ⊗ₜ[ℤ] t))) = _
  rw [hcancel']
  rfl

/-- The inverse positive-word coordinate transport acts only on the tail tensor factor. -/
theorem summandModule_succ_symm_eqToHom
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (summandModule_succ d).symm =
      𝟙 (factorModule d 0) ⊗ₘ
        eqToHom (congrArg tensorModuleList
          (finFamilyList_factorModule_tail d).symm) := by
  let h := congrArg tensorModuleList
    (congrArg (factorModule d 0 :: ·) (finFamilyList_factorModule_tail d).symm)
  rw [Subsingleton.elim (summandModule_succ d).symm h]
  exact tensorModuleList_eqToHom_cons
    (factorModule d 0) (finFamilyList_factorModule_tail d).symm

set_option maxHeartbeats 4000000 in
-- Normalizing the head differential through the nested tensor transports needs extra budget.
/-- The head internal differential is the head factor differential tensored with tail transport. -/
theorem internalDifferentialTensorMap_zero_normal_form
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    internalDifferentialTensorMap d 0 =
      eqToHom (summandModule_succ d) ≫
        (factorDifferential d 0 0 ⊗ₘ
          eqToHom (tailRaiseZeroSummandModuleEq d)) ≫
        eqToHom (summandModule_succ (d.raise 0)).symm := by
  unfold internalDifferentialTensorMap
  simp only [TensorMapData.ofFn, TensorMapData.tensorMap]
  rw [summandModule_succ_eqToHom, summandModule_succ_symm_eqToHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [← tailInternalZeroRaw_eq]
  rfl

/-- Raising a tail factor identifies the resulting tail summand with the raised tail profile. -/
def tailRaiseSuccSummandModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    summandModule (tailDegreeProfile (d.raise i.succ)) =
      summandModule ((tailDegreeProfile d).raise i) :=
  (summandModule_castTotal_eq (tailDegree_raise_succ_eq d i)
      (tailDegreeProfile (d.raise i.succ))).symm.trans
    (congrArg summandModule (tailDegreeProfile_raise_succ d i))

/-- Tail factor differentials agree with successor-indexed differentials of the full word. -/
theorem factorDifferential_tail_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i q : Fin (k + 1)) :
    HEq (factorDifferential d i.succ q.succ)
      (factorDifferential (tailDegreeProfile d) i q) := by
  by_cases h : q = i
  · subst q
    unfold factorDifferential
    simp only [eq_self, ↓reduceDIte]
    apply dgHomDifferential_heq
    · exact (tailWord_arrowSource (X := X) (Y := Y)
        (intermediate := intermediate) i).symm
    · exact (tailWord_arrowTarget (X := X) (Y := Y)
        (intermediate := intermediate) i).symm
    · rfl
    · simp [DegreeProfile.raise]
  · have hs : q.succ ≠ i.succ := by
      intro hsi
      apply h
      apply Fin.ext
      have hv := congrArg (fun z : Fin (k + 2) ↦ z.val) hsi
      simp only [Fin.val_succ] at hv
      omega
    have hid := congr_arg_heq
      (fun M : ModuleCat.{0} ℤ ↦ 𝟙 M) (tailFactorModule d q).symm
    unfold factorModule at hid
    simpa [factorDifferential, h, hs] using hid

def tailRaiseSuccFactorFamilyEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (fun q : Fin (k + 1) ↦ factorModule (d.raise i.succ) q.succ) =
      factorModule ((tailDegreeProfile d).raise i) := by
  funext q
  unfold factorModule
  rw [tailWord_arrowSource, tailWord_arrowTarget]
  apply congrArg (fun m : ℤ ↦
    (dgHomZModuleCochainComplex
      (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowSource
        q.succ)
      (({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y).arrowTarget
        q.succ)).X m)
  simp [DegreeProfile.raise]

theorem tailInternalSuccTensorMap_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    HEq
      (TensorMapData.ofFn
        (fun q : Fin (k + 1) ↦ factorModule d q.succ)
        (fun q : Fin (k + 1) ↦ factorModule (d.raise i.succ) q.succ)
        (fun q ↦ factorDifferential d i.succ q.succ)).tensorMap
      (internalDifferentialTensorMap (tailDegreeProfile d) i) := by
  unfold internalDifferentialTensorMap
  apply TensorMapData.ofFn_tensorMap_heq_of_pointwise
  · exact funext fun q ↦ (tailFactorModule d q).symm
  · exact tailRaiseSuccFactorFamilyEq d i
  · exact factorDifferential_tail_heq d i

/-- A map identified by HEq is the transported map between the original source and target. -/
theorem map_eq_transport_comp_of_heq
    {A A' B B' : ModuleCat.{0} ℤ}
    (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f g) :
    f = eqToHom hA ≫ g ≫ eqToHom hB.symm := by
  subst A'
  subst B'
  rw [eq_of_heq hfg]
  simp

/-- In successor-factor coordinates, a tail internal differential is the transported tail map. -/
theorem tailInternalSuccRaw_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (TensorMapData.ofFn
      (fun q : Fin (k + 1) ↦ factorModule d q.succ)
      (fun q : Fin (k + 1) ↦ factorModule (d.raise i.succ) q.succ)
      (fun q ↦ factorDifferential d i.succ q.succ)).tensorMap =
      eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail d)) ≫
      internalDifferentialTensorMap (tailDegreeProfile d) i ≫
      eqToHom (tailRaiseSuccSummandModuleEq d i).symm ≫
      eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_tail (d.raise i.succ)).symm) := by
  have hbase := map_eq_transport_comp_of_heq
    (congrArg tensorModuleList (finFamilyList_factorModule_tail d))
    (congrArg tensorModuleList
      (congrArg finFamilyList (tailRaiseSuccFactorFamilyEq d i)))
    _ _ (tailInternalSuccTensorMap_heq d i)
  rw [hbase]
  simp only [eqToHom_trans]

/-- Unfolding the internal tensor differential once separates the head and raw tail maps. -/
theorem internalDifferentialTensorMap_succ_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    internalDifferentialTensorMap d i.succ =
      factorDifferential d i.succ 0 ⊗ₘ
        (TensorMapData.ofFn
          (fun q : Fin (k + 1) ↦ factorModule d q.succ)
          (fun q : Fin (k + 1) ↦ factorModule (d.raise i.succ) q.succ)
          (fun q ↦ factorDifferential d i.succ q.succ)).tensorMap := by
  rfl

set_option maxHeartbeats 4000000 in
-- Reassociating a tail differential through every tensor coordinate needs extra budget.
/-- A tail internal differential is the corresponding tail-word differential with head transport. -/
theorem internalDifferentialTensorMap_succ_normal_form
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    internalDifferentialTensorMap d i.succ =
      eqToHom (summandModule_succ d) ≫
        (factorDifferential d i.succ 0 ⊗ₘ
          (internalDifferentialTensorMap (tailDegreeProfile d) i ≫
            eqToHom (tailRaiseSuccSummandModuleEq d i).symm)) ≫
        eqToHom (summandModule_succ (d.raise i.succ)).symm := by
  rw [internalDifferentialTensorMap_succ_raw,
    summandModule_succ_eqToHom, summandModule_succ_symm_eqToHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ factorDifferential d i.succ 0 ⊗ₘ f)
    (tailInternalSuccRaw_eq d i)

/-- Contracting after the head commutes with dropping the head degree. -/
theorem contractedArrowDegree_tail
    {k : ℕ} (a : Fin (k + 3) → ℤ) (i q : Fin (k + 1)) :
    contractedArrowDegree a i.succ q.succ =
      contractedArrowDegree (fun j ↦ a j.succ) i q := by
  unfold contractedArrowDegree
  have hi : i.succ.castSucc = i.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hi, Fin.succ_succAbove_succ]
  simp only [Fin.succ_inj]

/-- Erasing a non-head intermediate object commutes with passing to the tail word. -/
theorem tailWord_eraseIntermediate_succ
    {X Y : ComplexCategory} {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory)
    (i : Fin (k + 1)) :
    tailWord (Y := Y)
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          i.succ).intermediate =
      eraseIntermediate (tailWord (Y := Y) intermediate) i := by
  cases k with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact eq_nil_of_length_eq_zero _ rfl
  | succ k =>
      change
        ({ length := k + 1,
            intermediate := fun q ↦ intermediate (i.succ.succAbove q.succ) } :
          DrinfeldWord (intermediate 0).obj Y) =
        { length := k + 1,
          intermediate := fun q ↦ intermediate ((i.succAbove q).succ) }
      congr 1
      funext q
      rw [Fin.succ_succAbove_succ]

/-- A contraction after the head leaves the head arrow degree unchanged. -/
theorem contract_succ_arrowDegree_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (d.contract i.succ).arrowDegree 0 = d.arrowDegree 0 := by
  unfold DegreeProfile.contract contractedArrowDegree
  simp only [Fin.cast_zero]
  have hi0 : i.succ.castSucc ≠ 0 := by simp
  have h0i : (0 : Fin (k + 2)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  rw [Fin.succAbove_ne_zero_zero hi0]
  simp [h0i]

/-- The tail total degree after a non-head contraction is the contracted tail degree. -/
def tailDegree_contract_succ_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    n + 1 - (d.contract i.succ).arrowDegree 0 + 1 = tailDegree d + 1 := by
  rw [contract_succ_arrowDegree_zero]
  unfold tailDegree
  omega

/-- The tail profile after a non-head contraction, transported to the contracted tail word. -/
def tailContractedProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    DegreeProfile (eraseIntermediate (tailWord (Y := Y) intermediate) i)
      (tailDegree d + 1) :=
  DegreeProfile.transport
    (X := (intermediate 0).obj) (Y := Y)
    (tailWord_eraseIntermediate_succ (X := X) intermediate i)
    (tailDegree_contract_succ_eq d i)
    (tailDegreeProfile (d.contract i.succ))

/-- Contracting a tail position in the full word gives the contracted tail profile. -/
theorem tailContractedProfile_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    tailContractedProfile d i = (tailDegreeProfile d).contract i := by
  apply DegreeProfile.ext
  funext q
  simp only [tailContractedProfile, DegreeProfile.transport_arrowDegree,
    tailDegreeProfile_arrowDegree, DegreeProfile.contract]
  let q' : Fin (k + 1) :=
    Fin.cast (eraseIntermediate_length (tailWord (Y := Y) intermediate) i) q
  have hcast :
      Fin.cast
          (eraseIntermediate_length
            ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) i.succ)
          q'.succ = q'.succ := by
    apply Fin.ext
    rfl
  rw [hcast]
  change contractedArrowDegree d.arrowDegree i.succ q'.succ =
    contractedArrowDegree (fun j ↦ d.arrowDegree j.succ) i q'
  exact contractedArrowDegree_tail d.arrowDegree i q'

/-- The old-index contracted factor at the merge position is the raw composition target. -/
theorem contractedFactorAtOldIndex_self_eq_raw
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractedFactorAtOldIndex d i i = rawContractionFactor d i := by
  unfold contractedFactorAtOldIndex rawContractionFactor factorModule
  rw [uneraseFactorIndex_self, eraseIntermediate_arrowSource_at,
    eraseIntermediate_arrowTarget_at, contract_arrowDegree_at]

/-- The transported contraction merge is heterogeneously the raw adjacent composition. -/
theorem contractionMergeAtOldIndex_raw_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (contractionMergeAtOldIndex d i) (adjacentFactorComposition d i) := by
  unfold contractionMergeAtOldIndex contractFactorAtOldIndexIso
  exact comp_eqToHom_heq_left (adjacentFactorComposition d i)
    (contractedFactorAtOldIndex_self_eq_raw d i).symm

/-- Recursive adjacent-merge data respects target-factor transport. -/
theorem recursiveAdjacentMergeDataOfFn_congr_target
    {k : ℕ} (M : Fin (k + 1) → ModuleCat.{0} ℤ) (i : Fin k)
    {P P' : ModuleCat.{0} ℤ} (hP : P = P')
    {f : Quiver.Hom (M i.castSucc ⊗ M i.succ) P}
    {g : Quiver.Hom (M i.castSucc ⊗ M i.succ) P'} (hfg : HEq f g) :
    HEq (recursiveAdjacentMergeDataOfFn M i P f)
      (recursiveAdjacentMergeDataOfFn M i P' g) := by
  subst P'
  rw [eq_of_heq hfg]

/-- The recursive contraction merge is the raw recursive merge up to target transport. -/
theorem recursiveContractionAdjacentMergeData_raw_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (recursiveContractionAdjacentMergeData d i)
      (rawContractionAdjacentMergeData d i) := by
  unfold recursiveContractionAdjacentMergeData rawContractionAdjacentMergeData
  exact recursiveAdjacentMergeDataOfFn_congr_target (factorModule d) i
    (contractedFactorAtOldIndex_self_eq_raw d i)
    (contractionMergeAtOldIndex_raw_heq d i)

/-- The raw recursive merge target is the contracted summand after canonical transport. -/
def rawContractionTargetEq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    summandModule (d.contract i) =
      tensorModuleList (finFamilyList
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i))) := by
  let hP := contractedFactorAtOldIndex_self_eq_raw d i
  let hfamily : recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) = contractedFactorAtOldIndex d i :=
    funext (recursiveContractionMergedFactor_eq d i)
  let hraw : recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) =
      recursiveMergedFactor (factorModule d) i (rawContractionFactor d i) :=
    congrArg (recursiveMergedFactor (factorModule d) i) hP
  exact (congrArg tensorModuleList (contractedFactorsOldIndex_eq d i).symm).trans
    ((congrArg tensorModuleList (congrArg finFamilyList hfamily).symm).trans
      (congrArg tensorModuleList (congrArg finFamilyList hraw)))

/-- The recursive transported merge and raw merge induce heterogeneously equal tensor maps. -/
theorem recursiveContractionAdjacentMergeData_raw_tensorMap_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (recursiveContractionAdjacentMergeData d i).tensorMap
      (rawContractionAdjacentMergeData d i).tensorMap := by
  apply AdjacentMergeData.tensorMap_heq rfl
    (congrArg finFamilyList
      (congrArg (recursiveMergedFactor (factorModule d) i)
        (contractedFactorAtOldIndex_self_eq_raw d i)))
  exact recursiveContractionAdjacentMergeData_raw_heq d i

/-- The contraction tensor map is the raw recursive adjacent merge followed by target transport. -/
theorem contractionTensorMap_raw_normal_form
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    contractionTensorMap d i =
      (rawContractionAdjacentMergeData d i).tensorMap ≫
        eqToHom (rawContractionTargetEq d i).symm := by
  have hheq := (contractionTensorMap_recursive_heq d i).trans
    (recursiveContractionAdjacentMergeData_raw_tensorMap_heq d i)
  have h := map_eq_transport_comp_of_heq rfl (rawContractionTargetEq d i)
    (contractionTensorMap d i) (rawContractionAdjacentMergeData d i).tensorMap hheq
  simpa using h

/-- The raw merged tail family is the successor-indexed raw merged full family. -/
def rawContractionTailTargetFamilyEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    recursiveMergedFactor (factorModule (tailDegreeProfile d)) i
        (rawContractionFactor (tailDegreeProfile d) i) =
      fun q ↦ recursiveMergedFactor (factorModule d) i.succ
        (rawContractionFactor d i.succ) q.succ := by
  have hfactor : factorModule (tailDegreeProfile d) =
      fun q ↦ factorModule d q.succ := by
    funext q
    exact tailFactorModule d q
  have hraw : rawContractionFactor (tailDegreeProfile d) =
      fun q ↦ rawContractionFactor d q.succ := by
    funext q
    exact tailRawContractionFactor d q
  rw [hfactor, hraw]
  rfl

/-- The raw full contraction target is the head factor followed by the raw tail target. -/
def rawContractionTailTargetListEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    finFamilyList (recursiveMergedFactor (factorModule d) i.succ
        (rawContractionFactor d i.succ)) =
      factorModule d 0 ::
        finFamilyList (recursiveMergedFactor (factorModule (tailDegreeProfile d)) i
          (rawContractionFactor (tailDegreeProfile d) i)) := by
  change factorModule d 0 ::
      finFamilyList (fun q ↦ recursiveMergedFactor (factorModule d) i.succ
        (rawContractionFactor d i.succ) q.succ) = _
  exact congrArg (factorModule d 0 :: ·)
    (congrArg finFamilyList (rawContractionTailTargetFamilyEq d i).symm)

/-- The raw full contraction is the head identity tensored with the raw tail contraction. -/
theorem rawContractionTensorMap_succ_normal_form
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (rawContractionAdjacentMergeData d i.succ).tensorMap =
      eqToHom (summandModule_succ d) ≫
        (𝟙 (factorModule d 0) ⊗ₘ
          (rawContractionAdjacentMergeData (tailDegreeProfile d) i).tensorMap) ≫
        eqToHom (congrArg tensorModuleList
          (rawContractionTailTargetListEq d i)).symm := by
  have hsource : finFamilyList (factorModule d) =
      factorModule d 0 :: finFamilyList (factorModule (tailDegreeProfile d)) := by
    change factorModule d 0 ::
        finFamilyList (fun q ↦ factorModule d q.succ) = _
    exact congrArg (factorModule d 0 :: ·) (finFamilyList_factorModule_tail d)
  have hdata := rawContractionAdjacentMergeData_tail_heq d i
  have hmap := AdjacentMergeData.tensorMap_heq hsource
    (rawContractionTailTargetListEq d i) hdata
  have h := map_eq_transport_comp_of_heq
    (congrArg tensorModuleList hsource)
    (congrArg tensorModuleList (rawContractionTailTargetListEq d i))
    (rawContractionAdjacentMergeData d i.succ).tensorMap
    (@AdjacentMergeData.tail (factorModule d 0) _ _
      (rawContractionAdjacentMergeData (tailDegreeProfile d) i)).tensorMap hmap
  simpa only [AdjacentMergeData.tensorMap] using h

/-- A non-head contraction preserves the head factor module. -/
theorem contract_succ_factorModule_zero_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    factorModule (d.contract i.succ) 0 = factorModule d 0 := by
  let w : DrinfeldWord X Y := { length := k + 2, intermediate := intermediate }
  have hindex : eraseFactorIndex w i.succ 0 = 0 := rfl
  have hbefore : eraseFactorIndex w i.succ 0 < i.succ := by
    change 0 < i.val + 1
    omega
  have hcast : (eraseFactorIndex w i.succ 0).castSucc = 0 := by
    rw [hindex]
    rfl
  unfold factorModule
  rw [eraseIntermediate_arrowSource_of_before w i.succ 0 hbefore,
    eraseIntermediate_arrowTarget_of_before w i.succ 0 hbefore,
    contract_arrowDegree_of_before d i.succ 0 hbefore, hcast]

/-- The contracted full-word tail summand is the contracted original tail summand. -/
def tailContractSummandModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    summandModule (tailDegreeProfile (d.contract i.succ)) =
      summandModule ((tailDegreeProfile d).contract i) :=
  (summandModuleTransportEq
      (tailWord_eraseIntermediate_succ (X := X) intermediate i)
      (tailDegree_contract_succ_eq d i)
      (tailDegreeProfile (d.contract i.succ))).trans
    (congrArg summandModule (tailContractedProfile_eq d i))

/-- The contracted full-word summand is the preserved head factor tensored with the contracted
tail. -/
def contractSuccSummandModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    summandModule (d.contract i.succ) =
      factorModule d 0 ⊗ summandModule ((tailDegreeProfile d).contract i) :=
  (summandModule_succ (d.contract i.succ)).trans
    (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
      (contract_succ_factorModule_zero_eq d i)
      (tailContractSummandModuleEq d i))

/-- The contraction map and raw recursive merge are heterogeneously equal. -/
theorem contractionTensorMap_raw_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (contractionTensorMap d i)
      (rawContractionAdjacentMergeData d i).tensorMap :=
  (contractionTensorMap_recursive_heq d i).trans
    (recursiveContractionAdjacentMergeData_raw_tensorMap_heq d i)

/-- The raw non-head contraction is heterogeneously the head identity tensored with the raw tail. -/
theorem rawContractionTensorMap_succ_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    HEq (rawContractionAdjacentMergeData d i.succ).tensorMap
      (𝟙 (factorModule d 0) ⊗ₘ
        (rawContractionAdjacentMergeData (tailDegreeProfile d) i).tensorMap) := by
  have hsource : finFamilyList (factorModule d) =
      factorModule d 0 :: finFamilyList (factorModule (tailDegreeProfile d)) := by
    change factorModule d 0 ::
        finFamilyList (fun q ↦ factorModule d q.succ) = _
    exact congrArg (factorModule d 0 :: ·) (finFamilyList_factorModule_tail d)
  have hmap := AdjacentMergeData.tensorMap_heq hsource
    (rawContractionTailTargetListEq d i)
    (rawContractionAdjacentMergeData_tail_heq d i)
  simpa only [AdjacentMergeData.tensorMap] using hmap

/-- A non-head contraction is the head identity tensored with the tail contraction. -/
theorem contractionTensorMap_succ_heq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    HEq (contractionTensorMap d i.succ)
      (𝟙 (factorModule d 0) ⊗ₘ contractionTensorMap (tailDegreeProfile d) i) := by
  apply HEq.trans (contractionTensorMap_raw_heq d i.succ)
  apply HEq.trans (rawContractionTensorMap_succ_heq d i)
  apply tensorHom_heq rfl rfl rfl
    (rawContractionTargetEq (tailDegreeProfile d) i).symm
  · rfl
  · exact (contractionTensorMap_raw_heq (tailDegreeProfile d) i).symm

/-- A non-head contraction has the head/tail tensor normal form. -/
theorem contractionTensorMap_succ_normal_form
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    contractionTensorMap d i.succ =
      eqToHom (summandModule_succ d) ≫
        (𝟙 (factorModule d 0) ⊗ₘ contractionTensorMap (tailDegreeProfile d) i) ≫
        eqToHom (contractSuccSummandModuleEq d i).symm := by
  have h := map_eq_transport_comp_of_heq
    (summandModule_succ d) (contractSuccSummandModuleEq d i)
    (contractionTensorMap d i.succ)
    (𝟙 (factorModule d 0) ⊗ₘ contractionTensorMap (tailDegreeProfile d) i)
    (contractionTensorMap_succ_heq d i)
  exact h

/-- A tail contraction has the expected value on a head/tail pure tensor. -/
theorem contractionTensorMap_succ_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (contractionTensorMap d i.succ).hom
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      (eqToHom (contractSuccSummandModuleEq d i).symm).hom
        (x ⊗ₜ[ℤ] (contractionTensorMap (tailDegreeProfile d) i).hom t) := by
  rw [contractionTensorMap_succ_normal_form]
  simp only [ModuleCat.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (summandModule_succ d)).inv_hom_id (x ⊗ₜ[ℤ] t)
  have hcancel' :
      (eqToHom (summandModule_succ d)).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
        x ⊗ₜ[ℤ] t := by
    simpa only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
      CategoryTheory.id_apply] using hcancel
  rw [hcancel']
  rfl

@[reassoc]
private lemma ιTensorObj_tensorHom_eval
    {K₁ K₂ L₁ L₂ : QuotientDGCochain} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

/-- The original enriched functor sends homogeneous source composition to target composition. -/
theorem factorMap_compose
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : p + q = n)
    (x : (dgHomZModuleCochainComplex X Y).X p)
    (y : (dgHomZModuleCochainComplex Y Z).X q) :
    E.factorMap X Z n
        ((dgCochainCompTensorOfEq X Y Y Z rfl h).hom (x ⊗ₜ[ℤ] y)) =
      E.composeElement X Y Z p q n (by omega)
        (E.factorMap X Y p x) (E.factorMap Y Z q y) := by
  letI : EnrichedCategory QuotientDGCochain OriginalCoefficientDGCategory :=
    originalCoefficientDGEnrichedCategory
  let A := originalCoefficientDGEnrichedHom (Opposite.op Z) (Opposite.op Y)
  let B := originalCoefficientDGEnrichedHom (Opposite.op Y) (Opposite.op X)
  let C := originalCoefficientDGEnrichedHom (Opposite.op Z) (Opposite.op X)
  have hmap := congrArg (fun f : A ⊗ B ⟶ E.hom X Z ↦ f.f n)
    (E.functor.map_comp (Opposite.op Z) (Opposite.op Y) (Opposite.op X))
  have happ := ConcreteCategory.congr_hom hmap
    ((HomologicalComplex.ιTensorObj A B q p n (by omega)).hom
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x)))
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at happ
  dsimp only [A, B, C] at happ
  have hsource :
      ((OriginalCoefficientDGComposition X Y Z).f n).hom
          ((HomologicalComplex.ιTensorObj
            (originalCoefficientDGEnrichedHom (Opposite.op Z) (Opposite.op Y))
            (originalCoefficientDGEnrichedHom (Opposite.op Y) (Opposite.op X))
            q p n (by omega)).hom
            (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
              ULift.up (ULift.up x))) =
        ULift.up (ULift.up
          ((dgCochainCompTensorOfEq X Y Y Z rfl h).hom (x ⊗ₜ[ℤ] y))) := by
    change ((OriginalCoefficientDGComposition X Y Z).f n).hom
        ((HomologicalComplex.ιTensorObj
          (OriginalCoefficientCochainComplex Y Z)
          (OriginalCoefficientCochainComplex X Y) q p n (by omega)).hom
          (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
            ULift.up (ULift.up x))) = _
    rw [OriginalCoefficientDGComposition_f, ← ModuleCat.comp_apply,
      HomologicalComplex.ι_mapBifunctorDesc]
    change ULift.up (ULift.up
      ((dgCochainCompTensorReversed X Y Z (by omega)).hom (y ⊗ₜ[ℤ] x))) = _
    rw [dgCochainCompTensorReversed_tmul]
    rfl
  change ((E.functor.map (Opposite.op Z) (Opposite.op X)).f n).hom
      (((OriginalCoefficientDGComposition X Y Z).f n).hom _) = _ at happ
  have hι := ιTensorObj_tensorHom_eval
    (E.functor.map (Opposite.op Z) (Opposite.op Y))
    (E.functor.map (Opposite.op Y) (Opposite.op X))
    (show q + p = n by omega)
  have htensor :
      (ConcreteCategory.hom ((HomologicalComplex.tensorHom
        (E.functor.map (Opposite.op Z) (Opposite.op Y))
        (E.functor.map (Opposite.op Y) (Opposite.op X))).f n))
        ((ConcreteCategory.hom (HomologicalComplex.ιTensorObj
          (originalCoefficientDGEnrichedHom (Opposite.op Z) (Opposite.op Y))
          (originalCoefficientDGEnrichedHom (Opposite.op Y) (Opposite.op X))
          q p n (by omega)))
          (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
            ULift.up (ULift.up x))) =
        (ConcreteCategory.hom (HomologicalComplex.ιTensorObj
          (E.hom Y Z) (E.hom X Y) q p n (by omega)))
          ((ConcreteCategory.hom
              ((E.functor.map (Opposite.op Z) (Opposite.op Y)).f q)
              (ULift.up (ULift.up y))) ⊗ₜ[QuotientCoefficientRing]
            (ConcreteCategory.hom
              ((E.functor.map (Opposite.op Y) (Opposite.op X)).f p)
              (ULift.up (ULift.up x)))) := by
    have hιapp := ConcreteCategory.congr_hom hι
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x))
    simp only [ModuleCat.comp_apply] at hιapp
    have htmul :
        (ConcreteCategory.hom
          ((E.functor.map (Opposite.op Z) (Opposite.op Y)).f q ⊗ₘ
            (E.functor.map (Opposite.op Y) (Opposite.op X)).f p))
          (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
            ULift.up (ULift.up x)) =
          (ConcreteCategory.hom
              ((E.functor.map (Opposite.op Z) (Opposite.op Y)).f q)
              (ULift.up (ULift.up y))) ⊗ₜ[QuotientCoefficientRing]
            (ConcreteCategory.hom
              ((E.functor.map (Opposite.op Y) (Opposite.op X)).f p)
              (ULift.up (ULift.up x))) := by
      rfl
    rw [htmul] at hιapp
    exact hιapp
  rw [hsource] at happ
  change _ =
    (ConcreteCategory.hom
      ((eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f n))
      ((ConcreteCategory.hom ((HomologicalComplex.tensorHom
        (E.functor.map (Opposite.op Z) (Opposite.op Y))
        (E.functor.map (Opposite.op Y) (Opposite.op X))).f n))
        ((ConcreteCategory.hom (HomologicalComplex.ιTensorObj
          (originalCoefficientDGEnrichedHom (Opposite.op Z) (Opposite.op Y))
          (originalCoefficientDGEnrichedHom (Opposite.op Y) (Opposite.op X))
          q p n (by omega)))
          (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
            ULift.up (ULift.up x)))) at happ
  rw [htensor] at happ
  change E.factorMap X Z n
      ((dgCochainCompTensorOfEq X Y Y Z rfl h).hom (x ⊗ₜ[ℤ] y)) = _
  exact happ

/-- Homogeneous target composition is associative. -/
theorem composeElement_assoc
    (X Y Z W : ComplexCategory) (p q r : ℤ)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q)
    (z : (E.hom Z W).X r) :
    E.composeElement X Z W (q + p) r (r + q + p) (by omega)
        (E.composeElement X Y Z p q (q + p) rfl x y) z =
      E.composeElement X Y W p (r + q) (r + q + p) rfl x
        (E.composeElement Y Z W q r (r + q) rfl y z) := by
  let A := E.hom Z W
  let B := E.hom Y Z
  let C := E.hom X Y
  let AB := E.hom Y W
  let BC := E.hom X Z
  let T := E.hom X W
  let μAB := eComp QuotientDGCochain (E.obj W) (E.obj Z) (E.obj Y)
  let μBC := eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)
  let μL := eComp QuotientDGCochain (E.obj W) (E.obj Y) (E.obj X)
  let μR := eComp QuotientDGCochain (E.obj W) (E.obj Z) (E.obj X)
  let total := r + q + p
  have hassoc := congrArg (fun f : A ⊗ B ⊗ C ⟶ T ↦ f.f total)
    (e_assoc QuotientDGCochain (E.obj W) (E.obj Z) (E.obj Y) (E.obj X))
  have hpre := congrArg
    (fun f ↦ GradedObject.Monoidal.ιTensorObj₃ A.X B.X C.X
      r q p total (by omega) ≫ f) hassoc
  simp only [HomologicalComplex.comp_f] at hpre
  have hassociator :
      (α_ A B C).inv.f total =
        (GradedObject.Monoidal.associator A.X B.X C.X).inv total := rfl
  rw [hassociator,
    GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc] at hpre
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq A.X B.X C.X
      r q p total (by omega) (r + q) rfl,
    GradedObject.Monoidal.ιTensorObj₃_eq A.X B.X C.X
      r q p total (by omega) (q + p) rfl] at hpre
  have hwr : (μAB ▷ C).f total =
      (HomologicalComplex.tensorHom μAB (𝟙 C)).f total := rfl
  have hwl : (A ◁ μBC).f total =
      (HomologicalComplex.tensorHom (𝟙 A) μBC).f total := rfl
  rw [hwr, hwl] at hpre
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj A.X B.X) C.X
            (r + q) p total (by omega) ≫
          (HomologicalComplex.tensorHom μAB (𝟙 C)).f total =
        (μAB.f (r + q) ⊗ₘ 𝟙 (C.X p)) ≫
          GradedObject.Monoidal.ιTensorObj AB.X C.X
            (r + q) p total (by omega) := by
    change HomologicalComplex.ιTensorObj (A ⊗ B) C
        (r + q) p total (by omega) ≫
      (HomologicalComplex.tensorHom μAB (𝟙 C)).f total = _
    exact ιTensorObj_tensorHom_eval μAB (𝟙 C)
      (show (r + q) + p = total by omega)
  have houterR :
      GradedObject.Monoidal.ιTensorObj A.X
            (GradedObject.Monoidal.tensorObj B.X C.X)
            r (q + p) total (by omega) ≫
          (HomologicalComplex.tensorHom (𝟙 A) μBC).f total =
        (𝟙 (A.X r) ⊗ₘ μBC.f (q + p)) ≫
          GradedObject.Monoidal.ιTensorObj A.X BC.X
            r (q + p) total (by omega) := by
    change HomologicalComplex.ιTensorObj A (B ⊗ C)
        r (q + p) total (by omega) ≫
      (HomologicalComplex.tensorHom (𝟙 A) μBC).f total = _
    exact ιTensorObj_tensorHom_eval (𝟙 A) μBC
      (show r + (q + p) = total by omega)
  simp only [Category.assoc] at hpre
  have hleftRaw := congrArg
    (fun t ↦
      (α_ (A.X r) (B.X q) (C.X p)).inv ≫
        (GradedObject.Monoidal.ιTensorObj A.X B.X
          r q (r + q) rfl ▷ C.X p) ≫
        t ≫ μL.f total)
    houterL
  have hrightRaw := congrArg
    (fun t ↦
      (A.X r ◁ GradedObject.Monoidal.ιTensorObj B.X C.X
        q p (q + p) rfl) ≫
        t ≫ μR.f total)
    houterR
  simp only [Category.assoc] at hleftRaw hrightRaw
  have hnorm := hleftRaw.symm.trans (hpre.trans hrightRaw)
  let v : ↑(A.X r ⊗ B.X q ⊗ C.X p) :=
    z ⊗ₜ[QuotientCoefficientRing]
      (y ⊗ₜ[QuotientCoefficientRing] x)
  have happ := ConcreteCategory.congr_hom hnorm v
  dsimp only [v] at happ
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.associator_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at happ
  change E.composeElement X Y W p (r + q) total rfl x
      (E.composeElement Y Z W q r (r + q) rfl y z) =
    E.composeElement X Z W (q + p) r total (by omega)
      (E.composeElement X Y Z p q (q + p) rfl x y) z at happ
  exact happ.symm

/-- Homogeneous target composition remains associative after replacing displayed degree sums
by propositionally equal indices. -/
theorem composeElement_assoc_of_degree_eq
    (X Y Z W : ComplexCategory) {p q r s t n : ℤ}
    (hqp : q + p = s) (hrs : r + s = n)
    (hrq : r + q = t) (htp : t + p = n)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q)
    (z : (E.hom Z W).X r) :
    E.composeElement X Z W s r n hrs
        (E.composeElement X Y Z p q s hqp x y) z =
      E.composeElement X Y W p t n htp x
        (E.composeElement Y Z W q r t hrq y z) := by
  subst s
  subst t
  have hn : n = r + q + p := by omega
  cases hn
  exact E.composeElement_assoc X Y Z W p q r x y z

/-- The head internal differential has the expected value on a head/tail pure tensor. -/
theorem internalDifferentialTensorMap_zero_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (internalDifferentialTensorMap d 0).hom
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      (eqToHom (summandModule_succ (d.raise 0)).symm).hom
        ((factorDifferential d 0 0).hom x ⊗ₜ[ℤ]
          (eqToHom (tailRaiseZeroSummandModuleEq d)).hom t) := by
  rw [internalDifferentialTensorMap_zero_normal_form]
  simp only [ModuleCat.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (summandModule_succ d)).inv_hom_id (x ⊗ₜ[ℤ] t)
  have hcancel' :
      (eqToHom (summandModule_succ d)).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
        x ⊗ₜ[ℤ] t := by
    simpa only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
      CategoryTheory.id_apply] using hcancel
  rw [hcancel']
  rfl

/-- A tail internal differential has the expected value on a head/tail pure tensor. -/
theorem internalDifferentialTensorMap_succ_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (internalDifferentialTensorMap d i.succ).hom
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      (eqToHom (summandModule_succ (d.raise i.succ)).symm).hom
        ((factorDifferential d i.succ 0).hom x ⊗ₜ[ℤ]
          (eqToHom (tailRaiseSuccSummandModuleEq d i).symm).hom
            ((internalDifferentialTensorMap (tailDegreeProfile d) i).hom t)) := by
  rw [internalDifferentialTensorMap_succ_normal_form]
  simp only [ModuleCat.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (summandModule_succ d)).inv_hom_id (x ⊗ₜ[ℤ] t)
  have hcancel' :
      (eqToHom (summandModule_succ d)).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
        x ⊗ₜ[ℤ] t := by
    simpa only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
      CategoryTheory.id_apply] using hcancel
  rw [hcancel']
  rfl

/-- Raising a tail factor leaves the head degree unchanged. -/
def tailRaiseHeadDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (d.raise i.succ).arrowDegree 0 = d.arrowDegree 0 := by
  have hne : (0 : Fin (k + 2)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [DegreeProfile.raise, hne]

/-- The original-factor map is natural under transport of its homogeneous degree. -/
theorem factorMap_cast_degree
    (X Y : ComplexCategory) {p q : ℤ} (h : p = q)
    (x : (dgHomZModuleCochainComplex X Y).X p) :
    (eqToHom (congrArg (fun r ↦ (E.hom X Y).X r) h)).hom
        (E.factorMap X Y p x) =
      E.factorMap X Y q
        ((eqToHom (congrArg
          (fun r ↦ (dgHomZModuleCochainComplex X Y).X r) h)).hom x) := by
  subst q
  rfl

/-- The first-factor map is unchanged when a tail factor is raised. -/
theorem firstFactorMap_raise_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (tailRaiseHeadDegreeEq d i))).hom
        (E.firstFactorMap (d.raise i.succ)
          ((factorDifferential d i.succ 0).hom x)) =
      E.firstFactorMap d x := by
  have hne : i.succ ≠ (0 : Fin (k + 2)) := Fin.succ_ne_zero i
  obtain ⟨hM, hmap⟩ := factorDifferential_eqToHom_of_ne d i.succ 0 hne
  rw [hmap]
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  rw [E.factorMap_cast_degree X (intermediate 0).obj
    (tailRaiseHeadDegreeEq d i)]
  let hdegree := congrArg
    (fun q ↦ (dgHomZModuleCochainComplex X (intermediate 0).obj).X q)
    (tailRaiseHeadDegreeEq d i)
  have hsource : hM.trans
      ((factorModule_zero_succ (d.raise i.succ)).trans hdegree) =
        factorModule_zero_succ d := Subsingleton.elim _ _
  have hx :
      (eqToHom hdegree).hom
          ((eqToHom (factorModule_zero_succ (d.raise i.succ))).hom
            ((eqToHom hM).hom x)) =
        (eqToHom (factorModule_zero_succ d)).hom x := by
    change ((eqToHom hM ≫
      eqToHom (factorModule_zero_succ (d.raise i.succ)) ≫
      eqToHom hdegree).hom x) = _
    rw [eqToHom_trans, eqToHom_trans, hsource]
  rw [hx]

/-- Homogeneous target composition is natural under first-input and output-degree transport. -/
theorem composeElement_cast_first_output
    (X Y Z : ComplexCategory)
    {p p' q n n' : ℤ} (hp : p = p') (hn : n = n')
    (h : q + p = n) (h' : q + p' = n')
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (eqToHom (congrArg (fun r ↦ (E.hom X Z).X r) hn)).hom
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X Y Z p' q n' h'
        ((eqToHom (congrArg (fun r ↦ (E.hom X Y).X r) hp)).hom x) y := by
  subst p'
  subst n'
  rfl

/-- Homogeneous target composition is natural under second-input and output-degree transport. -/
theorem composeElement_cast_second_output
    (X Y Z : ComplexCategory)
    {p q q' n n' : ℤ} (hq : q = q') (hn : n = n')
    (h : q + p = n) (h' : q' + p = n')
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (eqToHom (congrArg (fun r ↦ (E.hom X Z).X r) hn)).hom
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X Y Z p q' n' h' x
        ((eqToHom (congrArg (fun r ↦ (E.hom Y Z).X r) hq)).hom y) := by
  subst q'
  subst n'
  rfl

/-- Homogeneous target composition is natural under both input-degree transports and an
output-degree transport. -/
theorem composeElement_cast_inputs_output
    (X Y Z : ComplexCategory)
    {p p' q q' n n' : ℤ} (hp : p = p') (hq : q = q') (hn : n = n')
    (h : q + p = n) (h' : q' + p' = n')
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (eqToHom (congrArg (fun r ↦ (E.hom X Z).X r) hn)).hom
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X Y Z p' q' n' h'
        ((eqToHom (congrArg (fun r ↦ (E.hom X Y).X r) hp)).hom x)
        ((eqToHom (congrArg (fun r ↦ (E.hom Y Z).X r) hq)).hom y) := by
  subst p'
  subst q'
  subst n'
  rfl

/-- Raising a tail factor leaves the contracted head degree unchanged. -/
def tailRaiseContractedHeadDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    -1 + (d.raise i.succ).arrowDegree 0 = -1 + d.arrowDegree 0 := by
  rw [tailRaiseHeadDegreeEq d i]

/-- The first contraction map is unchanged when a tail factor is raised. -/
theorem firstContractionMap_raise_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (tailRaiseContractedHeadDegreeEq d i))).hom
        (E.firstContractionMap (d.raise i.succ)
          ((factorDifferential d i.succ 0).hom x)) =
      E.firstContractionMap d x := by
  unfold firstContractionMap composeFirstMap
  change (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (tailRaiseContractedHeadDegreeEq d i))).hom
      (E.composeElement X (intermediate 0).obj (intermediate 0).obj
        ((d.raise i.succ).arrowDegree 0) (-1)
        (-1 + (d.raise i.succ).arrowDegree 0) rfl
        (E.firstFactorMap (d.raise i.succ)
          ((factorDifferential d i.succ 0).hom x))
        (E.contraction (intermediate 0))) =
    E.composeElement X (intermediate 0).obj (intermediate 0).obj
      (d.arrowDegree 0) (-1) (-1 + d.arrowDegree 0) rfl
      (E.firstFactorMap d x) (E.contraction (intermediate 0))
  rw [E.composeElement_cast_first_output X (intermediate 0).obj
    (intermediate 0).obj
    (tailRaiseHeadDegreeEq d i)
    (tailRaiseContractedHeadDegreeEq d i)]
  rw [E.firstFactorMap_raise_succ d i x]

/-- The head factor and the evaluated tail compose in degree one above the word. -/
def headContractionOutputDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tailDegree d + d.arrowDegree 0 = n + 1 := by
  unfold tailDegree
  omega

/-- Evaluation of an explicitly zero-length word is the nil-profile evaluator. -/
theorem evaluateWord_zeroLength_apply
    {X Y : ComplexCategory}
    (intermediate : Fin 0 → CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : summandModule d) :
    E.evaluateWord
        ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) d x =
      E.evaluateNilProfile X Y
        (d.castWord (eq_nil_of_length_eq_zero
          ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) rfl))
        ((summandModuleCastWordIso
          (eq_nil_of_length_eq_zero
            ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) rfl)
          d).hom.hom x) := by
  rfl

/-- Evaluation of any word proved to have length zero is the nil-profile evaluator. -/
theorem evaluateWord_length_zero_apply
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} (h : w.length = 0) {n : ℤ}
    (d : DegreeProfile w n) (x : summandModule d) :
    E.evaluateWord w d x =
      E.evaluateNilProfile X Y (d.castWord (eq_nil_of_length_eq_zero w h))
        ((summandModuleCastWordIso (eq_nil_of_length_eq_zero w h) d).hom.hom x) := by
  cases w with
  | mk k intermediate =>
      change k = 0 at h
      subst k
      exact E.evaluateWord_zeroLength_apply intermediate d x

/-- The tail of a one-letter word is the zero-length word. -/
def singletonTailWordEqNil
    (Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    tailWord (Y := Y) (fun _ : Fin 1 ↦ A) = nil A.obj Y :=
  eq_nil_of_length_eq_zero _ rfl

/-- The second arrow degree of a one-letter word is its tail degree. -/
theorem singleton_arrowDegree_one_eq_tailDegree
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    d.arrowDegree 1 = tailDegree d := by
  have hsum := singleton_arrowDegree_sum X Y A d
  unfold tailDegree
  omega

/-- The second factor of a one-letter word is the corresponding original Hom module. -/
def singletonFactorOneEqOriginal
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    factorModule d 1 =
      (dgHomZModuleCochainComplex A.obj Y).X (tailDegree d) := by
  have hsource : (singleton X Y A).arrowSource (1 : Fin 2) = A.obj := rfl
  have htarget : (singleton X Y A).arrowTarget (1 : Fin 2) = Y := by
    change (singleton X Y A).vertex (Fin.last 2) = Y
    exact vertex_last (singleton X Y A)
  unfold factorModule
  rw [hsource, htarget, singleton_arrowDegree_one_eq_tailDegree X Y A d]

/-- The second factor represented by a one-letter word's tail summand. -/
def singletonTailFactorElement
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (t : summandModule (tailDegreeProfile d)) : factorModule d 1 :=
  (eqToHom (tailFactorModule d 0)).hom
    ((ρ_ (factorModule (tailDegreeProfile d) 0)).hom t)

/-- The original homogeneous cochain represented by a one-letter word's tail summand. -/
def singletonTailOriginalElement
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (t : summandModule (tailDegreeProfile d)) :
    (dgHomZModuleCochainComplex A.obj Y).X (tailDegree d) :=
  (eqToHom (singletonFactorOneEqOriginal X Y A d)).hom
    (singletonTailFactorElement X Y A d t)

private theorem singletonSummandIsoTensor_eq_assoc_unitor
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    singletonSummandIsoTensor X Y A d =
      (α_ (factorModule d 0) (factorModule d 1)
        (𝟙_ (ModuleCat.{0} ℤ))).symm ≪≫
        ρ_ (factorModule d 0 ⊗ factorModule d 1) := by
  rfl

private theorem tensorModuleList_singleton_eqToHom
    {M N : ModuleCat.{0} ℤ} (h : M = N) :
    eqToHom (congrArg tensorModuleList
      (congrArg (fun Q : ModuleCat.{0} ℤ ↦ [Q]) h)) =
      eqToHom h ⊗ₘ 𝟙 (𝟙_ (ModuleCat.{0} ℤ)) := by
  subst h
  change 𝟙 (M ⊗ 𝟙_ (ModuleCat.{0} ℤ)) =
    𝟙 M ⊗ₘ 𝟙 (𝟙_ (ModuleCat.{0} ℤ))
  exact (MonoidalCategory.id_tensorHom_id M
    (𝟙_ (ModuleCat.{0} ℤ))).symm

set_option maxHeartbeats 2000000 in
-- Expanding the singleton tensor isomorphisms creates a large transport-normalization goal.
/-- Head/tail coordinates of a one-letter summand are its two original Hom factors. -/
theorem singletonSummandIsoTensor_apply_headTail
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (singletonSummandIsoTensor X Y A d).hom.hom
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t := by
  have hlist : (finFamilyList_factorModule_tail d).symm =
      congrArg (fun Q : ModuleCat.{0} ℤ ↦ [Q])
        (tailFactorModule d 0) := by
    apply Subsingleton.elim
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · have hzero : singletonTailFactorElement X Y A d 0 = 0 := by
      unfold singletonTailFactorElement
      rw [map_zero, map_zero]
    have htmul :
        x ⊗ₜ[ℤ] (0 : summandModule (tailDegreeProfile d)) = 0 :=
      TensorProduct.tmul_zero _ _
    rw [htmul, map_zero, map_zero, hzero, TensorProduct.tmul_zero]
  · intro y r
    let y' : factorModule d 1 :=
      (eqToHom (tailFactorModule d 0)).hom y
    have hsource :
        (eqToHom (summandModule_succ d).symm).hom
            (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
          x ⊗ₜ[ℤ] (y' ⊗ₜ[ℤ] r) := by
      have happ := ConcreteCategory.congr_hom
        (summandModule_succ_symm_eqToHom d)
        (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))
      rw [hlist,
        tensorModuleList_singleton_eqToHom (tailFactorModule d 0)] at happ
      calc
        (eqToHom (summandModule_succ d).symm).hom
            (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
          ((𝟙 (factorModule d 0) ⊗ₘ
            (eqToHom (tailFactorModule d 0) ⊗ₘ
              𝟙 (𝟙_ (ModuleCat.{0} ℤ)))).hom
                (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))) := happ
        _ = x ⊗ₜ[ℤ] (y' ⊗ₜ[ℤ] r) := by rfl
    rw [hsource]
    unfold singletonTailFactorElement
    rw [singletonSummandIsoTensor_eq_assoc_unitor]
    simp only [Iso.trans_hom, ModuleCat.comp_apply, Iso.symm_hom]
    change (ρ_ (factorModule d 0 ⊗ factorModule d 1)).hom.hom
        ((α_ (factorModule d 0) (factorModule d 1)
          (𝟙_ (ModuleCat.{0} ℤ))).inv.hom
            (x ⊗ₜ[ℤ] (y' ⊗ₜ[ℤ] r))) = _
    rw [ModuleCat.MonoidalCategory.associator_inv_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
      map_smul, TensorProduct.tmul_smul]
  · intro t₁ t₂ h₁ h₂
    have htailAdd :
        singletonTailFactorElement X Y A d (t₁ + t₂) =
          singletonTailFactorElement X Y A d t₁ +
            singletonTailFactorElement X Y A d t₂ := by
      unfold singletonTailFactorElement
      rw [map_add, map_add]
    calc
      (singletonSummandIsoTensor X Y A d).hom.hom
          ((eqToHom (summandModule_succ d).symm).hom
            (x ⊗ₜ[ℤ] (t₁ + t₂))) =
        (singletonSummandIsoTensor X Y A d).hom.hom
            ((eqToHom (summandModule_succ d).symm).hom
              (x ⊗ₜ[ℤ] t₁)) +
          (singletonSummandIsoTensor X Y A d).hom.hom
            ((eqToHom (summandModule_succ d).symm).hom
              (x ⊗ₜ[ℤ] t₂)) := by
                rw [TensorProduct.tmul_add, map_add, map_add]
      _ = x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t₁ +
          x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t₂ := by
            rw [h₁, h₂]
      _ = x ⊗ₜ[ℤ]
          (singletonTailFactorElement X Y A d t₁ +
            singletonTailFactorElement X Y A d t₂) := by
              rw [TensorProduct.tmul_add]
      _ = x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d (t₁ + t₂) := by
            rw [htailAdd]

/-- A one-letter contraction is adjacent composition in the original homogeneous Hom. -/
theorem singletonContraction_original_apply_headTail
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (singletonContractedSummandIsoOriginal X Y A d 0).hom.hom
        ((contractionTensorMap d 0).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      (singletonAdjacentTargetIsoOriginalDirect X Y A d 0).hom.hom
        ((adjacentFactorComposition d 0).hom
          (x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t)) := by
  rw [contractionTensorMap_singleton]
  unfold singletonContractionTensorMap
  simp only [Fin.cases_zero, ModuleCat.comp_apply]
  rw [singletonSummandIsoTensor_apply_headTail]
  rw [← singletonAdjacentTargetIsoOriginal_eq_direct]
  rfl

/-- The first singleton factor is the original Hom module from the source to the intermediate
object. -/
def singletonFirstFactorEq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    factorModule d i.castSucc =
      (dgHomZModuleCochainComplex X A.obj).X (d.arrowDegree 0) := by
  have hi : i = singletonIndex X Y A := Subsingleton.elim _ _
  subst i
  simpa using factorModule_zero_succ d

/-- The second singleton factor is the original Hom module from the intermediate object to the
target. -/
def singletonSecondFactorEq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    factorModule d i.succ =
      (dgHomZModuleCochainComplex A.obj Y).X (tailDegree d) := by
  have hi : i = singletonIndex X Y A := Subsingleton.elim _ _
  subst i
  simpa using singletonFactorOneEqOriginal X Y A d

/-- Source transport from the singleton factor modules to the two original Hom modules. -/
def singletonCompositionSourceEq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    factorModule d i.castSucc ⊗ factorModule d i.succ =
      (dgHomZModuleCochainComplex X A.obj).X (d.arrowDegree 0) ⊗
        (dgHomZModuleCochainComplex A.obj Y).X (tailDegree d) :=
  congrArg₂ (· ⊗ ·) (singletonFirstFactorEq X Y A d i)
    (singletonSecondFactorEq X Y A d i)

/-- Target transport from the raw singleton adjacent-composition degree to degree `n + 1`. -/
def singletonCompositionTargetEq
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    ((dgHomZModuleCochainComplex
      ((singleton X Y A).arrowSource i.castSucc)
      ((singleton X Y A).arrowTarget i.succ)).X
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) =
      (dgHomZModuleCochainComplex X Y).X (n + 1) := by
  have hi : i = singletonIndex X Y A := Subsingleton.elim _ _
  subst i
  have hs : (singleton X Y A).arrowSource
      (singletonIndex X Y A).castSucc = X := rfl
  have ht : (singleton X Y A).arrowTarget
      (singletonIndex X Y A).succ = Y :=
    vertex_last (singleton X Y A)
  rw [hs, ht]
  apply congrArg (fun q ↦ (dgHomZModuleCochainComplex X Y).X q)
  simpa using singleton_arrowDegree_sum X Y A d

private theorem eqToHom_tensor_apply
    {M M' N N' : ModuleCat.{0} ℤ}
    (hM : M = M') (hN : N = N') (x : M) (y : N) :
    (eqToHom (congrArg₂ (· ⊗ ·) hM hN)).hom (x ⊗ₜ[ℤ] y) =
      (eqToHom hM).hom x ⊗ₜ[ℤ] (eqToHom hN).hom y := by
  subst M'
  subst N'
  rfl

/-- The raw singleton adjacent composition is the transported standard original composition. -/
theorem singletonAdjacentComposition_map
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    adjacentFactorComposition d i ≫
        (singletonAdjacentTargetIsoOriginalDirect X Y A d i).hom =
      eqToHom (singletonCompositionSourceEq X Y A d i) ≫
        dgCochainCompTensorOfEq X A.obj A.obj Y rfl
          (show d.arrowDegree 0 + tailDegree d = n + 1 by
            simpa [add_comm] using headContractionOutputDegreeEq d) := by
  have hi : i = singletonIndex X Y A := Subsingleton.elim _ _
  subst i
  let f := adjacentFactorComposition d (singletonIndex X Y A)
  let g := dgCochainCompTensorOfEq X A.obj A.obj Y rfl
    (show d.arrowDegree 0 + tailDegree d = n + 1 by
      simpa [add_comm] using headContractionOutputDegreeEq d)
  have hfg : HEq f g := by
    unfold f g adjacentFactorComposition
    apply dgCochainCompTensorOfEq_heq
    · rfl
    · rfl
    · rfl
    · exact vertex_last (singleton X Y A)
    · rfl
    · simpa using singleton_arrowDegree_one_eq_tailDegree X Y A d
    · simpa using singleton_arrowDegree_sum X Y A d
  have hleft : HEq
      (f ≫ (singletonAdjacentTargetIsoOriginalDirect X Y A d
        (singletonIndex X Y A)).hom) f := by
    have h := CategoryTheory.comp_eqToHom_heq f
      (singletonCompositionTargetEq X Y A d (singletonIndex X Y A))
    unfold singletonAdjacentTargetIsoOriginalDirect
    exact h
  have hright : HEq
      (eqToHom (singletonCompositionSourceEq X Y A d
        (singletonIndex X Y A)) ≫ g) g :=
    CategoryTheory.eqToHom_comp_heq g
      (singletonCompositionSourceEq X Y A d (singletonIndex X Y A))
  exact eq_of_heq (hleft.trans (hfg.trans hright.symm))

/-- The normalized singleton composition is the standard original homogeneous composition. -/
theorem singletonAdjacentComposition_apply_headTail
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    (singletonAdjacentTargetIsoOriginalDirect X Y A d 0).hom.hom
        ((adjacentFactorComposition d 0).hom
          (x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t)) =
      (dgCochainCompTensorOfEq X A.obj A.obj Y rfl
        (show d.arrowDegree 0 + tailDegree d = n + 1 by
          simpa [add_comm] using headContractionOutputDegreeEq d)).hom
        ((eqToHom (factorModule_zero_succ d)).hom x ⊗ₜ[ℤ]
          singletonTailOriginalElement X Y A d t) := by
  have happ := ConcreteCategory.congr_hom
    (singletonAdjacentComposition_map X Y A d 0)
    (x ⊗ₜ[ℤ] singletonTailFactorElement X Y A d t)
  simp only [ModuleCat.comp_apply] at happ
  have hsource : singletonCompositionSourceEq X Y A d 0 =
      congrArg₂ (· ⊗ ·) (factorModule_zero_succ d)
        (singletonFactorOneEqOriginal X Y A d) := Subsingleton.elim _ _
  rw [hsource, eqToHom_tensor_apply] at happ
  exact happ

/-- The only factor of a zero-length word is its original homogeneous Hom module. -/
def zeroLengthFactorEq
    (X Y : ComplexCategory)
    (intermediate : Fin 0 → CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 = (dgHomZModuleCochainComplex X Y).X n := by
  have hsource :
      ({ length := 0, intermediate := intermediate } :
        DrinfeldWord X Y).arrowSource 0 = X := rfl
  have htarget :
      ({ length := 0, intermediate := intermediate } :
        DrinfeldWord X Y).arrowTarget 0 = Y := by
    exact vertex_last
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y)
  have hdegree : d.arrowDegree 0 = n := by
    have hd := d.totalDegree
    rw [Fin.sum_univ_succ] at hd
    simpa using hd
  unfold factorModule
  rw [hsource, htarget, hdegree]

/-- Casting a zero-length word to `nil` and applying the nil summand isomorphism is the direct
right-unitor identification of its unique factor. -/
theorem zeroLengthCastNilIso_hom
    (X Y : ComplexCategory)
    (intermediate : Fin 0 → CorrectedAcyclicComplexCategory)
    (h : ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) = nil X Y)
    {n : ℤ}
    (d : DegreeProfile
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (summandModuleCastWordIso h d).hom ≫
      (nilSummandIsoOriginal X Y (d.castWord h)).hom =
      (ρ_ (factorModule d 0)).hom ≫
        eqToHom (zeroLengthFactorEq X Y intermediate d) := by
  have hintermediate : intermediate = Fin.elim0 := Subsingleton.elim _ _
  subst intermediate
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  change (nilSummandIsoOriginal X Y d).hom =
    (ρ_ (factorModule d 0)).hom ≫
      eqToHom (zeroLengthFactorEq X Y Fin.elim0 d)
  unfold nilSummandIsoOriginal
  simp only [Iso.trans_hom, eqToIso.hom]

/-- The zero-length tail evaluator recovers the original second singleton factor. -/
theorem singletonTailNilOriginalElement
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (t : summandModule (tailDegreeProfile d)) :
    (nilSummandIsoOriginal A.obj Y
      ((tailDegreeProfile d).castWord (singletonTailWordEqNil Y A))).hom.hom
        ((summandModuleCastWordIso (singletonTailWordEqNil Y A)
          (tailDegreeProfile d)).hom.hom t) =
      singletonTailOriginalElement X Y A d t := by
  let intermediate : Fin 0 → CorrectedAcyclicComplexCategory :=
    fun i ↦ (fun _ : Fin 1 ↦ A) i.succ
  have hmap := zeroLengthCastNilIso_hom A.obj Y intermediate
    (singletonTailWordEqNil Y A) (tailDegreeProfile d)
  have happ := ConcreteCategory.congr_hom hmap t
  simp only [ModuleCat.comp_apply] at happ
  let hsecond : factorModule d (Fin.succ (0 : Fin 1)) =
      (dgHomZModuleCochainComplex A.obj Y).X (tailDegree d) := by
    simpa using singletonFactorOneEqOriginal X Y A d
  have hfactor : zeroLengthFactorEq A.obj Y intermediate (tailDegreeProfile d) =
      (tailFactorModule d 0).trans hsecond := Subsingleton.elim _ _
  have hvalue :
      (eqToHom (zeroLengthFactorEq A.obj Y intermediate
        (tailDegreeProfile d))).hom
          ((ρ_ (factorModule (tailDegreeProfile d) 0)).hom.hom t) =
        singletonTailOriginalElement X Y A d t := by
    rw [hfactor]
    unfold singletonTailOriginalElement singletonTailFactorElement
    have hcomp := ConcreteCategory.congr_hom
      (eqToHom_trans (tailFactorModule d 0) hsecond)
      ((ρ_ (factorModule (tailDegreeProfile d) 0)).hom.hom t)
    simp only [ModuleCat.comp_apply] at hcomp
    exact hcomp
  exact happ.trans hvalue

set_option maxHeartbeats 4000000 in
-- The singleton contraction calculation normalizes several nested transported tensor maps.
/-- Evaluating the contraction of a one-letter word composes its two factor images. -/
theorem evaluate_headContraction_singleton_apply_tensor
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord (eraseIntermediate (singleton X Y A) 0) (d.contract 0)
        ((contractionTensorMap d 0).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      E.composeElement X A.obj Y
        (d.arrowDegree 0) (tailDegree d) (n + 1)
        (headContractionOutputDegreeEq d)
        (E.firstFactorMap d x)
        (E.evaluateWord
          (tailWord (Y := Y) (fun _ : Fin 1 ↦ A)) (tailDegreeProfile d) t) := by
  rw [E.evaluateWord_length_zero_apply rfl,
    E.evaluateWord_length_zero_apply rfl]
  unfold evaluateNilProfile tailDegree
  simp only [LinearMap.coe_comp, Function.comp_apply]
  change E.factorMap X Y (n + 1)
      ((singletonContractedSummandIsoOriginal X Y A d 0).hom.hom
        ((contractionTensorMap d 0).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)))) = _
  rw [singletonContraction_original_apply_headTail,
    singletonAdjacentComposition_apply_headTail,
    E.factorMap_compose]
  have htail := singletonTailNilOriginalElement X Y A d t
  have htail' :
      (nilSummandIsoOriginal A.obj Y
        ((tailDegreeProfile d).castWord
          (eq_nil_of_length_eq_zero
            (tailWord (Y := Y) (fun _ : Fin 1 ↦ A)) rfl))).hom.hom
          ((summandModuleCastWordIso
            (eq_nil_of_length_eq_zero
              (tailWord (Y := Y) (fun _ : Fin 1 ↦ A)) rfl)
            (tailDegreeProfile d)).hom.hom t) =
        singletonTailOriginalElement X Y A d t := by
    simpa [singletonTailWordEqNil] using htail
  rw [htail']
  unfold firstFactorMap tailDegree
  rfl

/-- Word evaluation is natural under transport of both the word and total degree. -/
theorem evaluateWord_transport_apply
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n)
    (x : summandModule d) :
    E.evaluateWord v (d.transport hw hn)
        ((eqToHom (summandModuleTransportEq hw hn d)).hom x) =
      (eqToHom (congrArg (fun q ↦ (E.hom X Y).X q) hn)).hom
        (E.evaluateWord w d x) := by
  subst v
  subst m
  rfl

/-- Word evaluation is natural under a cast of the indexing word. -/
theorem evaluateWord_castWord_apply
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) (x : summandModule d) :
    E.evaluateWord v (d.castWord h)
        ((summandModuleCastWordIso h d).hom.hom x) =
      E.evaluateWord w d x := by
  subst v
  rfl

/-- Word evaluation is natural under equality of degree profiles. -/
theorem evaluateWord_profile_eq_apply
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    {d e : DegreeProfile w n} (h : d = e) (x : summandModule d) :
    E.evaluateWord w e ((eqToHom (congrArg summandModule h)).hom x) =
      E.evaluateWord w d x := by
  cases h
  rfl

/-- Word evaluation is natural under a cast of the total degree. -/
theorem evaluateWord_castTotal_apply
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (h : n = m) (d : DegreeProfile w n) (x : summandModule d) :
    E.evaluateWord w (d.castTotal h)
        ((eqToHom (summandModule_castTotal_eq h d).symm).hom x) =
      (eqToHom (congrArg (fun q ↦ (E.hom X Y).X q) h)).hom
        (E.evaluateWord w d x) := by
  cases h
  rfl

/-- Evaluating the tail after raising the head is the original tail evaluation after
transporting the output degree back. -/
theorem evaluateWord_tail_raise_zero
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (t : summandModule (tailDegreeProfile d)) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom (intermediate 0).obj Y).X q)
      (tailDegree_raise_zero_eq d))).hom
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile (d.raise 0))
          ((eqToHom (tailRaiseZeroSummandModuleEq d)).hom t)) =
      E.evaluateWord (tailWord (Y := Y) intermediate)
        (tailDegreeProfile d) t := by
  let hdeg := tailDegree_raise_zero_eq d
  let dRaised := tailDegreeProfile (d.raise 0)
  let dCast := dRaised.castTotal hdeg
  let hprofile : dCast = tailDegreeProfile d :=
    tailDegreeProfile_raise_zero d
  let xRaised := (eqToHom (tailRaiseZeroSummandModuleEq d)).hom t
  let xCast :=
    (eqToHom (summandModule_castTotal_eq hdeg dRaised).symm).hom xRaised
  have hcast := E.evaluateWord_castTotal_apply hdeg dRaised xRaised
  have hprofileEval := E.evaluateWord_profile_eq_apply hprofile xCast
  have hinput :
      (eqToHom (congrArg summandModule hprofile)).hom xCast = t := by
    change ((eqToHom (tailRaiseZeroSummandModuleEq d) ≫
      eqToHom (summandModule_castTotal_eq hdeg dRaised).symm ≫
      eqToHom (congrArg summandModule hprofile)).hom t) = t
    simp only [eqToHom_trans]
    have htotal :
        ((tailRaiseZeroSummandModuleEq d).trans
          (summandModule_castTotal_eq hdeg dRaised).symm).trans
            (congrArg summandModule hprofile) = rfl :=
      Subsingleton.elim _ _
    rw [htotal]
    rfl
  rw [hinput] at hprofileEval
  exact hcast.symm.trans hprofileEval.symm

/-- Evaluating the tail after raising a tail factor is the raised-tail evaluation after
transporting the output degree back. -/
theorem evaluateWord_tail_raise_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (u : summandModule ((tailDegreeProfile d).raise i)) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom (intermediate 0).obj Y).X q)
      (tailDegree_raise_succ_eq d i))).hom
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile (d.raise i.succ))
          ((eqToHom (tailRaiseSuccSummandModuleEq d i).symm).hom u)) =
      E.evaluateWord (tailWord (Y := Y) intermediate)
        ((tailDegreeProfile d).raise i) u := by
  let hdeg := tailDegree_raise_succ_eq d i
  let dRaised := tailDegreeProfile (d.raise i.succ)
  let dCast := dRaised.castTotal hdeg
  let hprofile : dCast = (tailDegreeProfile d).raise i :=
    tailDegreeProfile_raise_succ d i
  let xRaised :=
    (eqToHom (tailRaiseSuccSummandModuleEq d i).symm).hom u
  let xCast :=
    (eqToHom (summandModule_castTotal_eq hdeg dRaised).symm).hom xRaised
  have hcast := E.evaluateWord_castTotal_apply hdeg dRaised xRaised
  have hprofileEval := E.evaluateWord_profile_eq_apply hprofile xCast
  have hinput :
      (eqToHom (congrArg summandModule hprofile)).hom xCast = u := by
    change ((eqToHom (tailRaiseSuccSummandModuleEq d i).symm ≫
      eqToHom (summandModule_castTotal_eq hdeg dRaised).symm ≫
      eqToHom (congrArg summandModule hprofile)).hom u) = u
    simp only [eqToHom_trans]
    have htotal :
        (((tailRaiseSuccSummandModuleEq d i).symm.trans
          (summandModule_castTotal_eq hdeg dRaised).symm).trans
            (congrArg summandModule hprofile)) = rfl :=
      Subsingleton.elim _ _
    rw [htotal]
    rfl
  rw [hinput] at hprofileEval
  exact hcast.symm.trans hprofileEval.symm

/-- Evaluating the tail after a non-head contraction is the contracted-tail evaluation
after transporting the word, profile, and output degree. -/
theorem evaluateWord_tail_contract_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (u : summandModule ((tailDegreeProfile d).contract i)) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom (intermediate 0).obj Y).X q)
      (tailDegree_contract_succ_eq d i))).hom
        (E.evaluateWord
          (tailWord (Y := Y)
            (eraseIntermediate
              ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
              i.succ).intermediate)
          (tailDegreeProfile (d.contract i.succ))
          ((eqToHom (tailContractSummandModuleEq d i).symm).hom u)) =
      E.evaluateWord
        (eraseIntermediate (tailWord (Y := Y) intermediate) i)
        ((tailDegreeProfile d).contract i) u := by
  let hword := tailWord_eraseIntermediate_succ (X := X) (Y := Y) intermediate i
  let hdeg := tailDegree_contract_succ_eq d i
  let dSource := tailDegreeProfile (d.contract i.succ)
  let dTransport := dSource.transport hword hdeg
  let hprofile : dTransport = (tailDegreeProfile d).contract i :=
    tailContractedProfile_eq d i
  let xSource :=
    (eqToHom (tailContractSummandModuleEq d i).symm).hom u
  have htransport := E.evaluateWord_transport_apply hword hdeg dSource xSource
  have hprofileEval := E.evaluateWord_profile_eq_apply hprofile
    ((eqToHom (summandModuleTransportEq hword hdeg dSource)).hom xSource)
  have hinput :
      (eqToHom (congrArg summandModule hprofile)).hom
          ((eqToHom (summandModuleTransportEq hword hdeg dSource)).hom xSource) = u := by
    change ((eqToHom (tailContractSummandModuleEq d i).symm ≫
      eqToHom (summandModuleTransportEq hword hdeg dSource) ≫
      eqToHom (congrArg summandModule hprofile)).hom u) = u
    simp only [eqToHom_trans]
    have htotal :
        (((tailContractSummandModuleEq d i).symm.trans
          (summandModuleTransportEq hword hdeg dSource)).trans
            (congrArg summandModule hprofile)) = rfl :=
      Subsingleton.elim _ _
    rw [htotal]
    rfl
  rw [hinput] at hprofileEval
  exact htransport.symm.trans hprofileEval.symm

/-- A positive word evaluates by the recursive head/tail formula. -/
theorem evaluateWord_succ_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    E.evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d =
      E.evaluateSucc d
        (E.evaluateWord (tailWord (Y := Y) intermediate) (tailDegreeProfile d)) := by
  rfl

/-- Evaluation of all signed internal-differential terms from one homogeneous word. -/
def evaluateInternalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X (n + 1) :=
  ∑ i, d.internalSign i •
    (E.evaluateWord w (d.raise i)).comp (internalDifferentialTensorMap d i).hom

/-- Evaluation of all signed contraction terms from one homogeneous word. -/
def evaluateContractionDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X (n + 1) :=
  ∑ i, d.contractionSign i •
    (E.evaluateWord (eraseIntermediate w i) (d.contract i)).comp
      (contractionTensorMap d i).hom

/-- Evaluation of the complete Drinfeld differential from one homogeneous word. -/
def evaluateTotalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X (n + 1) :=
  E.evaluateInternalDifferential d + E.evaluateContractionDifferential d

/-- The target differential after evaluating one homogeneous word. -/
def differentialAfterEvaluate
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X (n + 1) :=
  ({ toFun := fun x ↦ ((E.hom X Y).d n (n + 1)) (E.evaluateWord w d x)
     map_zero' := by simp
     map_add' := by simp } :
    summandModule d →+ (E.hom X Y).X (n + 1)).toIntLinearMap

/-- The enriched composition Leibniz rule transported to any propositionally equal output degree. -/
theorem composeElement_d_of_output_eq
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : q + p = n)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    ((E.hom X Z).d n (n + 1))
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X Y Z p (q + 1) (n + 1) (by omega)
        x (((E.hom Y Z).d q (q + 1)) y) +
      q.negOnePow •
        E.composeElement X Y Z (p + 1) q (n + 1) (by omega)
          (((E.hom X Y).d p (p + 1)) x) y := by
  subst n
  simpa using E.composeElement_d X Y Z p q x y

/-- The target differential of a positive-word evaluation has the raw enriched Leibniz form. -/
theorem differentialAfterEvaluate_succ_raw
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.differentialAfterEvaluate d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
        (E.firstContractionMap d x)
        (((E.hom (intermediate 0).obj Y).d
          (tailDegree d) (tailDegree d + 1))
            (E.evaluateWord (tailWord (Y := Y) intermediate)
              (tailDegreeProfile d) t)) +
      (tailDegree d).negOnePow •
        E.composeElement X (intermediate 0).obj Y
          ((-1 + d.arrowDegree 0) + 1) (tailDegree d) (n + 1)
            (by have h := tailDegree_add_neg_one_add_head d; omega)
          (((E.hom X (intermediate 0).obj).d
            (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + 1))
              (E.firstContractionMap d x))
          (E.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t) := by
  change ((E.hom X Y).d n (n + 1))
      (E.evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) = _
  rw [E.evaluateWord_succ_eq d,
    E.evaluateSucc_apply_tensor]
  exact E.composeElement_d_of_output_eq X (intermediate 0).obj Y
    (-1 + d.arrowDegree 0) (tailDegree d) n
    (tailDegree_add_neg_one_add_head d)
    (E.firstContractionMap d x)
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile d) t)

/-- Evaluation of a nil word is the direct nil-profile evaluator. -/
theorem evaluateWord_nil_apply
    {X Y : ComplexCategory} {n : ℤ}
    (d : DegreeProfile (nil X Y) n) (x : summandModule d) :
    E.evaluateWord (nil X Y) d x = E.evaluateNilProfile X Y d x := by
  rw [E.evaluateWord_length_zero_apply rfl]
  have h : eq_nil_of_length_eq_zero (nil X Y) rfl = rfl :=
    Subsingleton.elim _ _
  rw [h]
  rfl

/-- Evaluation commutes with the differential on a zero-length word. -/
theorem evaluateWord_d_nil
    {X Y : ComplexCategory} {n : ℤ}
    (d : DegreeProfile (nil X Y) n) :
    E.differentialAfterEvaluate d = E.evaluateTotalDifferential d := by
  apply LinearMap.ext
  intro x
  unfold differentialAfterEvaluate evaluateTotalDifferential
    evaluateInternalDifferential evaluateContractionDifferential
  change ((E.hom X Y).d n (n + 1))
      (E.evaluateWord (nil X Y) d x) =
    (∑ i : Fin ((nil X Y).length + 1),
      d.internalSign i •
        E.evaluateWord (nil X Y) (d.raise i)
          ((internalDifferentialTensorMap d i).hom x)) +
    (∑ i : Fin (nil X Y).length,
      d.contractionSign i •
        E.evaluateWord (eraseIntermediate (nil X Y) i) (d.contract i)
          ((contractionTensorMap d i).hom x))
  rw [Fin.sum_univ_succ, nil_internalSign, one_smul]
  change ((E.hom X Y).d n (n + 1))
      (E.evaluateWord (nil X Y) d x) =
    (E.evaluateWord (nil X Y) (d.raise 0)
      ((internalDifferentialTensorMap d 0).hom x) +
      (∑ i : Fin 0,
        d.internalSign i.succ •
          E.evaluateWord (nil X Y) (d.raise i.succ)
            ((internalDifferentialTensorMap d i.succ).hom x))) +
    (∑ i : Fin 0,
      d.contractionSign i •
        E.evaluateWord (eraseIntermediate (nil X Y) i) (d.contract i)
          ((contractionTensorMap d i).hom x))
  have htail : (∑ i : Fin 0,
      d.internalSign i.succ •
        E.evaluateWord (nil X Y) (d.raise i.succ)
          ((internalDifferentialTensorMap d i.succ).hom x)) = 0 :=
    Finset.sum_empty
  have hcontraction : (∑ i : Fin 0,
      d.contractionSign i •
        E.evaluateWord (eraseIntermediate (nil X Y) i) (d.contract i)
          ((contractionTensorMap d i).hom x)) = 0 :=
    Finset.sum_empty
  rw [htail, hcontraction, add_zero, add_zero]
  rw [E.evaluateWord_nil_apply, E.evaluateWord_nil_apply]
  exact E.evaluateNilProfile_d X Y d x

end AnnihilatingEnrichedFunctorData

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
