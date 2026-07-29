/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationHeadContraction

/-! # Completion of corrected Drinfeld word differential compatibility -/

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

/-- The head contribution in the target Leibniz rule is the first-factor image minus the
raised-head contraction contribution. -/
theorem composeElement_firstContractionMap_d
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : (E.hom (intermediate 0).obj Y).X (tailDegree d)) :
    E.composeElement X (intermediate 0).obj Y
        ((-1 + d.arrowDegree 0) + 1) (tailDegree d) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        (((E.hom X (intermediate 0).obj).d
          (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + 1))
            (E.firstContractionMap d x)) t =
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d)
          (E.firstFactorMap d x) t -
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d)
          ((eqToHom (congrArg
            (fun q ↦ (E.hom X (intermediate 0).obj).X q)
            (raisedHeadContractDegreeEq d))).hom
              (E.firstContractionMap (d.raise 0)
                ((factorDifferential d 0 0).hom x))) t := by
  have hcast := E.composeElement_cast_first_output X (intermediate 0).obj Y
    (firstContractionDifferentialTargetEq d) rfl
    (by have h := tailDegree_add_neg_one_add_head d; omega)
    (headContractionOutputDegreeEq d)
    (((E.hom X (intermediate 0).obj).d
      (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + 1))
        (E.firstContractionMap d x)) t
  simp only [eqToHom_refl, CategoryTheory.id_apply] at hcast
  rw [E.firstContractionMap_d d x] at hcast
  change _ =
    (E.composeFirstMap X (intermediate 0).obj Y
      (d.arrowDegree 0) (tailDegree d) (n + 1)
      (headContractionOutputDegreeEq d) t)
      (E.firstFactorMap d x -
        (eqToHom (congrArg
          (fun q ↦ (E.hom X (intermediate 0).obj).X q)
          (raisedHeadContractDegreeEq d))).hom
            (E.firstContractionMap (d.raise 0)
              ((factorDifferential d 0 0).hom x))) at hcast
  rw [map_sub] at hcast
  exact hcast

/-- The signed internal differential of a positive word splits into its head term and the
unchanged head contraction composed with the signed tail internal differential. -/
theorem evaluateInternalDifferential_succ_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateInternalDifferential d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      d.internalSign 0 •
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d)
          ((eqToHom (congrArg
            (fun q ↦ (E.hom X (intermediate 0).obj).X q)
            (raisedHeadContractDegreeEq d))).hom
              (E.firstContractionMap (d.raise 0)
                ((factorDifferential d 0 0).hom x)))
          (E.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t) +
        E.composeElement X (intermediate 0).obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          (E.firstContractionMap d x)
          (E.evaluateInternalDifferential (tailDegreeProfile d) t) := by
  unfold evaluateInternalDifferential
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [Fin.sum_univ_succ]
  congr 1
  · exact congrArg (fun z ↦ d.internalSign 0 • z)
      (E.evaluateWord_head_internal_apply_tensor d x t)
  · change (∑ i : Fin (k + 1),
        d.internalSign i.succ •
          E.evaluateWord
            ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
            (d.raise i.succ)
            ((internalDifferentialTensorMap d i.succ).hom
              ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)))) = _
    change _ =
      (E.composeSecondMap X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        (E.firstContractionMap d x))
        (∑ i : Fin (k + 1),
          (tailDegreeProfile d).internalSign i •
            E.evaluateWord (tailWord (Y := Y) intermediate)
              ((tailDegreeProfile d).raise i)
              ((internalDifferentialTensorMap (tailDegreeProfile d) i).hom t))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, ← internalSign_succ_eq_tail d i]
    exact congrArg (fun z ↦ d.internalSign i.succ • z)
      (E.evaluateWord_tail_internal_apply_tensor d i x t)

set_option maxHeartbeats 4000000 in
-- Normalizing the nested head/tail summand transports is expensive.
private theorem headRawInput_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (y : factorModule d 1)
    (r : headContractionRemainderModule d) :
    (eqToHom (summandModule_succ d).symm).hom
        (x ⊗ₜ[ℤ]
          (eqToHom (tailRawCoordinateEq d).symm).hom (y ⊗ₜ[ℤ] r)) =
      x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r) := by
  let hTail := (tailRawCoordinateEq d).symm
  let hTensor := congrArg
    (fun T : ModuleCat.{0} ℤ ↦ factorModule d 0 ⊗ T) hTail
  let hOuter := (summandModule_succ d).symm
  have htensor :
      (eqToHom hTensor).hom (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r)) =
        x ⊗ₜ[ℤ] (eqToHom hTail).hom (y ⊗ₜ[ℤ] r) := by
    rw [tensor_obj_eqToHom]
    rfl
  have hcomp := ConcreteCategory.congr_hom
    (eqToHom_trans hTensor hOuter) (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))
  simp only [ModuleCat.comp_apply] at hcomp
  have htotal : hTensor.trans hOuter = rfl := Subsingleton.elim _ _
  rw [htotal] at hcomp
  rw [← htensor]
  change (eqToHom hOuter).hom
      ((eqToHom hTensor).hom (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))) =
    (ConcreteCategory.hom (𝟙 (summandModule d)))
      (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] r))
  exact hcomp

set_option maxHeartbeats 4000000 in
-- The proof normalizes two nested tensor-coordinate transports in the pure-tensor case.
/-- For every positive tail, evaluating the head contraction composes the original first-factor
image with evaluation of the entire tail. -/
theorem evaluateWord_head_contraction_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) 0)
        (d.contract 0)
        ((contractionTensorMap d 0).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      E.composeElement X (intermediate 0).obj Y
        (d.arrowDegree 0) (tailDegree d) (n + 1)
        (headContractionOutputDegreeEq d)
        (E.firstFactorMap d x)
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile d) t) := by
  let u := (eqToHom (tailRawCoordinateEq d)).hom t
  have ht : (eqToHom (tailRawCoordinateEq d).symm).hom u = t := by
    have hcancel := ConcreteCategory.congr_hom
      (eqToIso (tailRawCoordinateEq d)).hom_inv_id t
    simp only [ModuleCat.comp_apply, CategoryTheory.id_apply,
      eqToIso.hom, eqToIso.inv] at hcancel
    exact hcancel
  rw [← ht]
  refine TensorProduct.induction_on u ?_ ?_ ?_
  · simp only [map_zero, TensorProduct.tmul_zero]
    change 0 = (E.composeSecondMap X (intermediate 0).obj Y
      (d.arrowDegree 0) (tailDegree d) (n + 1)
      (headContractionOutputDegreeEq d) (E.firstFactorMap d x)) 0
    exact (LinearMap.map_zero _).symm
  · intro y r
    rw [headRawInput_eq]
    unfold firstFactorMap
    simp only [LinearMap.comp_apply]
    convert E.evaluateWord_head_contraction_apply_raw d x y r using 1
    congr 1
  · intro a b ha hb
    simp only [map_add, TensorProduct.tmul_add]
    have hsum := congrArg₂ (· + ·) ha hb
    have hlinear := (E.composeSecondMap X (intermediate 0).obj Y
      (d.arrowDegree 0) (tailDegree d) (n + 1)
      (headContractionOutputDegreeEq d) (E.firstFactorMap d x)).map_add
        ((E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile d)) ((eqToHom (tailRawCoordinateEq d).symm).hom a))
        ((E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile d)) ((eqToHom (tailRawCoordinateEq d).symm).hom b))
    exact hsum.trans hlinear.symm

set_option maxHeartbeats 4000000 in
-- Splitting the dependent contraction sum and normalizing its head coordinate is expensive.
/-- The signed contraction differential of a positive word splits into its head contraction and
the unchanged head contraction composed with the signed tail contraction differential. -/
theorem evaluateContractionDifferential_succ_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateContractionDifferential d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      d.contractionSign 0 •
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d)
          (E.firstFactorMap d x)
          (E.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t) +
        E.composeElement X (intermediate 0).obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          (E.firstContractionMap d x)
          (E.evaluateContractionDifferential (tailDegreeProfile d) t) := by
  cases k with
  | zero =>
      let A := intermediate 0
      have hA : A = intermediate 0 := rfl
      clear_value A
      have hintermediate : intermediate = fun _ : Fin 1 ↦ A := by
        funext i
        rw [hA]
        exact congrArg intermediate (Fin.eq_zero i)
      cases hintermediate
      unfold evaluateContractionDifferential
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
      rw [Fin.sum_univ_succ]
      have hrest :
          (∑ i : Fin 0,
            d.contractionSign i.succ •
              E.evaluateWord
                (eraseIntermediate (singleton X Y A) i.succ)
                (d.contract i.succ)
                ((contractionTensorMap d i.succ).hom
                  ((eqToHom (summandModule_succ d).symm).hom
                    (x ⊗ₜ[ℤ] t)))) = 0 := Finset.sum_empty
      have htail :
          (∑ i : Fin 0,
            (tailDegreeProfile d).contractionSign i •
              E.evaluateWord
                (eraseIntermediate (tailWord (Y := Y) (fun _ : Fin 1 ↦ A)) i)
                ((tailDegreeProfile d).contract i)
                ((contractionTensorMap (tailDegreeProfile d) i).hom t)) = 0 :=
        Finset.sum_empty
      rw [hrest, add_zero, htail]
      have hhead := E.evaluate_headContraction_singleton_apply_tensor
        X Y A d x t
      rw [hhead]
      change _ = _ +
        (E.composeSecondMap X A.obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          (E.firstContractionMap d x)) 0
      rw [LinearMap.map_zero, add_zero]
  | succ k =>
      unfold evaluateContractionDifferential
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
      rw [Fin.sum_univ_succ]
      congr 1
      · exact congrArg (fun z ↦ d.contractionSign 0 • z)
          (E.evaluateWord_head_contraction_apply_tensor d x t)
      · change (∑ i : Fin (k + 1),
            d.contractionSign i.succ •
              E.evaluateWord
                (eraseIntermediate
                  ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
                  i.succ)
                (d.contract i.succ)
                ((contractionTensorMap d i.succ).hom
                  ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)))) = _
        change _ =
          (E.composeSecondMap X (intermediate 0).obj Y
            (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
            (by have h := tailDegree_add_neg_one_add_head d; omega)
            (E.firstContractionMap d x))
            (∑ i : Fin (k + 1),
              (tailDegreeProfile d).contractionSign i •
                E.evaluateWord
                  (eraseIntermediate (tailWord (Y := Y) intermediate) i)
                  ((tailDegreeProfile d).contract i)
                  ((contractionTensorMap (tailDegreeProfile d) i).hom t))
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, ← contractionSign_succ_eq_tail d i]
        exact congrArg (fun z ↦ d.contractionSign i.succ • z)
          (E.evaluateWord_tail_contraction_apply_tensor d i x t)

set_option maxHeartbeats 4000000 in
-- The dependent degree indices in the four Leibniz contributions require substantial
-- normalization before the final additive identity is visible.
/-- Differential compatibility for a positive-word pure head/tail tensor, assuming compatibility
for the tail word. -/
theorem differentialAfterEvaluate_succ_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (htail : E.differentialAfterEvaluate (tailDegreeProfile d) =
      E.evaluateTotalDifferential (tailDegreeProfile d))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.differentialAfterEvaluate d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) =
      E.evaluateTotalDifferential d
        ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)) := by
  let tailEval := E.evaluateWord (tailWord (Y := Y) intermediate)
    (tailDegreeProfile d) t
  let tailInternal := E.evaluateInternalDifferential (tailDegreeProfile d) t
  let tailContraction := E.evaluateContractionDifferential (tailDegreeProfile d) t
  let headRaised :=
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (raisedHeadContractDegreeEq d))).hom
        (E.firstContractionMap (d.raise 0)
          ((factorDifferential d 0 0).hom x))
  let headOriginal := E.firstFactorMap d x
  let headContracted := E.firstContractionMap d x
  have htailPoint := congrArg
    (fun f : summandModule (tailDegreeProfile d) →ₗ[ℤ]
      (E.hom (intermediate 0).obj Y).X (tailDegree d + 1) ↦ f t) htail
  have htailDifferential := htailPoint
  unfold differentialAfterEvaluate evaluateTotalDifferential at htailDifferential
  change
    ((E.hom (intermediate 0).obj Y).d
      (tailDegree d) (tailDegree d + 1)) tailEval =
      tailInternal + tailContraction at htailDifferential
  have htailCompose :=
    (E.composeSecondMap X (intermediate 0).obj Y
      (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
      (by have h := tailDegree_add_neg_one_add_head d; omega)
      headContracted).map_add tailInternal tailContraction
  change
    E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        headContracted (tailInternal + tailContraction) =
      E.composeElement X (intermediate 0).obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          headContracted tailInternal +
        E.composeElement X (intermediate 0).obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          headContracted tailContraction at htailCompose
  have hhead := E.composeElement_firstContractionMap_d d x tailEval
  unfold evaluateTotalDifferential
  simp only [LinearMap.add_apply]
  rw [E.differentialAfterEvaluate_succ_raw d x t,
    E.evaluateInternalDifferential_succ_apply_tensor d x t,
    E.evaluateContractionDifferential_succ_apply_tensor d x t]
  change
    E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        headContracted
        (((E.hom (intermediate 0).obj Y).d
          (tailDegree d) (tailDegree d + 1)) tailEval) +
      (tailDegree d).negOnePow •
        E.composeElement X (intermediate 0).obj Y
          ((-1 + d.arrowDegree 0) + 1) (tailDegree d) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          (((E.hom X (intermediate 0).obj).d
            (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + 1))
              headContracted) tailEval =
    d.internalSign 0 •
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0) (tailDegree d) (n + 1)
          (headContractionOutputDegreeEq d) headRaised tailEval +
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        headContracted tailInternal +
      (d.contractionSign 0 •
          E.composeElement X (intermediate 0).obj Y
            (d.arrowDegree 0) (tailDegree d) (n + 1)
            (headContractionOutputDegreeEq d) headOriginal tailEval +
        E.composeElement X (intermediate 0).obj Y
          (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
          (by have h := tailDegree_add_neg_one_add_head d; omega)
          headContracted tailContraction)
  rw [htailDifferential]
  change
    E.composeElement X (intermediate 0).obj Y
      (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
      (by have h := tailDegree_add_neg_one_add_head d; omega)
      headContracted (tailInternal + tailContraction) + _ = _
  rw [htailCompose]
  rw [hhead]
  rw [internalSign_zero_eq_neg_tail, contractionSign_zero_eq_tail]
  simp only [Units.smul_def, smul_sub, neg_smul]
  dsimp only [headRaised, headOriginal]
  abel

set_option maxHeartbeats 4000000 in
-- Transporting an arbitrary summand through the recursive tensor coordinate is expensive.
/-- Differential compatibility for a positive word follows from compatibility of its tail. -/
theorem evaluateWord_d_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (htail : E.differentialAfterEvaluate (tailDegreeProfile d) =
      E.evaluateTotalDifferential (tailDegreeProfile d)) :
    E.differentialAfterEvaluate d = E.evaluateTotalDifferential d := by
  apply LinearMap.ext
  intro u
  let v := (eqToHom (summandModule_succ d)).hom u
  have hu : (eqToHom (summandModule_succ d).symm).hom v = u := by
    have hcancel := ConcreteCategory.congr_hom
      (eqToIso (summandModule_succ d)).hom_inv_id u
    simp only [ModuleCat.comp_apply, CategoryTheory.id_apply,
      eqToIso.hom, eqToIso.inv] at hcancel
    exact hcancel
  rw [← hu]
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp only [map_zero]
  · intro x t
    exact E.differentialAfterEvaluate_succ_apply_tensor d htail x t
  · intro a b ha hb
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

set_option maxHeartbeats 4000000 in
-- The induction step unfolds and normalizes the complete corrected-word differential formula.
/-- Evaluation commutes with the corrected Drinfeld differential on every homogeneous word. -/
theorem evaluateWord_d_of_length
    {X Y : ComplexCategory} (k : ℕ)
    (intermediate : Fin k → CorrectedAcyclicComplexCategory)
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) n) :
    E.differentialAfterEvaluate d = E.evaluateTotalDifferential d := by
  induction k generalizing X n with
  | zero =>
      have hintermediate : intermediate = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      cases hintermediate
      exact E.evaluateWord_d_nil d
  | succ k ih =>
      apply E.evaluateWord_d_succ d
      exact ih (fun i : Fin k ↦ intermediate i.succ) (tailDegreeProfile d)

/-- Evaluation commutes with the corrected Drinfeld differential for an arbitrary word. -/
theorem evaluateWord_d
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    E.differentialAfterEvaluate d = E.evaluateTotalDifferential d := by
  cases w with
  | mk k intermediate =>
      exact E.evaluateWord_d_of_length k intermediate d

/-- On an included homogeneous summand, evaluating the quotient total differential is exactly
the wordwise total-differential evaluation. -/
theorem evaluateGradedValue_totalDifferential_inclusion
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (x : summandModule d) :
    E.evaluateGradedValue X Y (n + 1)
        ((quotientTotalDifferential X Y n).hom
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
            ⟨w, d⟩).hom (ULift.up x))) =
      E.evaluateTotalDifferential d x := by
  change E.evaluateGradedValue X Y (n + 1)
      (((Limits.Sigma.ι
        (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
        ⟨w, d⟩ ≫ quotientTotalDifferential X Y n).hom) (ULift.up x)) = _
  rw [quotientTotalDifferential_inclusion]
  unfold evaluateTotalDifferential evaluateInternalDifferential
    evaluateContractionDifferential internalDifferentialFromSummand
    contractionDifferentialFromSummand internalDifferentialLargeMap
    contractionLargeMap
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.comp_apply]
  rw [E.evaluateGradedValue_add]
  congr 1
  · change (E.evaluateGradedModule X Y (n + 1)).hom
        (∑ i, d.internalSign i •
          (Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
            ⟨w, d.raise i⟩).hom
              (((ModuleCat.uliftFunctor.{1} ℤ).map
                (internalDifferentialTensorMap d i)).hom (ULift.up x))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul]
    apply congrArg (fun z ↦ d.internalSign i • z)
    change (E.evaluateGradedModule X Y (n + 1)).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
          ⟨w, d.raise i⟩).hom
            (ULift.up ((internalDifferentialTensorMap d i).hom x))) =
      E.evaluateWord w (d.raise i)
        ((internalDifferentialTensorMap d i).hom x)
    exact E.evaluateGradedModule_inclusion ⟨w, d.raise i⟩
      ((internalDifferentialTensorMap d i).hom x)
  · change (E.evaluateGradedModule X Y (n + 1)).hom
        (∑ i, d.contractionSign i •
          (Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
            ⟨eraseIntermediate w i, d.contract i⟩).hom
              (((ModuleCat.uliftFunctor.{1} ℤ).map
                (contractionTensorMap d i)).hom (ULift.up x))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul]
    apply congrArg (fun z ↦ d.contractionSign i • z)
    change (E.evaluateGradedModule X Y (n + 1)).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
          ⟨eraseIntermediate w i, d.contract i⟩).hom
            (ULift.up ((contractionTensorMap d i).hom x))) =
      E.evaluateWord (eraseIntermediate w i) (d.contract i)
        ((contractionTensorMap d i).hom x)
    exact E.evaluateGradedModule_inclusion
      ⟨eraseIntermediate w i, d.contract i⟩
      ((contractionTensorMap d i).hom x)

/-- The target Hom differential, with scalars forgotten to integers. -/
def targetIntDifferential (X Y : ComplexCategory) (n : ℤ) :
    E.targetIntModule X Y n ⟶ E.targetIntModule X Y (n + 1) :=
  ModuleCat.ofHom
    (((E.hom X Y).d n (n + 1)).hom.toAddMonoidHom.toIntLinearMap)

/-- Evaluation of the corrected quotient graded carrier commutes with its total differential. -/
theorem evaluateGradedModule_comm_d
    (X Y : ComplexCategory) (n : ℤ) :
    E.evaluateGradedModule X Y n ≫ E.targetIntDifferential X Y n =
      quotientTotalDifferential X Y n ≫
        E.evaluateGradedModule X Y (n + 1) := by
  apply Limits.Sigma.hom_ext
  rintro ⟨w, d⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  cases z with
  | up x =>
      simp only [ModuleCat.comp_apply]
      rw [E.evaluateGradedModule_inclusion ⟨w, d⟩ x]
      change ((E.hom X Y).d n (n + 1))
          (E.evaluateWord w d x) =
        E.evaluateGradedValue X Y (n + 1)
          ((quotientTotalDifferential X Y n).hom
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
              ⟨w, d⟩).hom (ULift.up x)))
      rw [E.evaluateGradedValue_totalDifferential_inclusion d x]
      exact congrArg (fun f ↦ f x) (E.evaluateWord_d d)

/-- The corrected Drinfeld word evaluator is an actual cochain map on each Hom complex. -/
def evaluateCochainMap (X Y : ComplexCategory) :
    quotientCoefficientCochainComplex X Y ⟶ E.hom X Y where
  f n := E.evaluateCoefficientDegree X Y n
  comm' i j hij := by
    subst j
    rw [quotientCoefficientCochainComplex_d_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rcases z with ⟨z⟩
    change ((E.hom X Y).d i (i + 1))
        (E.evaluateGradedValue X Y i z) =
      E.evaluateGradedValue X Y (i + 1)
        ((quotientTotalDifferential X Y i).hom z)
    have h := ConcreteCategory.congr_hom
      (E.evaluateGradedModule_comm_d X Y i) z
    change ((E.hom X Y).d i (i + 1))
        (E.evaluateGradedValue X Y i z) =
      E.evaluateGradedValue X Y (i + 1)
        ((quotientTotalDifferential X Y i).hom z) at h
    exact h

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
