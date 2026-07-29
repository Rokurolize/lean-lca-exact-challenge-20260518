/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationDifferential

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

/-- The evaluated head-internal term has the normalized head/tail composition form. -/
theorem evaluateWord_head_internal_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
        (d.raise 0)
        ((internalDifferentialTensorMap d 0).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      E.composeElement X (intermediate 0).obj Y
        (d.arrowDegree 0) (tailDegree d) (n + 1)
        (headContractionOutputDegreeEq d)
        ((eqToHom (congrArg
          (fun q ↦ (E.hom X (intermediate 0).obj).X q)
          (raisedHeadContractDegreeEq d))).hom
            (E.firstContractionMap (d.raise 0)
              ((factorDifferential d 0 0).hom x)))
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile d) t) := by
  rw [internalDifferentialTensorMap_zero_apply_tensor,
    E.evaluateWord_succ_eq (d.raise 0), E.evaluateSucc_apply_tensor]
  have hcast := E.composeElement_cast_inputs_output X (intermediate 0).obj Y
    (raisedHeadContractDegreeEq d) (tailDegree_raise_zero_eq d) rfl
    (tailDegree_add_neg_one_add_head (d.raise 0))
    (headContractionOutputDegreeEq d)
    (E.firstContractionMap (d.raise 0)
      ((factorDifferential d 0 0).hom x))
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile (d.raise 0))
      ((eqToHom (tailRaiseZeroSummandModuleEq d)).hom t))
  have htail := E.evaluateWord_tail_raise_zero d t
  rw [htail] at hcast
  simpa only [tailDegree, eqToHom_refl, CategoryTheory.id_apply] using hcast

/-- The evaluated tail-internal term is the unchanged head contraction composed with the
corresponding evaluated differential term of the tail word. -/
theorem evaluateWord_tail_internal_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
        (d.raise i.succ)
        ((internalDifferentialTensorMap d i.succ).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        (E.firstContractionMap d x)
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          ((tailDegreeProfile d).raise i)
          ((internalDifferentialTensorMap (tailDegreeProfile d) i).hom t)) := by
  rw [internalDifferentialTensorMap_succ_apply_tensor,
    E.evaluateWord_succ_eq (d.raise i.succ), E.evaluateSucc_apply_tensor]
  let u := (internalDifferentialTensorMap (tailDegreeProfile d) i).hom t
  have hcast := E.composeElement_cast_inputs_output X (intermediate 0).obj Y
    (tailRaiseContractedHeadDegreeEq d i) (tailDegree_raise_succ_eq d i) rfl
    (tailDegree_add_neg_one_add_head (d.raise i.succ))
    (by have h := tailDegree_add_neg_one_add_head d; omega)
    (E.firstContractionMap (d.raise i.succ)
      ((factorDifferential d i.succ 0).hom x))
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile (d.raise i.succ))
      ((eqToHom (tailRaiseSuccSummandModuleEq d i).symm).hom u))
  have hhead := E.firstContractionMap_raise_succ d i x
  have htail := E.evaluateWord_tail_raise_succ d i u
  rw [hhead, htail] at hcast
  simpa only [u, tailDegree, eqToHom_refl, CategoryTheory.id_apply] using hcast

private theorem induction_eqToHom_tensor_apply
    {M M' N N' : ModuleCat.{0} ℤ}
    (hM : M = M') (hN : N = N') (x : M) (y : N) :
    (eqToHom (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hM hN)).hom
        (x ⊗ₜ[ℤ] y) =
      (eqToHom hM).hom x ⊗ₜ[ℤ] (eqToHom hN).hom y := by
  subst M'
  subst N'
  rfl

/-- Evaluation of a positive word through any transported head/tail coordinate equality. -/
theorem evaluateWord_succ_apply_tensor_of_coordinates
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    {M N : ModuleCat.{0} ℤ}
    (hM : factorModule d 0 = M)
    (hN : summandModule (tailDegreeProfile d) = N)
    (x : M) (t : N) :
    E.evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
        ((eqToHom ((summandModule_succ d).trans
          (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hM hN)).symm).hom
            (x ⊗ₜ[ℤ] t)) =
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d) n
        (tailDegree_add_neg_one_add_head d)
        (E.firstContractionMap d ((eqToHom hM.symm).hom x))
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile d) ((eqToHom hN.symm).hom t)) := by
  let hTensor :=
    congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hM hN
  have hinput :
      (eqToHom ((summandModule_succ d).trans hTensor).symm).hom
          (x ⊗ₜ[ℤ] t) =
        (eqToHom (summandModule_succ d).symm).hom
          ((eqToHom hM.symm).hom x ⊗ₜ[ℤ] (eqToHom hN.symm).hom t) := by
    have hproof : ((summandModule_succ d).trans hTensor).symm =
        hTensor.symm.trans (summandModule_succ d).symm :=
      Subsingleton.elim _ _
    rw [hproof]
    have hcomp := ConcreteCategory.congr_hom
      (eqToHom_trans hTensor.symm (summandModule_succ d).symm)
      (x ⊗ₜ[ℤ] t)
    simp only [ModuleCat.comp_apply] at hcomp
    rw [← hcomp]
    rw [induction_eqToHom_tensor_apply]
  rw [hinput, E.evaluateWord_succ_eq d, E.evaluateSucc_apply_tensor]
  rfl

/-- A non-head contraction preserves the first intermediate object. -/
def contractSuccIntermediateZeroEq
    {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory)
    (i : Fin (k + 1)) :
    intermediate (i.succ.succAbove (0 : Fin (k + 1))) = intermediate 0 := by
  congr 1

def dgHomModuleTransportEq
    (X X' Y Y' : ComplexCategory) (hX : X = X') (hY : Y = Y')
    {p p' : ℤ} (hp : p = p') :
    (dgHomZModuleCochainComplex X Y).X p =
      (dgHomZModuleCochainComplex X' Y').X p' := by
  subst X'
  subst Y'
  subst p'
  rfl

def targetHomModuleTransportEq
    (X X' Y Y' : ComplexCategory) (hX : X = X') (hY : Y = Y')
    {p p' : ℤ} (hp : p = p') :
    (E.hom X Y).X p = (E.hom X' Y').X p' := by
  subst X'
  subst Y'
  subst p'
  rfl

/-- The original enriched functor map is natural under endpoint and degree transport. -/
theorem factorMap_transport
    (X X' Y Y' : ComplexCategory) (hX : X = X') (hY : Y = Y')
    {p p' : ℤ} (hp : p = p')
    (x : (dgHomZModuleCochainComplex X Y).X p) :
    (eqToHom (targetHomModuleTransportEq E X X' Y Y' hX hY hp)).hom
        (E.factorMap X Y p x) =
      E.factorMap X' Y' p'
        ((eqToHom (dgHomModuleTransportEq X X' Y Y' hX hY hp)).hom x) := by
  subst X'
  subst Y'
  subst p'
  rfl

def contractSuccHeadObjectEq
    {k : ℕ}
    (intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory)
    (i : Fin (k + 1)) :
    (intermediate (i.succ.succAbove (0 : Fin (k + 1)))).obj =
      (intermediate 0).obj :=
  congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj)
    (contractSuccIntermediateZeroEq intermediate i)

def contractSuccContractedHeadDegreeEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    -1 + (d.contract i.succ).arrowDegree 0 = -1 + d.arrowDegree 0 := by
  rw [contract_succ_arrowDegree_zero d i]

def contractSuccOriginalHeadModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (dgHomZModuleCochainComplex X
      (intermediate (i.succ.succAbove (0 : Fin (k + 1)))).obj).X
        ((d.contract i.succ).arrowDegree 0) =
      (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) :=
  dgHomModuleTransportEq X X _ _ rfl (contractSuccHeadObjectEq intermediate i)
    (contract_succ_arrowDegree_zero d i)

def contractSuccTargetHeadModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (E.hom X
      (intermediate (i.succ.succAbove (0 : Fin (k + 1)))).obj).X
        ((d.contract i.succ).arrowDegree 0) =
      (E.hom X (intermediate 0).obj).X (d.arrowDegree 0) :=
  targetHomModuleTransportEq E X X _ _ rfl (contractSuccHeadObjectEq intermediate i)
    (contract_succ_arrowDegree_zero d i)

/-- The first-factor map is unchanged by a contraction strictly after the head. -/
theorem firstFactorMap_contract_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) (x : factorModule d 0) :
    (eqToHom (contractSuccTargetHeadModuleEq E d i)).hom
        (E.firstFactorMap (d.contract i.succ)
          ((eqToHom (contract_succ_factorModule_zero_eq d i).symm).hom x)) =
      E.firstFactorMap d x := by
  let B : CorrectedAcyclicComplexCategory :=
    intermediate (i.succ.succAbove (0 : Fin (k + 1)))
  let hA : B = intermediate 0 := by
    dsimp only [B]
    congr 1
  let hB : B.obj = (intermediate 0).obj :=
    congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj) hA
  let hdeg := contract_succ_arrowDegree_zero d i
  let hFactor := contract_succ_factorModule_zero_eq d i
  let hZero := factorModule_zero_succ (d.contract i.succ)
  have hcast := E.factorMap_transport X X B.obj (intermediate 0).obj
    rfl hB hdeg
    ((eqToHom hZero).hom ((eqToHom hFactor.symm).hom x))
  have hsourceProof :
      dgHomModuleTransportEq X X B.obj (intermediate 0).obj rfl hB hdeg =
        contractSuccOriginalHeadModuleEq d i := Subsingleton.elim _ _
  have htargetProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 0).obj rfl hB hdeg =
        contractSuccTargetHeadModuleEq E d i := Subsingleton.elim _ _
  rw [hsourceProof, htargetProof] at hcast
  have hx :
      (eqToHom (contractSuccOriginalHeadModuleEq d i)).hom
          ((eqToHom hZero).hom ((eqToHom hFactor.symm).hom x)) =
        (eqToHom (factorModule_zero_succ d)).hom x := by
    change ((eqToHom hFactor.symm ≫ eqToHom hZero ≫
      eqToHom (contractSuccOriginalHeadModuleEq d i)).hom x) = _
    simp only [eqToHom_trans]
  rw [hx] at hcast
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  exact hcast

/-- Homogeneous target composition is natural under object and degree transport. -/
theorem composeElement_transport
    (X X' Y Y' Z Z' : ComplexCategory)
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {p p' q q' n n' : ℤ} (hp : p = p') (hq : q = q') (hn : n = n')
    (h : q + p = n) (h' : q' + p' = n')
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (eqToHom (targetHomModuleTransportEq E X X' Z Z' hX hZ hn)).hom
        (E.composeElement X Y Z p q n h x y) =
      E.composeElement X' Y' Z' p' q' n' h'
        ((eqToHom (targetHomModuleTransportEq E X X' Y Y' hX hY hp)).hom x)
        ((eqToHom (targetHomModuleTransportEq E Y Y' Z Z' hY hZ hq)).hom y) := by
  subst X'
  subst Y'
  subst Z'
  subst p'
  subst q'
  subst n'
  rfl

/-- The chosen contraction element is natural under equality of corrected acyclic objects. -/
theorem contraction_transport
    {A B : CorrectedAcyclicComplexCategory} (h : A = B) :
    (eqToHom (targetHomModuleTransportEq E A.obj B.obj A.obj B.obj
      (congrArg (fun C : CorrectedAcyclicComplexCategory ↦ C.obj) h)
      (congrArg (fun C : CorrectedAcyclicComplexCategory ↦ C.obj) h) rfl)).hom
        (E.contraction A) = E.contraction B := by
  subst B
  rfl

def contractSuccFirstContractionTargetEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    (E.hom X
      (intermediate (i.succ.succAbove (0 : Fin (k + 1)))).obj).X
        (-1 + (d.contract i.succ).arrowDegree 0) =
      (E.hom X (intermediate 0).obj).X (-1 + d.arrowDegree 0) :=
  targetHomModuleTransportEq E X X _ _ rfl (contractSuccHeadObjectEq intermediate i)
    (contractSuccContractedHeadDegreeEq d i)

/-- The first contraction map is unchanged by a contraction strictly after the head. -/
theorem firstContractionMap_contract_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) (x : factorModule d 0) :
    (eqToHom (contractSuccFirstContractionTargetEq E d i)).hom
        (E.firstContractionMap (d.contract i.succ)
          ((eqToHom (contract_succ_factorModule_zero_eq d i).symm).hom x)) =
      E.firstContractionMap d x := by
  let B : CorrectedAcyclicComplexCategory :=
    intermediate (i.succ.succAbove (0 : Fin (k + 1)))
  let hB : B = intermediate 0 := by
    dsimp only [B]
    congr 1
  let hObj := congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj) hB
  let hdeg := contract_succ_arrowDegree_zero d i
  let hout := contractSuccContractedHeadDegreeEq d i
  let hFactor := contract_succ_factorModule_zero_eq d i
  have hcompose := E.composeElement_transport
    X X B.obj (intermediate 0).obj B.obj (intermediate 0).obj
    rfl hObj hObj hdeg rfl hout rfl rfl
    (E.firstFactorMap (d.contract i.succ) ((eqToHom hFactor.symm).hom x))
    (E.contraction B)
  have hOutProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 0).obj rfl hObj hout =
        contractSuccFirstContractionTargetEq E d i := Subsingleton.elim _ _
  have hFirstProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 0).obj rfl hObj hdeg =
        contractSuccTargetHeadModuleEq E d i := Subsingleton.elim _ _
  rw [hOutProof, hFirstProof] at hcompose
  have hfirst := E.firstFactorMap_contract_succ d i x
  have hcontr := E.contraction_transport hB
  rw [hfirst, hcontr] at hcompose
  unfold firstContractionMap composeFirstMap
  change (eqToHom (contractSuccFirstContractionTargetEq E d i)).hom
      (E.composeElement X B.obj B.obj
        ((d.contract i.succ).arrowDegree 0) (-1)
        (-1 + (d.contract i.succ).arrowDegree 0) rfl
        (E.firstFactorMap (d.contract i.succ)
          ((eqToHom hFactor.symm).hom x)) (E.contraction B)) = _
  exact hcompose

/-- The evaluated tail-contraction term is the unchanged head contraction composed with the
corresponding evaluated contraction term of the tail word. -/
theorem evaluateWord_tail_contraction_apply_tensor
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1))
    (x : factorModule d 0) (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        (eraseIntermediate
          ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y)
          i.succ)
        (d.contract i.succ)
        ((contractionTensorMap d i.succ).hom
          ((eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t))) =
      E.composeElement X (intermediate 0).obj Y
        (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
        (by have h := tailDegree_add_neg_one_add_head d; omega)
        (E.firstContractionMap d x)
        (E.evaluateWord
          (eraseIntermediate (tailWord (Y := Y) intermediate) i)
          ((tailDegreeProfile d).contract i)
          ((contractionTensorMap (tailDegreeProfile d) i).hom t)) := by
  rw [contractionTensorMap_succ_apply_tensor]
  let u := (contractionTensorMap (tailDegreeProfile d) i).hom t
  have heval := E.evaluateWord_succ_apply_tensor_of_coordinates
    (d.contract i.succ)
    (contract_succ_factorModule_zero_eq d i)
    (tailContractSummandModuleEq d i) x u
  change (E.evaluateWord
      (⟨k + 1, fun j ↦ intermediate (i.succ.succAbove j)⟩ :
        DrinfeldWord X Y)
      (d.contract i.succ)
      ((eqToHom (contractSuccSummandModuleEq d i).symm).hom
        (x ⊗ₜ[ℤ] u))) = _
  rw [heval]
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  let B : CorrectedAcyclicComplexCategory :=
    intermediate (i.succ.succAbove (0 : Fin (k + 1)))
  let hB : B = intermediate 0 := by
    dsimp only [B]
    congr 1
  let hObj := congrArg (fun A : CorrectedAcyclicComplexCategory ↦ A.obj) hB
  let hp := contractSuccContractedHeadDegreeEq d i
  let hq := tailDegree_contract_succ_eq d i
  have hcompose := E.composeElement_transport
    X X B.obj (intermediate 0).obj Y Y
    rfl hObj rfl hp hq rfl
    (tailDegree_add_neg_one_add_head (d.contract i.succ))
    (by have h := tailDegree_add_neg_one_add_head d; omega)
    (E.firstContractionMap (d.contract i.succ)
      ((eqToHom (contract_succ_factorModule_zero_eq d i).symm).hom x))
    (E.evaluateWord
      (tailWord (Y := Y) (eraseIntermediate w i.succ).intermediate)
      (tailDegreeProfile (d.contract i.succ))
      ((eqToHom (tailContractSummandModuleEq d i).symm).hom u))
  have hFirstProof :
      targetHomModuleTransportEq E X X B.obj (intermediate 0).obj rfl hObj hp =
        contractSuccFirstContractionTargetEq E d i := Subsingleton.elim _ _
  have hTailProof :
      targetHomModuleTransportEq E B.obj (intermediate 0).obj Y Y hObj rfl hq =
        congrArg (fun q ↦ (E.hom (intermediate 0).obj Y).X q) hq :=
    Subsingleton.elim _ _
  rw [hFirstProof, hTailProof] at hcompose
  dsimp only [w, B] at hcompose
  have hfirst := E.firstContractionMap_contract_succ d i x
  have htail := E.evaluateWord_tail_contract_succ d i u
  have hfirstCompose := congrArg
    (fun z ↦ E.composeElement X (intermediate 0).obj Y
      (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
      (by have h := tailDegree_add_neg_one_add_head d; omega) z
      ((eqToHom (congrArg
        (fun q ↦ (E.hom (intermediate 0).obj Y).X q) hq)).hom
          (E.evaluateWord
            (tailWord (Y := Y) (eraseIntermediate w i.succ).intermediate)
            (tailDegreeProfile (d.contract i.succ))
            ((eqToHom (tailContractSummandModuleEq d i).symm).hom u)))) hfirst
  have htailCompose := congrArg
    (fun z ↦ E.composeElement X (intermediate 0).obj Y
      (-1 + d.arrowDegree 0) (tailDegree d + 1) (n + 1)
      (by have h := tailDegree_add_neg_one_add_head d; omega)
      (E.firstContractionMap d x) z) htail
  have hnormalized := hcompose.trans (hfirstCompose.trans htailCompose)
  dsimp only [eraseIntermediate] at hnormalized
  simpa [u, w, B, tailDegree, eraseIntermediate] using hnormalized

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
