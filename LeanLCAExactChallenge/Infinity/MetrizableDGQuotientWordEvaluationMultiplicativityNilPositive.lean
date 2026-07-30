/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationNilPositiveApply
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationMultiplicativityNilNil

/-! # Zero-left/positive-right multiplicativity

This module combines the pure-tensor zero-left/positive-right composition formula with the
positive-word evaluation recursion.  It proves that evaluation preserves composition when the
left word has length zero and the right word has positive length.
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

/-- The merged head degree in the normalized positive profile. -/
def nilPositiveHeadDegreeEq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (nilPositiveDegreeProfile (W := W) p d).arrowDegree 0 =
      p + d.arrowDegree 0 :=
  nilPositiveDegreeProfile_arrowDegree_zero (W := W) p d

/-- The contracted merged-head degree in the order used by target associativity. -/
def nilPositiveContractedHeadDegreeEq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    -1 + (nilPositiveDegreeProfile (W := W) p d).arrowDegree 0 =
      (-1 + d.arrowDegree 0) + p := by
  rw [nilPositiveHeadDegreeEq]
  omega

/-- Mapping the merged head factor into the target enrichment is target composition of the
zero-word element with the original positive head factor. -/
theorem firstFactorMap_nil_positive_head
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : (dgHomZModuleCochainComplex W X).X p)
    (y : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom W (intermediate 0).obj).X q)
      (nilPositiveHeadDegreeEq (W := W) p d))).hom
        (E.firstFactorMap (nilPositiveDegreeProfile (W := W) p d)
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
            ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y))) =
      E.composeElement W X (intermediate 0).obj
        p (d.arrowDegree 0) (p + d.arrowDegree 0) (by omega)
        (E.factorMap W X p x) (E.firstFactorMap d y) := by
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  rw [E.factorMap_cast_degree W (intermediate 0).obj
    (nilPositiveHeadDegreeEq (W := W) p d)]
  let hdegree := congrArg
    (fun q ↦ (dgHomZModuleCochainComplex W (intermediate 0).obj).X q)
    (nilPositiveHeadDegreeEq (W := W) p d)
  have hsource :
      (factorModule_zero_succ
        (nilPositiveDegreeProfile (W := W) p d)).trans hdegree =
        nilPositiveHeadFactor_eq (W := W) p d :=
    Subsingleton.elim _ _
  have hinput :
      (eqToHom hdegree).hom
          ((eqToHom (factorModule_zero_succ
            (nilPositiveDegreeProfile (W := W) p d))).hom
            ((nilPositiveHeadCompositionMap (W := W) p d).hom
              ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ]
                y))) =
        (eqToHom (nilPositiveHeadFactor_eq (W := W) p d)).hom
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
            ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ]
              y)) := by
    change ((eqToHom (factorModule_zero_succ
      (nilPositiveDegreeProfile (W := W) p d)) ≫ eqToHom hdegree).hom
        ((nilPositiveHeadCompositionMap (W := W) p d).hom
          ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ]
            y))) = _
    rw [eqToHom_trans, hsource]
  rw [hinput]
  rw [nilPositiveHeadCompositionMap_apply]
  have hcancel := ConcreteCategory.congr_hom
    (eqToIso (factorModule_nilDegreeProfile W X p)).inv_hom_id x
  simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
    CategoryTheory.id_apply] at hcancel
  rw [hcancel]
  rw [E.factorMap_compose]

/-- Contracting the merged head is target composition of the zero-word image with the original
positive contracted head. -/
theorem firstContractionMap_nil_positive_head
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : (dgHomZModuleCochainComplex W X).X p)
    (y : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom W (intermediate 0).obj).X q)
      (nilPositiveContractedHeadDegreeEq (W := W) p d))).hom
        (E.firstContractionMap (nilPositiveDegreeProfile (W := W) p d)
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
            ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y))) =
      E.composeElement W X (intermediate 0).obj
        p (-1 + d.arrowDegree 0) ((-1 + d.arrowDegree 0) + p) rfl
        (E.factorMap W X p x) (E.firstContractionMap d y) := by
  unfold firstContractionMap composeFirstMap
  change (eqToHom (congrArg
      (fun q ↦ (E.hom W (intermediate 0).obj).X q)
      (nilPositiveContractedHeadDegreeEq (W := W) p d))).hom
      (E.composeElement W (intermediate 0).obj (intermediate 0).obj
        ((nilPositiveDegreeProfile (W := W) p d).arrowDegree 0) (-1)
        (-1 + (nilPositiveDegreeProfile (W := W) p d).arrowDegree 0) rfl
        (E.firstFactorMap (nilPositiveDegreeProfile (W := W) p d)
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
            ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y)))
        (E.contraction (intermediate 0))) = _
  have hcast := E.composeElement_cast_first_output W (intermediate 0).obj
    (intermediate 0).obj
    (nilPositiveHeadDegreeEq (W := W) p d)
    (nilPositiveContractedHeadDegreeEq (W := W) p d)
    rfl (by omega)
    (E.firstFactorMap (nilPositiveDegreeProfile (W := W) p d)
      ((nilPositiveHeadCompositionMap (W := W) p d).hom
        ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y)))
    (E.contraction (intermediate 0))
  rw [E.firstFactorMap_nil_positive_head (W := W) p d x y] at hcast
  have hassoc := E.composeElement_assoc_of_degree_eq W X (intermediate 0).obj
    (intermediate 0).obj
    (show d.arrowDegree 0 + p = p + d.arrowDegree 0 by omega)
    (show -1 + (p + d.arrowDegree 0) = (-1 + d.arrowDegree 0) + p by omega)
    rfl rfl
    (E.factorMap W X p x) (E.firstFactorMap d y)
    (E.contraction (intermediate 0))
  exact hcast.trans hassoc

/-- Evaluation of a zero-left/positive-right composite in its normalized positive coordinates. -/
theorem evaluateWord_nil_positive_coordinates
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (E.evaluateWord
        ((nil W X).append
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y))
        ((nilDegreeProfile W X p).append d)).comp
      (nilPositiveSummandIso (W := W) p d).inv.hom =
    (E.evaluateSucc (nilPositiveDegreeProfile (W := W) p d)
      (E.evaluateWord (tailWord (Y := Y) intermediate)
        (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)))).comp
      (((MonoidalCategory.tensorIso (Iso.refl _)
          (nilPositiveTailSummandIso (W := W) p d)).inv ≫
        (eqToIso (summandModule_succ
          (nilPositiveDegreeProfile (W := W) p d))).inv).hom) := by
  unfold nilPositiveSummandIso
  simp only [Iso.trans_inv]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, ModuleCat.comp_apply]
  rw [E.evaluateWord_castWord_inv_apply]
  rw [E.evaluateWord_succ_eq]
  rfl

/-- Evaluation of a normalized zero-left/positive-right pure head/tail tensor. -/
theorem evaluateWord_nil_positive_apply_tensor
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule (nilPositiveDegreeProfile (W := W) p d) 0)
    (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        ((nil W X).append
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y))
        ((nilDegreeProfile W X p).append d)
        ((nilPositiveSummandIso (W := W) p d).inv.hom (x ⊗ₜ[ℤ] t)) =
      E.composeElement W (intermediate 0).obj Y
        (-1 + (nilPositiveDegreeProfile (W := W) p d).arrowDegree 0)
        (tailDegree (nilPositiveDegreeProfile (W := W) p d)) (p + n)
        (tailDegree_add_neg_one_add_head
          (nilPositiveDegreeProfile (W := W) p d))
        (E.firstContractionMap (nilPositiveDegreeProfile (W := W) p d) x)
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d))
          ((nilPositiveTailSummandIso (W := W) p d).inv.hom t)) := by
  have hmap := LinearMap.congr_fun
    (E.evaluateWord_nil_positive_coordinates (W := W) p d) (x ⊗ₜ[ℤ] t)
  simp only [LinearMap.comp_apply, ModuleCat.comp_apply,
    MonoidalCategory.tensorIso_inv, Iso.refl_inv, eqToIso.inv,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hmap
  rw [E.evaluateSucc_apply_tensor] at hmap
  exact hmap

/-- Tail evaluation in normalized zero-left/positive-right coordinates is the original tail
evaluation after the canonical output-degree transport. -/
theorem evaluateWord_nil_positive_tail
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (t : summandModule (tailDegreeProfile d)) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom (intermediate 0).obj Y).X q)
      (nilPositiveTailDegree_eq (W := W) p d))).hom
        (E.evaluateWord (tailWord (Y := Y) intermediate)
          (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d))
          ((nilPositiveTailSummandIso (W := W) p d).inv.hom t)) =
      E.evaluateWord (tailWord (Y := Y) intermediate)
        (tailDegreeProfile d) t := by
  let hn := nilPositiveTailDegree_eq (W := W) p d
  let q := tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d)
  let hp := nilPositiveTailProfile_eq (W := W) p d
  let t' : summandModule (nilPositiveTailProfile (W := W) p d) :=
    (eqToIso (congrArg summandModule hp)).inv.hom t
  let x : summandModule q :=
    (summandModuleTransportIso rfl hn q).inv.hom t'
  have htransport := E.evaluateWord_transport_apply rfl hn q x
  have hcancel := ConcreteCategory.congr_hom
    (summandModuleTransportIso rfl hn q).inv_hom_id t'
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  have hcancel' :
      (eqToHom (summandModuleTransportEq rfl hn q)).hom x = t' := by
    dsimp [x]
    simpa only [summandModuleTransportIso, eqToIso.hom, eqToIso.inv] using hcancel
  rw [hcancel'] at htransport
  have hprofile := E.evaluateWord_profile_eq_apply hp t'
  have hprofileCancel := ConcreteCategory.congr_hom
    (eqToIso (congrArg summandModule hp)).inv_hom_id t
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hprofileCancel
  have hprofileCancel' :
      (eqToHom (congrArg summandModule hp)).hom t' = t := by
    dsimp [t']
    simpa only [eqToIso.hom, eqToIso.inv] using hprofileCancel
  rw [hprofileCancel'] at hprofile
  have hx : x = (nilPositiveTailSummandIso (W := W) p d).inv.hom t := by
    rfl
  rw [← hx]
  exact htransport.symm.trans hprofile.symm

/-- In original positive-word coordinates, evaluation of a normalized zero-left/positive-right
pure tensor is composition of the zero-word image with the original positive-word evaluation. -/
theorem evaluateWord_nil_positive_apply_tensor_normalized
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : (dgHomZModuleCochainComplex W X).X p)
    (y : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        ((nil W X).append
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y))
        ((nilDegreeProfile W X p).append d)
        ((nilPositiveSummandIso (W := W) p d).inv.hom
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
              ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ]
            t)) =
      E.composeElement W X Y p n (p + n)
        (wordEvaluationCompositionDegreeEq p n)
        (E.factorMap W X p x)
        (E.evaluateWord
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          ((eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t))) := by
  rw [E.evaluateWord_nil_positive_apply_tensor (W := W) p d]
  have hcast := E.composeElement_cast_inputs_output W (intermediate 0).obj Y
    (nilPositiveContractedHeadDegreeEq (W := W) p d)
    (nilPositiveTailDegree_eq (W := W) p d) rfl
    (tailDegree_add_neg_one_add_head
      (nilPositiveDegreeProfile (W := W) p d))
    (show tailDegree d + ((-1 + d.arrowDegree 0) + p) = p + n by
      have hd := tailDegree_add_neg_one_add_head d
      omega)
    (E.firstContractionMap (nilPositiveDegreeProfile (W := W) p d)
      ((nilPositiveHeadCompositionMap (W := W) p d).hom
        ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y)))
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile (nilPositiveDegreeProfile (W := W) p d))
      ((nilPositiveTailSummandIso (W := W) p d).inv.hom t))
  rw [E.firstContractionMap_nil_positive_head (W := W) p d x y,
    E.evaluateWord_nil_positive_tail (W := W) p d t] at hcast
  simp only [eqToHom_refl, CategoryTheory.id_apply] at hcast
  have hdValue := E.evaluateWord_succ_apply_tensor_of_coordinates
    d rfl rfl y t
  have hassoc := E.composeElement_assoc_of_degree_eq W X (intermediate 0).obj Y
    rfl
    (show tailDegree d + ((-1 + d.arrowDegree 0) + p) = p + n by
      have hd := tailDegree_add_neg_one_add_head d
      omega)
    (tailDegree_add_neg_one_add_head d)
    (wordEvaluationCompositionDegreeEq p n)
    (E.factorMap W X p x) (E.firstContractionMap d y)
    (E.evaluateWord (tailWord (Y := Y) intermediate)
      (tailDegreeProfile d) t)
  rw [hdValue]
  exact hcast.trans hassoc

/-- Corrected word evaluation is multiplicative for a zero-length left word and a positive
right word, on canonical pure head/tail coordinates. -/
theorem evaluateWord_multiplicative_nil_positive
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : (dgHomZModuleCochainComplex W X).X p)
    (y : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    E.evaluateWord
        ((nil W X).append
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y))
        ((nilDegreeProfile W X p).append d)
        ((summandCompositionMap (nilDegreeProfile W X p) d).hom
          ((nilSummandIsoOriginal W X (nilDegreeProfile W X p)).inv.hom x ⊗ₜ[ℤ]
            (eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t))) =
      E.composeElement W X Y p n (p + n)
        (wordEvaluationCompositionDegreeEq p n)
        (E.factorMap W X p x)
        (E.evaluateWord
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          ((eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t))) := by
  let rightValue :=
    (eqToHom (summandModule_succ d).symm).hom (y ⊗ₜ[ℤ] t)
  let composed :=
    (summandCompositionMap (nilDegreeProfile W X p) d).hom
      ((nilSummandIsoOriginal W X (nilDegreeProfile W X p)).inv.hom x ⊗ₜ[ℤ]
        rightValue)
  have hcoordinates := summandCompositionMap_nil_positive_apply_tensor
    (W := W) p d x y t
  have hcancel := ConcreteCategory.congr_hom
    (nilPositiveSummandIso (W := W) p d).hom_inv_id composed
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  have hinput :
      composed =
        (nilPositiveSummandIso (W := W) p d).inv.hom
          ((nilPositiveHeadCompositionMap (W := W) p d).hom
              ((eqToHom (factorModule_nilDegreeProfile W X p).symm).hom x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ]
            t) := by
    exact hcancel.symm.trans (congrArg
      (nilPositiveSummandIso (W := W) p d).inv.hom hcoordinates)
  change E.evaluateWord
      ((nil W X).append
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y))
      ((nilDegreeProfile W X p).append d) composed = _
  rw [hinput]
  exact E.evaluateWord_nil_positive_apply_tensor_normalized (W := W) p d x y t

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
