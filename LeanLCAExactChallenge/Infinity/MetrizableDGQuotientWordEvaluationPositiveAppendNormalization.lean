/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationPositiveAppendRecursion

/-! # Normalized positive-append recursion for corrected Drinfeld word evaluation

This module rewrites the recursive evaluation of an appended positive word from the transported
positive-append profile back into the original head and appended-tail coordinates.  The resulting
formula is the induction-ready evaluation counterpart of recursive summand composition.
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

/-- The recursive tail degree of an appended positive profile is the original tail degree plus
the degree of the appended profile. -/
theorem positiveAppendDegreeProfile_tailDegree
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    tailDegree (positiveAppendDegreeProfile d e) = tailDegree d + m := by
  unfold tailDegree
  rw [positiveAppendDegreeProfile_arrowDegree_zero]
  omega

/-- The transported head degree of an appended positive profile is the original head degree. -/
def positiveAppendHeadDegreeEq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (positiveAppendDegreeProfile d e).arrowDegree 0 = d.arrowDegree 0 :=
  positiveAppendDegreeProfile_arrowDegree_zero d e

/-- The transported contracted-head degree of an appended positive profile is the original
contracted-head degree. -/
def positiveAppendContractedHeadDegreeEq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    -1 + (positiveAppendDegreeProfile d e).arrowDegree 0 =
      -1 + d.arrowDegree 0 :=
  congrArg (fun q : ℤ ↦ -1 + q) (positiveAppendHeadDegreeEq d e)

/-- The original-factor map of an appended positive profile is the original head-factor map
after the canonical input and output transports. -/
theorem firstFactorMap_positive_append
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (positiveAppendHeadDegreeEq d e))).hom
        (E.firstFactorMap (positiveAppendDegreeProfile d e)
          ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x)) =
      E.firstFactorMap d x := by
  unfold firstFactorMap
  simp only [LinearMap.comp_apply]
  simp only [positiveAppendIntermediate, Fin.cases_zero]
  rw [E.factorMap_cast_degree X (intermediate 0).obj
    (positiveAppendHeadDegreeEq d e)]
  let hdegree := congrArg
    (fun q ↦ (dgHomZModuleCochainComplex X (intermediate 0).obj).X q)
    (positiveAppendHeadDegreeEq d e)
  have hsource :
      (positiveAppendFactorModule_zero d e).symm.trans
          ((factorModule_zero_succ (positiveAppendDegreeProfile d e)).trans hdegree) =
        factorModule_zero_succ d := Subsingleton.elim _ _
  have hx :
      (eqToHom hdegree).hom
          ((eqToHom (factorModule_zero_succ (positiveAppendDegreeProfile d e))).hom
            ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x)) =
        (eqToHom (factorModule_zero_succ d)).hom x := by
    change ((eqToHom (positiveAppendFactorModule_zero d e).symm ≫
      eqToHom (factorModule_zero_succ (positiveAppendDegreeProfile d e)) ≫
      eqToHom hdegree).hom x) = _
    rw [eqToHom_trans, eqToHom_trans, hsource]
  exact congrArg (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)) hx

/-- The first contracted factor of an appended positive profile is the original contracted
head after the canonical output-degree transport. -/
theorem firstContractionMap_positive_append
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (positiveAppendContractedHeadDegreeEq d e))).hom
        (E.firstContractionMap (positiveAppendDegreeProfile d e)
          ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x)) =
      E.firstContractionMap d x := by
  unfold firstContractionMap composeFirstMap
  change (eqToHom (congrArg
      (fun q ↦ (E.hom X (intermediate 0).obj).X q)
      (positiveAppendContractedHeadDegreeEq d e))).hom
      (E.composeElement X (intermediate 0).obj (intermediate 0).obj
        ((positiveAppendDegreeProfile d e).arrowDegree 0) (-1)
        (-1 + (positiveAppendDegreeProfile d e).arrowDegree 0) rfl
        (E.firstFactorMap (positiveAppendDegreeProfile d e)
          ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x))
        (E.contraction (intermediate 0))) =
    E.composeElement X (intermediate 0).obj (intermediate 0).obj
      (d.arrowDegree 0) (-1) (-1 + d.arrowDegree 0) rfl
      (E.firstFactorMap d x) (E.contraction (intermediate 0))
  rw [E.composeElement_cast_first_output X (intermediate 0).obj
    (intermediate 0).obj
    (positiveAppendHeadDegreeEq d e)
    (positiveAppendContractedHeadDegreeEq d e)]
  rw [E.firstFactorMap_positive_append d e x]

/-- Evaluating the recursive tail of an appended positive profile agrees, after the canonical
output-degree transport, with evaluating the appended original tail profile. -/
theorem evaluateWord_positive_append_tail
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (t : summandModule ((tailDegreeProfile d).append e)) :
    (eqToHom (congrArg
      (fun q ↦ (E.hom (intermediate 0).obj Z).X q)
      (positiveAppendDegreeProfile_tailDegree d e))).hom
        (E.evaluateWord
          (tailWord (Y := Z)
            (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v))
          (tailDegreeProfile (positiveAppendDegreeProfile d e))
          ((positiveAppendTailSummandIso d e).inv.hom t)) =
      E.evaluateWord ((tailWord (Y := Y) intermediate).append v)
        ((tailDegreeProfile d).append e) t := by
  let hw := tailWord_positiveAppend intermediate v
  let hn := positiveAppendDegreeProfile_tailDegree d e
  let p := tailDegreeProfile (positiveAppendDegreeProfile d e)
  let hp := positiveAppendTailProfile_eq d e
  let t' : summandModule (positiveAppendTailProfile d e) :=
    (eqToIso (congrArg summandModule hp)).inv.hom t
  let x : summandModule p :=
    (summandModuleTransportIso hw hn p).inv.hom t'
  have htransport := E.evaluateWord_transport_apply hw hn p x
  have hcancel := ConcreteCategory.congr_hom
    (summandModuleTransportIso hw hn p).inv_hom_id t'
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  have hcancel' :
      (eqToHom (summandModuleTransportEq hw hn p)).hom x = t' := by
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
  have hx : x = (positiveAppendTailSummandIso d e).inv.hom t := by
    rfl
  rw [← hx]
  exact htransport.symm.trans hprofile.symm

/-- The normalized tail and contracted-head degrees of an appended positive profile add to the
total appended degree. -/
def positiveAppendNormalizedOutputDegreeEq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (_e : DegreeProfile v m) :
    (tailDegree d + m) + (-1 + d.arrowDegree 0) = n + m := by
  have hd := tailDegree_add_neg_one_add_head d
  omega

/-- In the original head/tail coordinates, evaluation of an appended positive word is target
composition of the original contracted head with evaluation of the appended original tail. -/
theorem evaluateWord_positive_append_apply_tensor_normalized
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m)
    (x : factorModule d 0)
    (t : summandModule ((tailDegreeProfile d).append e)) :
    E.evaluateWord
        (({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y).append v) (d.append e)
        ((positiveCompositionTargetIso d e).inv.hom (x ⊗ₜ[ℤ] t)) =
      E.composeElement X (intermediate 0).obj Z
        (-1 + d.arrowDegree 0) (tailDegree d + m) (n + m)
        (positiveAppendNormalizedOutputDegreeEq d e)
        (E.firstContractionMap d x)
        (E.evaluateWord ((tailWord (Y := Y) intermediate).append v)
          ((tailDegreeProfile d).append e) t) := by
  rw [E.evaluateWord_positive_append_apply_tensor d e x t]
  simp only [positiveAppendIntermediate, Fin.cases_zero]
  have hcast := E.composeElement_cast_inputs_output X (intermediate 0).obj Z
    (positiveAppendContractedHeadDegreeEq d e)
    (positiveAppendDegreeProfile_tailDegree d e) rfl
    (tailDegree_add_neg_one_add_head (positiveAppendDegreeProfile d e))
    (positiveAppendNormalizedOutputDegreeEq d e)
    (E.firstContractionMap (positiveAppendDegreeProfile d e)
      ((eqToIso (positiveAppendFactorModule_zero d e)).inv.hom x))
    (E.evaluateWord
      (tailWord (Y := Z)
        (positiveAppendIntermediate (Y := Y) (Z := Z) intermediate v))
      (tailDegreeProfile (positiveAppendDegreeProfile d e))
      ((positiveAppendTailSummandIso d e).inv.hom t))
  rw [E.firstContractionMap_positive_append d e x,
    E.evaluateWord_positive_append_tail d e t] at hcast
  simp only [eqToHom_refl, CategoryTheory.id_apply] at hcast
  exact hcast

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
