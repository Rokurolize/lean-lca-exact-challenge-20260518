/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedGeneratorEvaluation

/-!
# Positive-word uniqueness for corrected quotient enriched functors

This file identifies the canonical positive-word generators under restriction of an arbitrary
quotient-enriched functor. These transport and head-contraction formulas are the coordinate input
for the extension-after-restriction uniqueness induction.
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

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]

/-- Canonical quotient word elements are natural under simultaneous word/degree transport. -/
theorem quotientWordElement_transport
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n)
    (x : summandModule d) :
    (eqToHom (congrArg
      (fun r ↦ (quotientCoefficientCochainComplex X Y).X r) hn)).hom
        (quotientWordElement w d x) =
      quotientWordElement v (d.transport hw hn)
        ((eqToHom (summandModuleTransportEq hw hn d)).hom x) := by
  subst v
  subst m
  rfl

/-- Canonical quotient word elements are natural under equality of degree profiles. -/
theorem quotientWordElement_profile_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    {d e : DegreeProfile w n} (h : d = e) (x : summandModule d) :
    quotientWordElement w e ((eqToHom (congrArg summandModule h)).hom x) =
      quotientWordElement w d x := by
  cases h
  rfl

set_option maxHeartbeats 8000000 in
-- The dependent word/profile transport normalization requires an enlarged elaboration budget.
theorem quotientWordElement_positiveRawSummandIso
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (u : summandModule
      (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d)) :
    quotientWordElement
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
        ((AnnihilatingEnrichedFunctorData.positiveRawSummandIso d).hom u) =
      (eqToHom (congrArg
        (fun r ↦ (quotientCoefficientCochainComplex X Y).X r)
        (show (d.arrowDegree 0 + (-1)) +
            (n - d.arrowDegree 0 + 1) = n by omega))).hom
        (quotientWordElement
          (((nil X (intermediate 0).obj).append
            (singleton (intermediate 0).obj (intermediate 0).obj
              (intermediate 0))).append (tailWord (Y := Y) intermediate))
          (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d) u) := by
  let hw := AnnihilatingEnrichedFunctorData.positiveWord_eq_head_contraction_tail
    (X := X) (Y := Y) intermediate
  let hn : (d.arrowDegree 0 + (-1)) +
      (n - d.arrowDegree 0 + 1) = n := by omega
  let raw := AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d
  have htransport := quotientWordElement_transport hw hn raw u
  have hprofile := AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile_transport d
  have hprofileElement := quotientWordElement_profile_eq hprofile
    ((eqToHom (summandModuleTransportEq hw hn raw)).hom u)
  have hresult := hprofileElement.trans htransport.symm
  change quotientWordElement
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
      (((summandModuleTransportIso hw hn raw).hom ≫
        eqToHom (congrArg summandModule hprofile)).hom u) = _
  exact hresult

namespace EnrichedFunctor

set_option maxHeartbeats 4000000 in
-- Cancelling the nil-summand transport crosses the coefficient-change and quotient inclusions.
theorem restriction_firstFactorMap
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    (AnnihilatingEnrichedFunctorData.restriction G).firstFactorMap d x =
      (G.map (Opposite.op (intermediate 0).obj) (Opposite.op X)).f
        (d.arrowDegree 0)
        (quotientWordElement
          (nil X (intermediate 0).obj)
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x)) := by
  rw [← restriction_evaluateWord_nil G X (intermediate 0).obj
    (d.arrowDegree 0)
    (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
    (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x)]
  rw [(AnnihilatingEnrichedFunctorData.restriction G).evaluateWord_nil_apply]
  unfold AnnihilatingEnrichedFunctorData.evaluateNilProfile
    AnnihilatingEnrichedFunctorData.firstFactorMap
    AnnihilatingEnrichedFunctorData.positiveHeadSummandElement
  simp only [LinearMap.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (nilSummandIsoOriginal X (intermediate 0).obj
      (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))).inv_hom_id
    ((eqToHom (AnnihilatingEnrichedFunctorData.factorModule_zero_succ d)).hom x)
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  rw [hcancel]

theorem restriction_contraction_quotientWordElement
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (A : CorrectedAcyclicComplexCategory) :
    (AnnihilatingEnrichedFunctorData.restriction G).contraction A =
      (G.map (Opposite.op A.obj) (Opposite.op A.obj)).f (-1)
        (quotientWordElement (singleton A.obj A.obj A)
          (singletonContractingDegreeProfile A) (singletonContractingElement A)) := by
  rfl

set_option maxHeartbeats 8000000 in
-- The enriched composition comparison expands both tensor inclusions and dependent degree casts.
theorem restriction_firstContractionMap_cast
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    (eqToHom (congrArg
      (fun r ↦ ((AnnihilatingEnrichedFunctorData.restriction G).hom
        X (intermediate 0).obj).X r)
      (Int.add_comm (-1) (d.arrowDegree 0)))).hom
        ((AnnihilatingEnrichedFunctorData.restriction G).firstContractionMap d x) =
      (G.map (Opposite.op (intermediate 0).obj) (Opposite.op X)).f
        (d.arrowDegree 0 + (-1))
        (quotientWordElement
          ((nil X (intermediate 0).obj).append
            (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0)))
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          ((summandCompositionMap
            (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
            (singletonContractingDegreeProfile (intermediate 0))).hom
              (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x ⊗ₜ[ℤ]
                singletonContractingElement (intermediate 0)))) := by
  let E := AnnihilatingEnrichedFunctorData.restriction G
  let a := d.arrowDegree 0
  let A := intermediate 0
  let headProfile := nilDegreeProfile X A.obj a
  let contractionProfile := singletonContractingDegreeProfile A
  let headElement :=
    AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x
  let contractionElement := singletonContractingElement A
  have hcast := E.composeElement_cast_output X A.obj A.obj
    a (-1) (-1 + a) (a + (-1)) rfl (Int.add_comm (-1) a)
    (E.firstFactorMap d x) (E.contraction A)
  unfold AnnihilatingEnrichedFunctorData.firstContractionMap
    AnnihilatingEnrichedFunctorData.composeFirstMap
  simp only [LinearMap.comp_apply]
  change
    (eqToHom (congrArg (fun r ↦ (E.hom X A.obj).X r)
      (Int.add_comm (-1) a))).hom
        (E.composeElement X A.obj A.obj a (-1) (-1 + a) rfl
          (E.firstFactorMap d x) (E.contraction A)) = _
  rw [hcast]
  rw [restriction_firstFactorMap G d x]
  rw [restriction_contraction_quotientWordElement G A]
  have hmap := map_quotientCompositionElement G X A.obj A.obj
    a (-1) (a + (-1)) (Int.add_comm (-1) a)
    (quotientWordElement (nil X A.obj) headProfile headElement)
    (quotientWordElement (singleton A.obj A.obj A)
      contractionProfile contractionElement)
  rw [← hmap]
  rw [quotientDGCompositionComponent_quotientWordElement
    headProfile contractionProfile headElement contractionElement]

end EnrichedFunctor

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
