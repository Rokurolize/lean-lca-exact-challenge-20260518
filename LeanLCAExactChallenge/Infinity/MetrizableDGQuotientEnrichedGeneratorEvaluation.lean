/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedRoundTrip

/-! # Generator evaluation for enriched quotient functors

This file starts the reverse direction of the corrected Drinfeld quotient's enriched universal
property. It packages a homogeneous word summand as its canonical element of the coefficient-
changed quotient, proves that quotient composition appends represented words, proves that every
quotient-enriched functor preserves this homogeneous composition on elements, and establishes the
zero-word base case for evaluation after restriction.
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

/-- The coefficient-changed quotient element represented by one homogeneous word summand. -/
def quotientWordElement
    {X Y : ComplexCategory} {n : ℤ}
    (w : DrinfeldWord X Y) (d : DegreeProfile w n)
    (x : summandModule d) :
    (quotientCoefficientCochainComplex X Y).X n :=
  ULift.up
    ((Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom
        (ULift.up x))

set_option maxHeartbeats 4000000 in
-- Normalizing the coefficient-changed output transport unfolds the full Sigma summand index.
/-- Quotient composition of two represented word summands is the represented appended summand. -/
theorem quotientDGCompositionComponent_quotientWordElement
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : summandModule d) (y : summandModule e) :
    (quotientDGCompositionComponent X Y Z (Int.add_comm m n)).hom
        (quotientWordElement v e y ⊗ₜ[QuotientCoefficientRing]
          quotientWordElement w d x) =
      quotientWordElement (w.append v) (d.append e)
        ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] y)) := by
  unfold quotientWordElement quotientDGCompositionComponent
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  change
    (eqToHom (congrArg
      (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
      ((Int.add_comm n m).trans (Int.add_comm m n)))).hom
        ((quotientCompositionTensorMap X Y Z n m).hom
          (ULift.up
              ((Limits.Sigma.ι
                (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
                ⟨w, d⟩).hom (ULift.up x)) ⊗ₜ[QuotientCoefficientRing]
            ULift.up
              ((Limits.Sigma.ι
                (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
                ⟨v, e⟩).hom (ULift.up y)))) =
      ULift.up
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z (n + m) ↦ largeSummandModule s)
          ⟨w.append v, d.append e⟩).hom
            (ULift.up ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] y))))
  have hdegree :
      ((Int.add_comm n m).trans (Int.add_comm m n)) =
        (rfl : n + m = n + m) := Subsingleton.elim _ _
  rw [hdegree]
  simp only [eqToHom_refl]
  rw [quotientCompositionTensorMap_tmul]
  apply congrArg ULift.up
  rw [quotientCompositionMap_on_summands]
  rfl

namespace EnrichedFunctor

set_option maxHeartbeats 4000000 in
-- Expanding enriched composition through the quotient's total-complex component is costly.
/-- A quotient-enriched functor preserves homogeneous quotient composition on elements. -/
theorem map_quotientCompositionElement
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : q + p = n)
    (x : (quotientCoefficientCochainComplex X Y).X p)
    (y : (quotientCoefficientCochainComplex Y Z).X q) :
    (G.map (Opposite.op Z) (Opposite.op X)).f n
        ((quotientDGCompositionComponent X Y Z h).hom
          (y ⊗ₜ[QuotientCoefficientRing] x)) =
      (AnnihilatingEnrichedFunctorData.restriction G).composeElement
        X Y Z p q n h
          ((G.map (Opposite.op Y) (Opposite.op X)).f p x)
          ((G.map (Opposite.op Z) (Opposite.op Y)).f q y) := by
  let K : CorrectedQuotientDGCategory := Opposite.op Z
  let L : CorrectedQuotientDGCategory := Opposite.op Y
  let M : CorrectedQuotientDGCategory := Opposite.op X
  let ι := HomologicalComplex.ιTensorObj
    (K ⟶[QuotientDGCochain] L) (L ⟶[QuotientDGCochain] M) q p n h
  have hmap := congrArg (fun f ↦ f.f n) (G.map_comp K L M)
  have hpre := congrArg (fun f ↦ ι ≫ f) hmap
  simp only [HomologicalComplex.comp_f] at hpre
  change
    HomologicalComplex.ιTensorObj
          (quotientCoefficientCochainComplex Y Z)
          (quotientCoefficientCochainComplex X Y) q p n h ≫
        (quotientDGComposition X Y Z).f n ≫
        (G.map (Opposite.op Z) (Opposite.op X)).f n =
      HomologicalComplex.ιTensorObj
          (quotientCoefficientCochainComplex Y Z)
          (quotientCoefficientCochainComplex X Y) q p n h ≫
        (G.map (Opposite.op Z) (Opposite.op Y) ⊗ₘ
          G.map (Opposite.op Y) (Opposite.op X)).f n ≫
        (eComp QuotientDGCochain
          (G.obj (Opposite.op Z)) (G.obj (Opposite.op Y))
          (G.obj (Opposite.op X))).f n at hpre
  rw [ιTensorObj_quotientDGComposition_assoc X Y Z h] at hpre
  have htensor :
      HomologicalComplex.ιTensorObj
            (quotientCoefficientCochainComplex Y Z)
            (quotientCoefficientCochainComplex X Y) q p n h ≫
          (G.map (Opposite.op Z) (Opposite.op Y) ⊗ₘ
            G.map (Opposite.op Y) (Opposite.op X)).f n =
        ((G.map (Opposite.op Z) (Opposite.op Y)).f q ⊗ₘ
            (G.map (Opposite.op Y) (Opposite.op X)).f p) ≫
          HomologicalComplex.ιTensorObj
            (G.obj (Opposite.op Z) ⟶[QuotientDGCochain]
              G.obj (Opposite.op Y))
            (G.obj (Opposite.op Y) ⟶[QuotientDGCochain]
              G.obj (Opposite.op X)) q p n h := by
    exact GradedObject.Monoidal.ι_tensorHom
      (G.map (Opposite.op Z) (Opposite.op Y)).f
      (G.map (Opposite.op Y) (Opposite.op X)).f q p n h
  rw [← Category.assoc, htensor, Category.assoc] at hpre
  have happ := ConcreteCategory.congr_hom hpre
    (y ⊗ₜ[QuotientCoefficientRing] x)
  simp only [ModuleCat.comp_apply] at happ
  exact happ

set_option maxHeartbeats 2000000 in
-- Cancelling the nil-summand isomorphism crosses both universe lifts and the Sigma inclusion.
/-- For a restricted quotient-enriched functor, zero-length word evaluation is the original
quotient map on the represented summand. -/
theorem restriction_evaluateWord_nil
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (X Y : ComplexCategory) (n : ℤ)
    (d : DegreeProfile (nil X Y) n) (x : summandModule d) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord
        (nil X Y) d x =
      (G.map (Opposite.op Y) (Opposite.op X)).f n
        (quotientWordElement (nil X Y) d x) := by
  have hd := AnnihilatingEnrichedFunctorData.degreeProfile_nil_eq d
  subst d
  rw [(AnnihilatingEnrichedFunctorData.restriction G).evaluateWord_nil_apply]
  unfold AnnihilatingEnrichedFunctorData.evaluateNilProfile
    AnnihilatingEnrichedFunctorData.factorMap
  simp only [LinearMap.comp_apply]
  change (G.map (Opposite.op Y) (Opposite.op X)).f n
      (((OriginalCoefficientHomToQuotient X Y).f n).hom
        (ULift.up (ULift.up
          ((nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).hom.hom x)))) = _
  rw [OriginalCoefficientHomToQuotient_apply_up]
  rw [originalHomInclusion_apply_up]
  have hcancel := ConcreteCategory.congr_hom
    (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).hom_inv_id x
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  rw [hcancel]
  rfl

end EnrichedFunctor

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
