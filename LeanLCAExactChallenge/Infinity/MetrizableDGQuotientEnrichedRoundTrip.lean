/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedExtension

/-! # Restriction-extension round trip for corrected Drinfeld words

This file proves the first inverse law in the corrected quotient's enriched universal
property.  The word evaluator sends the quotient's distinguished formal contracting element
to the contraction supplied by an annihilating enriched functor.  Consequently, extending an
annihilating enriched functor across the corrected quotient and then restricting it recovers
the original functor and contraction data exactly.
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

/-- Composing the target identity with a homogeneous target element returns that element. -/
theorem composeIdentityElement
    (X Y : ComplexCategory) (q : ℤ) (y : (E.hom X Y).X q) :
    E.composeElement X X Y 0 q q (by omega)
        (targetDGIdentityElement (E.obj X)) y = y := by
  let B := E.hom X Y
  let μ := eComp QuotientDGCochain (E.obj Y) (E.obj X) (E.obj X)
  let η := eId QuotientDGCochain (E.obj X)
  have hunit := congrArg (fun f : B ⟶ B ↦ f.f q)
    (e_comp_id QuotientDGCochain (E.obj Y) (E.obj X))
  have happ := ConcreteCategory.congr_hom hunit y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at happ
  change (((HomologicalComplex.rightUnitor' B).inv q ≫ _) ≫ _) y = y at happ
  rw [HomologicalComplex.rightUnitor'_inv] at happ
  have hwhisker :
      (B ◁ η).f q = (HomologicalComplex.tensorHom (𝟙 B) η).f q := rfl
  rw [hwhisker] at happ
  simp only [Category.assoc, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at happ
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  let idB : B ⟶ B := 𝟙 B
  have hι := GradedObject.Monoidal.ι_tensorHom idB.f η.f q 0 q (by omega)
  have hιapp := ConcreteCategory.congr_hom hι
    (y ⊗ₜ[QuotientCoefficientRing] e.inv.hom (1 : QuotientCoefficientRing))
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιapp
  dsimp only [e] at hιapp
  have hιapp' :
      (HomologicalComplex.tensorHom (𝟙 B) η).f q
          ((HomologicalComplex.ιTensorObj B
            (HomologicalComplex.tensorUnit
              (ModuleCat.{1} QuotientCoefficientRing) (ComplexShape.up ℤ))
            q 0 q (by omega))
            (y ⊗ₜ[QuotientCoefficientRing]
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)) =
        (HomologicalComplex.ιTensorObj B
          (E.obj X ⟶[QuotientDGCochain] E.obj X) q 0 q (by omega))
          (y ⊗ₜ[QuotientCoefficientRing]
            η.f 0
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)) := by
    exact hιapp
  have hμ := congrArg (fun z ↦ μ.f q z) hιapp'
  have hright := hμ.symm.trans happ
  change E.composeElement X X Y 0 q q (by omega)
      (targetDGIdentityElement (E.obj X)) y = y at hright
  exact hright

/-- The original enriched functor sends the identity cochain to the target enriched identity. -/
theorem factorMap_identityCochain (X : ComplexCategory) :
    E.factorMap X X 0 (identityCochain X) =
      targetDGIdentityElement (E.obj X) := by
  let K : OriginalCoefficientDGCategory := Opposite.op X
  let one : (𝟙_ QuotientDGCochain).X 0 :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1
  have hsource : (eId QuotientDGCochain K).f 0 one =
      ULift.up (ULift.up (identityCochain X)) := by
    change (OriginalCoefficientDGIdentity X).f 0 one = _
    rw [OriginalCoefficientDGIdentity_f_zero]
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
    have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
      have h := ConcreteCategory.congr_hom e.inv_hom_id
        (1 : QuotientCoefficientRing)
      simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
    change (OriginalCoefficientDGIdentitySpan X).hom
        (e.hom.hom (e.inv.hom 1)) = _
    rw [hone]
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _
  have hid := E.functor.map_id K
  have hid0 := congrArg (fun f ↦ f.f 0) hid
  have happ := ConcreteCategory.congr_hom hid0 one
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at happ
  rw [hsource] at happ
  exact happ

/-- The first identity coordinate of the formal contracting generator. -/
private def singletonEvaluationHead (A : CorrectedAcyclicComplexCategory) :
    factorModule (singletonContractingDegreeProfile A) 0 :=
  (eqToHom (singletonContractingFactor_zero A).symm).hom
    (identityCochain A.obj)

/-- The zero-word tail identity coordinate of the formal contracting generator. -/
private def singletonEvaluationTail (A : CorrectedAcyclicComplexCategory) :
    summandModule (tailDegreeProfile (singletonContractingDegreeProfile A)) :=
  (ρ_ (factorModule (singletonContractingDegreeProfile A) 1)).inv.hom
    ((eqToHom (singletonContractingFactor_one A).symm).hom
      (identityCochain A.obj))

set_option maxHeartbeats 16000000 in
-- Reducing the singleton summand to recursive head/tail coordinates unfolds nested tensors.
private theorem singletonContractingElement_eq_head_tail
    (A : CorrectedAcyclicComplexCategory) :
    singletonContractingElement A =
      (eqToHom
        (summandModule_succ (singletonContractingDegreeProfile A)).symm).hom
        (singletonEvaluationHead A ⊗ₜ[ℤ] singletonEvaluationTail A) := by
  rfl

set_option maxHeartbeats 16000000 in
-- Normalizing the dependent transports from the singleton tail needs an enlarged budget.
private theorem singletonTailOriginalElement_evaluationTail
    (A : CorrectedAcyclicComplexCategory) :
    singletonTailOriginalElement A.obj A.obj A
        (singletonContractingDegreeProfile A) (singletonEvaluationTail A) =
      identityCochain A.obj := by
  unfold singletonTailOriginalElement singletonTailFactorElement
    singletonEvaluationTail
  simp only [ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply, one_smul]
  change (eqToHom (singletonFactorOneEqOriginal A.obj A.obj A
      (singletonContractingDegreeProfile A))).hom
      ((eqToHom (tailFactorModule (singletonContractingDegreeProfile A) 0)).hom
        ((eqToHom (singletonContractingFactor_one A).symm).hom
          (identityCochain A.obj))) = identityCochain A.obj
  have htail :
      tailFactorModule (singletonContractingDegreeProfile A) 0 = rfl :=
    Subsingleton.elim _ _
  rw [htail]
  have hout :
      singletonFactorOneEqOriginal A.obj A.obj A
          (singletonContractingDegreeProfile A) =
        singletonContractingFactor_one A :=
    Subsingleton.elim _ _
  rw [hout]
  exact (eqToIso (singletonContractingFactor_one A)).inv_hom_id_apply
    (identityCochain A.obj)

set_option maxHeartbeats 16000000 in
-- The zero-word cast and original-Hom coordinate comparison elaborate through several isos.
private theorem evaluateWord_singletonEvaluationTail
    (A : CorrectedAcyclicComplexCategory) :
    E.evaluateWord
        (tailWord (Y := A.obj) (fun _ : Fin 1 ↦ A))
        (tailDegreeProfile (singletonContractingDegreeProfile A))
        (singletonEvaluationTail A) =
      targetDGIdentityElement (E.obj A.obj) := by
  rw [E.evaluateWord_length_zero_apply rfl]
  unfold evaluateNilProfile
  have htail := singletonTailNilOriginalElement A.obj A.obj A
    (singletonContractingDegreeProfile A) (singletonEvaluationTail A)
  have htail' :
      (nilSummandIsoOriginal A.obj A.obj
        ((tailDegreeProfile (singletonContractingDegreeProfile A)).castWord
          (eq_nil_of_length_eq_zero
            (tailWord (Y := A.obj) (fun _ : Fin 1 ↦ A)) rfl))).hom.hom
          ((summandModuleCastWordIso
            (eq_nil_of_length_eq_zero
              (tailWord (Y := A.obj) (fun _ : Fin 1 ↦ A)) rfl)
            (tailDegreeProfile (singletonContractingDegreeProfile A))).hom.hom
              (singletonEvaluationTail A)) =
        identityCochain A.obj := by
    simpa [singletonTailWordEqNil,
      singletonTailOriginalElement_evaluationTail] using htail
  simp only [LinearMap.comp_apply]
  rw [htail']
  simpa [tailDegree, singletonContractingDegreeProfile] using
    E.factorMap_identityCochain A.obj

set_option maxHeartbeats 8000000 in
-- Unfolding the transported first singleton factor requires dependent type normalization.
private theorem firstFactorMap_singletonEvaluationHead
    (A : CorrectedAcyclicComplexCategory) :
    E.firstFactorMap (singletonContractingDegreeProfile A)
        (singletonEvaluationHead A) =
      targetDGIdentityElement (E.obj A.obj) := by
  unfold firstFactorMap singletonEvaluationHead
  change E.factorMap A.obj A.obj 0 (identityCochain A.obj) =
    targetDGIdentityElement (E.obj A.obj)
  exact E.factorMap_identityCochain A.obj

set_option maxHeartbeats 8000000 in
-- The recursive first-contraction map contains nested dependent degree transports.
private theorem firstContractionMap_singletonEvaluationHead
    (A : CorrectedAcyclicComplexCategory) :
    E.firstContractionMap (singletonContractingDegreeProfile A)
        (singletonEvaluationHead A) = E.contraction A := by
  unfold firstContractionMap composeFirstMap
  simp only [LinearMap.comp_apply]
  change E.composeElement A.obj A.obj A.obj 0 (-1) (-1) rfl
      (E.firstFactorMap (singletonContractingDegreeProfile A)
        (singletonEvaluationHead A)) (E.contraction A) = E.contraction A
  rw [E.firstFactorMap_singletonEvaluationHead A]
  simpa using
    E.composeIdentityElement A.obj A.obj (-1) (E.contraction A)

set_option maxHeartbeats 16000000 in
-- Evaluating the formal generator normalizes the full recursive singleton tensor expression.
/-- The corrected-word evaluator sends the formal contracting generator to the chosen
target contraction. -/
theorem evaluateWord_singletonContractingElement
    (A : CorrectedAcyclicComplexCategory) :
    E.evaluateWord (singleton A.obj A.obj A)
        (singletonContractingDegreeProfile A) (singletonContractingElement A) =
      E.contraction A := by
  rw [singletonContractingElement_eq_head_tail]
  rw [E.evaluateWord_succ_eq (singletonContractingDegreeProfile A)]
  rw [E.evaluateSucc_apply_tensor]
  rw [E.firstContractionMap_singletonEvaluationHead A]
  change E.composeElement A.obj A.obj A.obj (-1) 0 (-1) (by omega)
      (E.contraction A)
      (E.evaluateWord
        (tailWord (Y := A.obj) (fun _ : Fin 1 ↦ A))
        (tailDegreeProfile (singletonContractingDegreeProfile A))
        (singletonEvaluationTail A)) = E.contraction A
  rw [E.evaluateWord_singletonEvaluationTail A]
  simpa using
    E.composeElement_identity A.obj A.obj (-1) (E.contraction A)

set_option maxHeartbeats 8000000 in
-- Passing through ULift, Sigma inclusion, and coefficient change needs extra elaboration time.
/-- The cochain evaluator sends the quotient's formal contracting element to the chosen
target contraction. -/
theorem evaluateCochainMap_quotientContractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (E.evaluateCochainMap A.obj A.obj).f (-1)
        (ULift.up (quotientContractingElement A)) = E.contraction A := by
  change (E.evaluateCoefficientDegree A.obj A.obj (-1)).hom
      (ULift.up (quotientContractingElement A)) = E.contraction A
  unfold quotientContractingElement
  rw [E.evaluateCoefficientDegree_inclusion]
  exact E.evaluateWord_singletonContractingElement A

/-- Restricting the enriched extension recovers the original enriched functor. -/
theorem restriction_enrichedExtension_functor :
    (restriction E.enrichedExtension).functor = E.functor := by
  apply EnrichedFunctor.ext
    (F := (restriction E.enrichedExtension).functor) (G := E.functor)
    QuotientDGCochain (fun _ ↦ rfl)
  intro K L
  change OriginalCoefficientHomToQuotient L.unop K.unop ≫
      E.evaluateCochainMap L.unop K.unop = E.functor.map K L
  exact E.enrichedExtension_restricts K L

/-- Extensionality for annihilating enriched-functor data. -/
theorem ext_of_functor_and_contraction
    {E F : AnnihilatingEnrichedFunctorData D}
    (hfunctor : E.functor = F.functor)
    (hcontraction : HEq E.contraction F.contraction) : E = F := by
  cases E with
  | mk Efunctor Econtraction Edifferential =>
      cases F with
      | mk Ffunctor Fcontraction Fdifferential =>
          dsimp at hfunctor hcontraction
          cases hfunctor
          cases hcontraction
          rfl

/-- Restricting the enriched extension recovers the chosen contraction family. -/
theorem restriction_enrichedExtension_contraction :
    (restriction E.enrichedExtension).contraction = E.contraction := by
  funext A
  exact E.evaluateCochainMap_quotientContractingElement A

/-- Restriction after enriched extension is the identity on annihilating enriched-functor data. -/
theorem restriction_enrichedExtension :
    restriction E.enrichedExtension = E := by
  apply ext_of_functor_and_contraction
  · exact E.restriction_enrichedExtension_functor
  · exact heq_of_eq E.restriction_enrichedExtension_contraction

end AnnihilatingEnrichedFunctorData

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
