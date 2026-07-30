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

@[simp]
theorem quotientWordElement_zero
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    quotientWordElement w d 0 = 0 := by
  unfold quotientWordElement
  apply ULift.down_injective
  have hup : (ULift.up (0 : summandModule d) : ULift (summandModule d)) = 0 := rfl
  rw [hup, map_zero]
  rfl

@[simp]
theorem quotientWordElement_add
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (x y : summandModule d) :
    quotientWordElement w d (x + y) =
      quotientWordElement w d x + quotientWordElement w d y := by
  unfold quotientWordElement
  apply ULift.down_injective
  have hup : (ULift.up (x + y) : ULift (summandModule d)) =
      ULift.up x + ULift.up y := rfl
  rw [hup, map_add]
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

set_option maxHeartbeats 8000000 in
-- Reassociating the dependent head/contraction/tail coordinates is elaboration-heavy.
/-- A canonical positive-word element is the transported quotient element of its explicit
head/formal-contraction/tail composition. -/
theorem quotientWordElement_positiveTensorSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    quotientWordElement
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
        (AnnihilatingEnrichedFunctorData.positiveTensorSummand d x t) =
      (eqToHom (congrArg
        (fun r ↦ (quotientCoefficientCochainComplex X Y).X r)
        (show (d.arrowDegree 0 + (-1)) +
            (n - d.arrowDegree 0 + 1) = n by omega))).hom
        (quotientWordElement
          (((nil X (intermediate 0).obj).append
            (singleton (intermediate 0).obj (intermediate 0).obj
              (intermediate 0))).append (tailWord (Y := Y) intermediate))
          (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d)
          (AnnihilatingEnrichedFunctorData.positiveComposedRawSummand d x t)) := by
  rw [← AnnihilatingEnrichedFunctorData.positiveComposedSummand_eq_positiveTensorSummand]
  exact quotientWordElement_positiveRawSummandIso d
    (AnnihilatingEnrichedFunctorData.positiveComposedRawSummand d x t)

/-- The raw head/formal-contraction/tail quotient element is obtained by the two corresponding
homogeneous quotient compositions. -/
theorem quotientWordElement_positiveComposedRawSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    quotientWordElement
        (((nil X (intermediate 0).obj).append
          (singleton (intermediate 0).obj (intermediate 0).obj
            (intermediate 0))).append (tailWord (Y := Y) intermediate))
        (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d)
        (AnnihilatingEnrichedFunctorData.positiveComposedRawSummand d x t) =
      (quotientDGCompositionComponent X (intermediate 0).obj Y
        (show (n - d.arrowDegree 0 + 1) +
            (d.arrowDegree 0 + (-1)) =
              (d.arrowDegree 0 + (-1)) + (n - d.arrowDegree 0 + 1) by omega)).hom
        (quotientWordElement (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t ⊗ₜ[QuotientCoefficientRing]
          (quotientDGCompositionComponent X (intermediate 0).obj
            (intermediate 0).obj (Int.add_comm (-1) (d.arrowDegree 0))).hom
            (quotientWordElement
                (singleton (intermediate 0).obj (intermediate 0).obj (intermediate 0))
                (singletonContractingDegreeProfile (intermediate 0))
                (singletonContractingElement (intermediate 0)) ⊗ₜ[QuotientCoefficientRing]
              quotientWordElement (nil X (intermediate 0).obj)
                (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
                (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x))) := by
  rw [quotientDGCompositionComponent_quotientWordElement]
  rw [quotientDGCompositionComponent_quotientWordElement]
  rfl

namespace EnrichedFunctor

/-- A cochain map is natural under equality transport of its degree index. -/
theorem map_eqToHom_degree
    {C E : QuotientDGCochain} (f : C ⟶ E)
    {p q : ℤ} (h : p = q) (z : C.X p) :
    f.f q ((eqToHom (congrArg (fun r ↦ C.X r) h)).hom z) =
      (eqToHom (congrArg (fun r ↦ E.X r) h)).hom (f.f p z) := by
  subst q
  rfl

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

set_option maxHeartbeats 8000000 in
-- The induction step compares two nested enriched compositions across dependent degree casts.
/-- If evaluation after restriction agrees with a quotient-enriched functor on the positive tail,
then it agrees on a pure head/tail tensor for the full positive word. -/
theorem restriction_evaluateWord_positive_tensor
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d))
    (htail :
      (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord
          (tailWord (Y := Y) intermediate) (tailDegreeProfile d) t =
        (G.map (Opposite.op Y) (Opposite.op (intermediate 0).obj)).f
          (AnnihilatingEnrichedFunctorData.tailDegree d)
          (quotientWordElement (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t)) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
        (AnnihilatingEnrichedFunctorData.positiveTensorSummand d x t) =
      (G.map (Opposite.op Y) (Opposite.op X)).f n
        (quotientWordElement
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          (AnnihilatingEnrichedFunctorData.positiveTensorSummand d x t)) := by
  let E := AnnihilatingEnrichedFunctorData.restriction G
  let a := d.arrowDegree 0
  let q := AnnihilatingEnrichedFunctorData.tailDegree d
  let hn : (d.arrowDegree 0 + (-1)) +
      (n - d.arrowDegree 0 + 1) = n := by omega
  rw [quotientWordElement_positiveTensorSummand d x t]
  change _ = (G.map (Opposite.op Y) (Opposite.op X)).f n
    ((eqToHom (congrArg
      (fun r ↦ (quotientCoefficientCochainComplex X Y).X r) hn)).hom
      (quotientWordElement
        (((nil X (intermediate 0).obj).append
          (singleton (intermediate 0).obj (intermediate 0).obj
            (intermediate 0))).append (tailWord (Y := Y) intermediate))
        (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d)
        (AnnihilatingEnrichedFunctorData.positiveComposedRawSummand d x t)))
  let rawElement := quotientWordElement
    (((nil X (intermediate 0).obj).append
      (singleton (intermediate 0).obj (intermediate 0).obj
        (intermediate 0))).append (tailWord (Y := Y) intermediate))
    (AnnihilatingEnrichedFunctorData.positiveRawDegreeProfile d)
    (AnnihilatingEnrichedFunctorData.positiveComposedRawSummand d x t)
  have hcast := map_eqToHom_degree
    (G.map (Opposite.op Y) (Opposite.op X)) hn rawElement
  change _ = (G.map (Opposite.op Y) (Opposite.op X)).f n
    ((eqToHom (congrArg
      (fun r ↦ (quotientCoefficientCochainComplex X Y).X r) hn)).hom rawElement)
  apply Eq.trans ?_ hcast.symm
  dsimp [rawElement]
  rw [quotientWordElement_positiveComposedRawSummand d x t]
  unfold AnnihilatingEnrichedFunctorData.positiveTensorSummand
  rw [AnnihilatingEnrichedFunctorData.evaluateWord_succ_apply_tensor_of_coordinates
    (AnnihilatingEnrichedFunctorData.restriction G) d rfl rfl x t]
  simp only [eqToHom_refl, CategoryTheory.id_apply]
  rw [htail]
  let A := intermediate 0
  let headElement := quotientWordElement (nil X A.obj)
    (nilDegreeProfile X A.obj a)
    (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x)
  let contractionElement := quotientWordElement (singleton A.obj A.obj A)
    (singletonContractingDegreeProfile A) (singletonContractingElement A)
  let headContractionElement :=
    (quotientDGCompositionComponent X A.obj A.obj (Int.add_comm (-1) a)).hom
      (contractionElement ⊗ₜ[QuotientCoefficientRing] headElement)
  let tailElement := quotientWordElement (tailWord (Y := Y) intermediate)
    (tailDegreeProfile d) t
  let houter : q + (a + (-1)) = (a + (-1)) + q := Int.add_comm _ _
  have houterMap := map_quotientCompositionElement G X A.obj Y
    (a + (-1)) q ((a + (-1)) + q) houter headContractionElement tailElement
  change E.composeElement X A.obj Y (-1 + a) q n
      (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
      (E.firstContractionMap d x)
      ((G.map (Opposite.op Y) (Opposite.op A.obj)).f q tailElement) =
    (eqToHom (congrArg (fun r ↦ (E.hom X Y).X r) hn)).hom
      ((G.map (Opposite.op Y) (Opposite.op X)).f ((a + (-1)) + q)
        ((quotientDGCompositionComponent X A.obj Y houter).hom
          (tailElement ⊗ₜ[QuotientCoefficientRing] headContractionElement)))
  rw [houterMap]
  let hp : a + (-1) = -1 + a := Int.add_comm _ _
  have hhead : headContractionElement =
      quotientWordElement
        ((nil X A.obj).append (singleton A.obj A.obj A))
        ((nilDegreeProfile X A.obj a).append
          (singletonContractingDegreeProfile A))
        ((summandCompositionMap (nilDegreeProfile X A.obj a)
          (singletonContractingDegreeProfile A)).hom
            (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x ⊗ₜ[ℤ]
              singletonContractingElement A)) := by
    dsimp [headContractionElement, contractionElement, headElement]
    exact quotientDGCompositionComponent_quotientWordElement
      (nilDegreeProfile X A.obj a) (singletonContractingDegreeProfile A)
      (AnnihilatingEnrichedFunctorData.positiveHeadSummandElement d x)
      (singletonContractingElement A)
  have hfirst0 := restriction_firstContractionMap_cast G d x
  have hfirst :
      (eqToHom (congrArg (fun r ↦ (E.hom X A.obj).X r)
        (Int.add_comm (-1) a))).hom (E.firstContractionMap d x) =
        (G.map (Opposite.op A.obj) (Opposite.op X)).f (a + (-1))
          headContractionElement := by
    simpa [E, A, a] using hfirst0.trans
      (congrArg
        (fun z ↦ (G.map (Opposite.op A.obj) (Opposite.op X)).f (a + (-1)) z)
        hhead.symm)
  have hfirstBack :
      (eqToHom (congrArg (fun r ↦ (E.hom X A.obj).X r) hp)).hom
          ((G.map (Opposite.op A.obj) (Opposite.op X)).f (a + (-1))
            headContractionElement) =
        E.firstContractionMap d x := by
    rw [← hfirst]
    have hcancel := ConcreteCategory.congr_hom
      (eqToIso (congrArg (fun r ↦ (E.hom X A.obj).X r)
        (Int.add_comm (-1) a))).hom_inv_id
      (E.firstContractionMap d x)
    simpa only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
      CategoryTheory.id_apply] using hcancel
  have hcomposition := E.composeElement_cast_first_output X A.obj Y hp hn
    houter (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
    ((G.map (Opposite.op A.obj) (Opposite.op X)).f (a + (-1))
      headContractionElement)
    ((G.map (Opposite.op Y) (Opposite.op A.obj)).f q tailElement)
  rw [hfirstBack] at hcomposition
  exact hcomposition.symm

set_option maxHeartbeats 8000000 in
-- Tensor-product induction repeatedly unfolds dependent word coordinates and enriched maps.
/-- Evaluation after restriction agrees with the original quotient-enriched functor on every
summand of every word of a fixed length. -/
theorem restriction_evaluateWord_of_length
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    (k : ℕ) :
    ∀ {X Y : ComplexCategory}
      (intermediate : Fin k → CorrectedAcyclicComplexCategory)
      {n : ℤ}
      (d : DegreeProfile
        ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) n)
      (z : summandModule d),
      (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord
          ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) d z =
        (G.map (Opposite.op Y) (Opposite.op X)).f n
          (quotientWordElement
            ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) d z) := by
  induction k with
  | zero =>
      intro X Y intermediate n d z
      have hintermediate : intermediate =
          (Fin.elim0 : Fin 0 → CorrectedAcyclicComplexCategory) :=
        Subsingleton.elim _ _
      subst intermediate
      exact restriction_evaluateWord_nil G X Y n d z
  | succ k ih =>
      intro X Y intermediate n d z
      let u := (eqToHom (AnnihilatingEnrichedFunctorData.summandModule_succ d)).hom z
      have hz := ConcreteCategory.congr_hom
        (eqToIso (AnnihilatingEnrichedFunctorData.summandModule_succ d)).hom_inv_id z
      simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
        CategoryTheory.id_apply] at hz
      rw [← hz]
      change
        (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord
            ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
            ((eqToHom
              (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom u) =
          (G.map (Opposite.op Y) (Opposite.op X)).f n
            (quotientWordElement
              ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
              ((eqToHom
                (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom u))
      refine TensorProduct.induction_on u ?_ ?_ ?_
      · simp only [map_zero, quotientWordElement_zero]
      · intro x t
        apply restriction_evaluateWord_positive_tensor G d x t
        exact ih (X := (intermediate 0).obj) (Y := Y)
          (fun i ↦ intermediate i.succ)
          (tailDegreeProfile d) t
      · intro a b ha hb
        simp only [map_add]
        rw [quotientWordElement_add]
        rw [map_add]
        exact congrArg₂ (· + ·) ha hb

/-- Evaluation after restriction agrees with the original quotient-enriched functor on every
corrected Drinfeld word summand. -/
theorem restriction_evaluateWord
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D)
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (z : summandModule d) :
    (AnnihilatingEnrichedFunctorData.restriction G).evaluateWord w d z =
      (G.map (Opposite.op Y) (Opposite.op X)).f n
        (quotientWordElement w d z) := by
  exact restriction_evaluateWord_of_length G w.length w.intermediate d z

end EnrichedFunctor

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
