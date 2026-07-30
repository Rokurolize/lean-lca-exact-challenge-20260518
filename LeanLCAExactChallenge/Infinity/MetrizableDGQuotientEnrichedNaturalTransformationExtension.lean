/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientAnnihilatingFunctorCategory

/-! # Extension of annihilating enriched natural transformations -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open Opposite

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]

/-- Naturality of an annihilating transformation on one original homogeneous Hom factor. -/
theorem annihilatingFactorMap_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (X Y : ComplexCategory) (p : ℤ)
    (x : (dgHomZModuleCochainComplex X Y).X p) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        p 0 p (by omega)
        (E.factorMap X Y p x)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 p p (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.factorMap X Y p x) := by
  change quotientDGComposeElement
      (E.functor.obj (op Y)) (E.functor.obj (op X)) (F.functor.obj (op X))
      p 0 p (by omega)
      ((E.functor.map (op Y) (op X)).f p (ULift.up (ULift.up x)))
      (quotientDGUnitGradedNatTransElement α.hom (op X)) =
    quotientDGComposeElement
      (E.functor.obj (op Y)) (F.functor.obj (op Y)) (F.functor.obj (op X))
      0 p p (by omega)
      (quotientDGUnitGradedNatTransElement α.hom (op Y))
      ((F.functor.map (op Y) (op X)).f p (ULift.up (ULift.up x)))
  exact quotientDGUnitGradedNatTrans_naturality_element
    α.hom (op Y) (op X) p (ULift.up (ULift.up x))

/-- Naturality of the mapped first ordinary factor of a positive word. -/
theorem annihilatingFirstFactorMap_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    quotientDGComposeElement (E.obj (intermediate 0).obj) (E.obj X) (F.obj X)
        (d.arrowDegree 0) 0 (d.arrowDegree 0) (by omega)
        (E.firstFactorMap d x)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj (intermediate 0).obj)
        (F.obj (intermediate 0).obj) (F.obj X)
        0 (d.arrowDegree 0) (d.arrowDegree 0) (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op (intermediate 0).obj))
        (F.firstFactorMap d x) := by
  unfold AnnihilatingEnrichedFunctorData.firstFactorMap
  exact annihilatingFactorMap_naturality α X (intermediate 0).obj
    (d.arrowDegree 0)
    ((eqToHom (AnnihilatingEnrichedFunctorData.factorModule_zero_succ d)).hom x)

/-- Naturality of the first ordinary factor after composition with the selected contraction. -/
theorem annihilatingFirstContractionMap_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0) :
    quotientDGComposeElement (E.obj (intermediate 0).obj) (E.obj X) (F.obj X)
        (-1 + d.arrowDegree 0) 0 (-1 + d.arrowDegree 0) (by omega)
        (E.firstContractionMap d x)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj (intermediate 0).obj)
        (F.obj (intermediate 0).obj) (F.obj X)
        0 (-1 + d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op (intermediate 0).obj))
        (F.firstContractionMap d x) := by
  let A := intermediate 0
  let hE := E.contraction A
  let hF := F.contraction A
  let e := E.firstFactorMap d x
  let f := F.firstFactorMap d x
  let aA := quotientDGUnitGradedNatTransElement α.hom (op A.obj)
  let aX := quotientDGUnitGradedNatTransElement α.hom (op X)
  have hfactor := annihilatingFirstFactorMap_naturality α d x
  have hcontr :
      quotientDGComposeElement (E.obj A.obj) (E.obj A.obj) (F.obj A.obj)
          (-1) 0 (-1) (by omega) hE aA =
        quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj A.obj)
          0 (-1) (-1) (by omega) aA hF := by
    exact α.contraction_naturality A
  unfold AnnihilatingEnrichedFunctorData.firstContractionMap
    AnnihilatingEnrichedFunctorData.composeFirstMap
  change quotientDGComposeElement (E.obj A.obj) (E.obj X) (F.obj X)
      (-1 + d.arrowDegree 0) 0 (-1 + d.arrowDegree 0) (by omega)
      (quotientDGComposeElement (E.obj A.obj) (E.obj A.obj) (E.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) rfl hE e) aX =
    quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
      0 (-1 + d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) aA
      (quotientDGComposeElement (F.obj A.obj) (F.obj A.obj) (F.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) rfl hF f)
  calc
    _ = quotientDGComposeElement (E.obj A.obj) (E.obj A.obj) (F.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) hE
        (quotientDGComposeElement (E.obj A.obj) (E.obj X) (F.obj X)
          (d.arrowDegree 0) 0 (d.arrowDegree 0) (by omega) e aX) := by
      exact quotientDGComposeElement_assoc_of_degree_eq
        (E.obj A.obj) (E.obj A.obj) (E.obj X) (F.obj X)
        (p := -1) (q := d.arrowDegree 0) (r := 0)
        (s := -1 + d.arrowDegree 0) (t := d.arrowDegree 0)
        (n := -1 + d.arrowDegree 0)
        (by omega) (by omega) (by omega) (by omega) hE e aX
    _ = quotientDGComposeElement (E.obj A.obj) (E.obj A.obj) (F.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) hE
        (quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
          0 (d.arrowDegree 0) (d.arrowDegree 0) (by omega) aA f) := by
      rw [hfactor]
    _ = quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega)
        (quotientDGComposeElement (E.obj A.obj) (E.obj A.obj) (F.obj A.obj)
          (-1) 0 (-1) (by omega) hE aA) f := by
      exact (quotientDGComposeElement_assoc_of_degree_eq
        (E.obj A.obj) (E.obj A.obj) (F.obj A.obj) (F.obj X)
        (p := -1) (q := 0) (r := d.arrowDegree 0)
        (s := -1) (t := d.arrowDegree 0)
        (n := -1 + d.arrowDegree 0)
        (by omega) (by omega) (by omega) (by omega) hE aA f).symm
    _ = quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
        (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega)
        (quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj A.obj)
          0 (-1) (-1) (by omega) aA hF) f := by
      exact congrArg
        (fun z ↦ quotientDGComposeElement
          (E.obj A.obj) (F.obj A.obj) (F.obj X)
          (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) z f)
        hcontr
    _ = quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
        0 (-1 + d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) aA
        (quotientDGComposeElement (F.obj A.obj) (F.obj A.obj) (F.obj X)
          (-1) (d.arrowDegree 0) (-1 + d.arrowDegree 0) (by omega) hF f) := by
      exact quotientDGComposeElement_assoc_of_degree_eq
        (E.obj A.obj) (F.obj A.obj) (F.obj A.obj) (F.obj X)
        (p := 0) (q := -1) (r := d.arrowDegree 0)
        (s := -1) (t := -1 + d.arrowDegree 0)
        (n := -1 + d.arrowDegree 0)
        (by omega) (by omega) (by omega) (by omega) aA hF f

/-- Naturality of the evaluator for a zero-length word profile. -/
theorem annihilatingEvaluateNilProfile_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (X Y : ComplexCategory) {n : ℤ}
    (d : DegreeProfile (nil X Y) n) (z : summandModule d) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega) (E.evaluateNilProfile X Y d z)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.evaluateNilProfile X Y d z) := by
  unfold AnnihilatingEnrichedFunctorData.evaluateNilProfile
  exact annihilatingFactorMap_naturality α X Y n
    ((nilSummandIsoOriginal X Y d).hom.hom z)

/-- Naturality of the evaluator for an explicitly zero-length word. -/
theorem annihilatingEvaluateWord_zeroLength_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    {X Y : ComplexCategory}
    (intermediate : Fin 0 → CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) n)
    (z : summandModule d) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega)
        (E.evaluateWord
          ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) d z)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.evaluateWord
          ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) d z) := by
  rw [E.evaluateWord_zeroLength_apply, F.evaluateWord_zeroLength_apply]
  exact annihilatingEvaluateNilProfile_naturality α X Y
    (d.castWord (eq_nil_of_length_eq_zero
      ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) rfl))
    ((summandModuleCastWordIso
      (eq_nil_of_length_eq_zero
        ({ length := 0, intermediate := intermediate } : DrinfeldWord X Y) rfl)
      d).hom.hom z)

/-- Naturality of positive-word evaluation on one canonical head/tail pure tensor. -/
theorem annihilatingEvaluateWord_positive_tensor_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d))
    (htail :
      quotientDGComposeElement (E.obj Y) (E.obj (intermediate 0).obj)
          (F.obj (intermediate 0).obj)
          (AnnihilatingEnrichedFunctorData.tailDegree d) 0
          (AnnihilatingEnrichedFunctorData.tailDegree d) (by omega)
          (E.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t)
          (quotientDGUnitGradedNatTransElement α.hom
            (op (intermediate 0).obj)) =
        quotientDGComposeElement (E.obj Y) (F.obj Y)
          (F.obj (intermediate 0).obj)
          0 (AnnihilatingEnrichedFunctorData.tailDegree d)
          (AnnihilatingEnrichedFunctorData.tailDegree d) (by omega)
          (quotientDGUnitGradedNatTransElement α.hom (op Y))
          (F.evaluateWord (tailWord (Y := Y) intermediate)
            (tailDegreeProfile d) t)) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega)
        (E.evaluateWord
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          ((eqToHom
            (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom
            (x ⊗ₜ[ℤ] t)))
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.evaluateWord
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
          ((eqToHom
            (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom
            (x ⊗ₜ[ℤ] t))) := by
  rw [E.evaluateWord_succ_eq, F.evaluateWord_succ_eq,
    E.evaluateSucc_apply_tensor, F.evaluateSucc_apply_tensor]
  let A := intermediate 0
  let q := AnnihilatingEnrichedFunctorData.tailDegree d
  let p := -1 + d.arrowDegree 0
  let tailE := E.evaluateWord (tailWord (Y := Y) intermediate)
    (tailDegreeProfile d) t
  let tailF := F.evaluateWord (tailWord (Y := Y) intermediate)
    (tailDegreeProfile d) t
  let headE := E.firstContractionMap d x
  let headF := F.firstContractionMap d x
  let aY := quotientDGUnitGradedNatTransElement α.hom (op Y)
  let aA := quotientDGUnitGradedNatTransElement α.hom (op A.obj)
  let aX := quotientDGUnitGradedNatTransElement α.hom (op X)
  have hhead := annihilatingFirstContractionMap_naturality α d x
  change quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
      n 0 n (by omega)
      (quotientDGComposeElement (E.obj Y) (E.obj A.obj) (E.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) tailE headE) aX =
    quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
      0 n n (by omega) aY
      (quotientDGComposeElement (F.obj Y) (F.obj A.obj) (F.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) tailF headF)
  calc
    _ = quotientDGComposeElement (E.obj Y) (E.obj A.obj) (F.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) tailE
        (quotientDGComposeElement (E.obj A.obj) (E.obj X) (F.obj X)
          p 0 p (by omega) headE aX) := by
      exact quotientDGComposeElement_assoc_of_degree_eq
        (E.obj Y) (E.obj A.obj) (E.obj X) (F.obj X)
        (p := q) (q := p) (r := 0) (s := n) (t := p) (n := n)
        (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) (by omega)
        (by omega) (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        tailE headE aX
    _ = quotientDGComposeElement (E.obj Y) (E.obj A.obj) (F.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) tailE
        (quotientDGComposeElement (E.obj A.obj) (F.obj A.obj) (F.obj X)
          0 p p (by omega) aA headF) := by
      rw [hhead]
    _ = quotientDGComposeElement (E.obj Y) (F.obj A.obj) (F.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        (quotientDGComposeElement (E.obj Y) (E.obj A.obj) (F.obj A.obj)
          q 0 q (by omega) tailE aA) headF := by
      exact (quotientDGComposeElement_assoc_of_degree_eq
        (E.obj Y) (E.obj A.obj) (F.obj A.obj) (F.obj X)
        (p := q) (q := 0) (r := p) (s := q) (t := p) (n := n)
        (by omega) (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        (by omega) (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        tailE aA headF).symm
    _ = quotientDGComposeElement (E.obj Y) (F.obj A.obj) (F.obj X)
        q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        (quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj A.obj)
          0 q q (by omega) aY tailF) headF := by
      rw [htail]
    _ = quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega) aY
        (quotientDGComposeElement (F.obj Y) (F.obj A.obj) (F.obj X)
          q p n (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
          tailF headF) := by
      exact quotientDGComposeElement_assoc_of_degree_eq
        (E.obj Y) (F.obj Y) (F.obj A.obj) (F.obj X)
        (p := 0) (q := q) (r := p) (s := q) (t := n) (n := n)
        (by omega) (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d)
        (AnnihilatingEnrichedFunctorData.tailDegree_add_neg_one_add_head d) (by omega)
        aY tailF headF

set_option maxHeartbeats 8000000 in
-- Tensor induction repeatedly unfolds dependent word coordinates and enriched composition.
/-- Naturality of word evaluation for every word of a fixed length. -/
theorem annihilatingEvaluateWord_naturality_of_length
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (k : ℕ) :
    ∀ {X Y : ComplexCategory}
      (intermediate : Fin k → CorrectedAcyclicComplexCategory)
      {n : ℤ}
      (d : DegreeProfile
        ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) n)
      (z : summandModule d),
      quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
          n 0 n (by omega)
          (E.evaluateWord
            ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) d z)
          (quotientDGUnitGradedNatTransElement α.hom (op X)) =
        quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
          0 n n (by omega)
          (quotientDGUnitGradedNatTransElement α.hom (op Y))
          (F.evaluateWord
            ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) d z) := by
  induction k with
  | zero =>
      intro X Y intermediate n d z
      exact annihilatingEvaluateWord_zeroLength_naturality α intermediate d z
  | succ k ih =>
      intro X Y intermediate n d z
      let u :=
        (eqToHom (AnnihilatingEnrichedFunctorData.summandModule_succ d)).hom z
      have hz := ConcreteCategory.congr_hom
        (eqToIso
          (AnnihilatingEnrichedFunctorData.summandModule_succ d)).hom_inv_id z
      simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
        CategoryTheory.id_apply] at hz
      rw [← hz]
      change quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
          n 0 n (by omega)
          (E.evaluateWord
            ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
            ((eqToHom
              (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom u))
          (quotientDGUnitGradedNatTransElement α.hom (op X)) =
        quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
          0 n n (by omega)
          (quotientDGUnitGradedNatTransElement α.hom (op Y))
          (F.evaluateWord
            ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) d
            ((eqToHom
              (AnnihilatingEnrichedFunctorData.summandModule_succ d).symm).hom u))
      refine TensorProduct.induction_on u ?_ ?_ ?_
      · simp only [map_zero]
        unfold quotientDGComposeElement
        simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]
      · intro x t
        apply annihilatingEvaluateWord_positive_tensor_naturality α d x t
        exact ih (X := (intermediate 0).obj) (Y := Y)
          (fun i ↦ intermediate i.succ) (tailDegreeProfile d) t
      · intro a b ha hb
        simp only [map_add]
        unfold quotientDGComposeElement
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
        exact congrArg₂ (· + ·) ha hb

/-- Naturality of evaluation on every corrected Drinfeld word summand. -/
theorem annihilatingEvaluateWord_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (z : summandModule d) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega) (E.evaluateWord w d z)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.evaluateWord w d z) := by
  exact annihilatingEvaluateWord_naturality_of_length α
    w.length w.intermediate d z

/-- Naturality of evaluation on the graded coproduct of all word summands. -/
theorem annihilatingEvaluateGradedValue_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (X Y : ComplexCategory) (n : ℤ)
    (z : quotientGradedModule X Y n) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega) (E.evaluateGradedValue X Y n z)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        (F.evaluateGradedValue X Y n z) := by
  classical
  let Z : GradedSummandIndex X Y n → ModuleCat.{1} ℤ :=
    fun s ↦ largeSummandModule s
  let e := ModuleCat.coprodIsoDirectSum.{0, 1, 1} Z
  let u := e.hom.hom z
  have hz : e.inv.hom u = z := by
    have h := ConcreteCategory.congr_hom e.hom_inv_id z
    dsimp only [u]
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [← hz]
  change quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
      n 0 n (by omega) (E.evaluateGradedValue X Y n (e.inv.hom u))
      (quotientDGUnitGradedNatTransElement α.hom (op X)) =
    quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
      0 n n (by omega)
      (quotientDGUnitGradedNatTransElement α.hom (op Y))
      (F.evaluateGradedValue X Y n (e.inv.hom u))
  induction u using DirectSum.induction_on with
  | zero =>
      rw [map_zero]
      have hEzero : E.evaluateGradedValue X Y n 0 = 0 :=
        (E.evaluateGradedModule X Y n).hom.map_zero
      have hFzero : F.evaluateGradedValue X Y n 0 = 0 :=
        (F.evaluateGradedModule X Y n).hom.map_zero
      rw [hEzero, hFzero]
      unfold quotientDGComposeElement
      rw [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
      simp only [map_zero]
  | of s x =>
      rcases s with ⟨w, d⟩
      have hlof := ConcreteCategory.congr_hom
        (ModuleCat.lof_coprodIsoDirectSum_inv.{0, 1, 1} Z ⟨w, d⟩) x
      simp only [ModuleCat.comp_apply] at hlof
      have hinv : e.inv.hom
          (DirectSum.of (fun i ↦ Z i) ⟨w, d⟩ x) =
          (Limits.Sigma.ι Z ⟨w, d⟩).hom x := by
        rw [← DirectSum.lof_eq_of ℤ]
        exact hlof
      rw [hinv]
      dsimp only [Z] at x
      rcases x with ⟨x⟩
      rw [E.evaluateGradedValue_inclusion, F.evaluateGradedValue_inclusion]
      exact annihilatingEvaluateWord_naturality α d x
  | add a b ha hb =>
      rw [map_add]
      rw [E.evaluateGradedValue_add, F.evaluateGradedValue_add]
      unfold quotientDGComposeElement
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
      exact congrArg₂ (· + ·) ha hb

/-- Naturality after coefficient change, on every homogeneous element. -/
theorem annihilatingEvaluateCoefficientDegree_naturality
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (X Y : ComplexCategory) (n : ℤ)
    (z : quotientCoefficientModule (quotientGradedModule X Y n)) :
    quotientDGComposeElement (E.obj Y) (E.obj X) (F.obj X)
        n 0 n (by omega) ((E.evaluateCoefficientDegree X Y n).hom z)
        (quotientDGUnitGradedNatTransElement α.hom (op X)) =
      quotientDGComposeElement (E.obj Y) (F.obj Y) (F.obj X)
        0 n n (by omega)
        (quotientDGUnitGradedNatTransElement α.hom (op Y))
        ((F.evaluateCoefficientDegree X Y n).hom z) := by
  rcases z with ⟨z⟩
  rw [E.evaluateCoefficientDegree_apply_up,
    F.evaluateCoefficientDegree_apply_up]
  exact annihilatingEvaluateGradedValue_naturality α X Y n z

/-- Extend an annihilating enriched transformation across the corrected Drinfeld quotient. -/
noncomputable def annihilatingEnrichedFunctorNatTransExtension
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F) :
    QuotientDGUnitGradedNatTrans E.enrichedExtension F.enrichedExtension :=
  quotientDGUnitGradedNatTransOfElements
    (fun K ↦ α.hom.app (op K.unop)) (fun K L p x ↦ by
      change quotientDGComposeElement
          (E.obj K.unop) (E.obj L.unop) (F.obj L.unop)
          p 0 p (by omega)
          ((E.evaluateCochainMap L.unop K.unop).f p x)
          (quotientDGUnitGradedNatTransElement α.hom (op L.unop)) =
        quotientDGComposeElement
          (E.obj K.unop) (F.obj K.unop) (F.obj L.unop)
          0 p p (by omega)
          (quotientDGUnitGradedNatTransElement α.hom (op K.unop))
          ((F.evaluateCochainMap L.unop K.unop).f p x)
      exact annihilatingEvaluateCoefficientDegree_naturality
        α L.unop K.unop p x)

/-- Restricting an extended transformation recovers the original annihilating
transformation after transporting along the object-level round trip. -/
theorem restriction_annihilatingEnrichedFunctorNatTransExtension
    {E F : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F) :
    annihilatingEnrichedFunctorNatTransTransport
        E.restriction_enrichedExtension F.restriction_enrichedExtension
        (quotientDGUnitGradedNatTransRestriction
          (annihilatingEnrichedFunctorNatTransExtension α)) = α := by
  apply AnnihilatingEnrichedFunctorNatTrans.ext
  apply GradedNatTrans.ext
  funext K
  apply eq_of_heq
  exact (annihilatingEnrichedFunctorNatTransTransport_app_heq
    E.restriction_enrichedExtension F.restriction_enrichedExtension
    (quotientDGUnitGradedNatTransRestriction
      (annihilatingEnrichedFunctorNatTransExtension α)) K).trans (by rfl)

/-- Extending the restriction of a quotient transformation recovers the original
transformation after transporting along the object-level round trip. -/
theorem annihilatingEnrichedFunctorNatTransExtension_restriction
    {G H : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D}
    (α : QuotientDGUnitGradedNatTrans G H) :
    quotientDGUnitGradedNatTransTransport
        (EnrichedFunctor.enrichedExtension_restriction G)
        (EnrichedFunctor.enrichedExtension_restriction H)
        (annihilatingEnrichedFunctorNatTransExtension
          (quotientDGUnitGradedNatTransRestriction α)) = α := by
  apply GradedNatTrans.ext
  funext K
  apply eq_of_heq
  exact (quotientDGUnitGradedNatTransTransport_app_heq
    (EnrichedFunctor.enrichedExtension_restriction G)
    (EnrichedFunctor.enrichedExtension_restriction H)
    (annihilatingEnrichedFunctorNatTransExtension
      (quotientDGUnitGradedNatTransRestriction α)) K).trans (by rfl)

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
