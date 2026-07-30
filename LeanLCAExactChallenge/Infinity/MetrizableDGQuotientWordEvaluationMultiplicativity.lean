/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationMultiplicativityNilPositive

/-! # Multiplicativity of corrected Drinfeld word evaluation

The zero-left cases and the positive recursive step are extended from pure tensors by tensor
induction, then combined by induction on the length of the left word.
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

set_option maxHeartbeats 4000000 in
/-- Multiplicativity when the left word is the canonical zero-length word. -/
theorem evaluateWord_multiplicative_nil_left
    (X Y Z : ComplexCategory) {v : DrinfeldWord Y Z} (n : ℤ) {m : ℤ}
    (e : DegreeProfile v m)
    (x : (dgHomZModuleCochainComplex X Y).X n)
    (z : summandModule e) :
    E.evaluateWord ((nil X Y).append v)
        ((nilDegreeProfile X Y n).append e)
        ((summandCompositionMap (nilDegreeProfile X Y n) e).hom
          ((nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ] z)) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.factorMap X Y n x) (E.evaluateWord v e z) := by
  cases v with
  | mk length intermediate =>
      cases length with
      | zero =>
          have hintermediate : intermediate =
              (Fin.elim0 : Fin 0 → CorrectedAcyclicComplexCategory) :=
            Subsingleton.elim _ _
          subst intermediate
          change E.evaluateWord ((nil X Y).append (nil Y Z))
              ((nilDegreeProfile X Y n).append e)
              ((summandCompositionMap (nilDegreeProfile X Y n) e).hom
                ((nilSummandIsoOriginal X Y
                    (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ] z)) =
            E.composeElement X Y Z n m (n + m)
              (wordEvaluationCompositionDegreeEq n m)
              (E.factorMap X Y n x) (E.evaluateWord (nil Y Z) e z)
          have he : e = nilDegreeProfile Y Z m := degreeProfile_nil_eq e
          cases he
          let z₀ :=
            (nilSummandIsoOriginal Y Z (nilDegreeProfile Y Z m)).hom.hom z
          have hz := ConcreteCategory.congr_hom
            (nilSummandIsoOriginal Y Z
              (nilDegreeProfile Y Z m)).hom_inv_id z
          simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hz
          change _ = E.composeElement X Y Z n m (n + m)
            (wordEvaluationCompositionDegreeEq n m)
            (E.factorMap X Y n x)
            (E.evaluateWord (nil Y Z) (nilDegreeProfile Y Z m) z)
          rw [← hz]
          rw [E.evaluateWord_nil_apply]
          unfold evaluateNilProfile
          simp only [LinearMap.comp_apply]
          have hcancel := ConcreteCategory.congr_hom
            (nilSummandIsoOriginal Y Z
              (nilDegreeProfile Y Z m)).inv_hom_id z₀
          simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
          rw [hcancel]
          exact E.evaluateWord_multiplicative_nil_nil X Y Z n m x z₀
      | succ k =>
          let u := (eqToHom (summandModule_succ e)).hom z
          have hz := ConcreteCategory.congr_hom
            (eqToIso (summandModule_succ e)).hom_inv_id z
          simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
            CategoryTheory.id_apply] at hz
          change E.evaluateWord
              ((nil X Y).append
                ({ length := k + 1, intermediate := intermediate } :
                  DrinfeldWord Y Z))
              ((nilDegreeProfile X Y n).append e)
              ((summandCompositionMap (nilDegreeProfile X Y n) e).hom
                ((nilSummandIsoOriginal X Y
                    (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ] z)) = _
          rw [← hz]
          change E.evaluateWord
              ((nil X Y).append
                ({ length := k + 1, intermediate := intermediate } :
                  DrinfeldWord Y Z))
              ((nilDegreeProfile X Y n).append e)
              ((summandCompositionMap (nilDegreeProfile X Y n) e).hom
                ((nilSummandIsoOriginal X Y
                    (nilDegreeProfile X Y n)).inv.hom x ⊗ₜ[ℤ]
                  (eqToHom (summandModule_succ e).symm).hom u)) =
            E.composeElement X Y Z n m (n + m)
              (wordEvaluationCompositionDegreeEq n m)
              (E.factorMap X Y n x)
              (E.evaluateWord
                ({ length := k + 1, intermediate := intermediate } :
                  DrinfeldWord Y Z) e
                ((eqToHom (summandModule_succ e).symm).hom u))
          refine TensorProduct.induction_on u ?_ ?_ ?_
          · simp only [map_zero, TensorProduct.tmul_zero]
            change 0 = (E.composeSecondMap X Y Z n m (n + m)
              (wordEvaluationCompositionDegreeEq n m)
              (E.factorMap X Y n x)) 0
            exact (LinearMap.map_zero _).symm
          · intro y t
            exact E.evaluateWord_multiplicative_nil_positive
              (W := X) n e x y t
          · intro a b ha hb
            simp only [map_add, TensorProduct.tmul_add]
            have hsum := congrArg₂ (· + ·) ha hb
            have hlinear := (E.composeSecondMap X Y Z n m (n + m)
              (wordEvaluationCompositionDegreeEq n m)
              (E.factorMap X Y n x)).map_add
                (E.evaluateWord
                  ({ length := k + 1, intermediate := intermediate } :
                    DrinfeldWord Y Z) e
                  ((eqToHom (summandModule_succ e).symm).hom a))
                (E.evaluateWord
                  ({ length := k + 1, intermediate := intermediate } :
                    DrinfeldWord Y Z) e
                  ((eqToHom (summandModule_succ e).symm).hom b))
            exact hsum.trans hlinear.symm

set_option maxHeartbeats 4000000 in
/-- Multiplicativity for a left word presented with a fixed length. -/
theorem evaluateWord_multiplicative_of_length
    (k : ℕ) :
    ∀ {X Y Z : ComplexCategory}
      (intermediate : Fin k → CorrectedAcyclicComplexCategory)
      {v : DrinfeldWord Y Z} {n m : ℤ}
      (d : DegreeProfile
        ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) n)
      (e : DegreeProfile v m)
      (x : summandModule d) (z : summandModule e),
      E.evaluateWord
          (({ length := k, intermediate := intermediate } :
            DrinfeldWord X Y).append v) (d.append e)
          ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] z)) =
        E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateWord
            ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) d x)
          (E.evaluateWord v e z) := by
  induction k with
  | zero =>
      intro X Y Z intermediate v n m d e x z
      have hintermediate : intermediate =
          (Fin.elim0 : Fin 0 → CorrectedAcyclicComplexCategory) :=
        Subsingleton.elim _ _
      subst intermediate
      change DegreeProfile (nil X Y) n at d
      change summandModule d at x
      change E.evaluateWord ((nil X Y).append v) (d.append e)
          ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] z)) =
        E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateWord (nil X Y) d x) (E.evaluateWord v e z)
      have hd : d = nilDegreeProfile X Y n := degreeProfile_nil_eq d
      cases hd
      let x₀ :=
        (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).hom.hom x
      have hx := ConcreteCategory.congr_hom
        (nilSummandIsoOriginal X Y
          (nilDegreeProfile X Y n)).hom_inv_id x
      simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hx
      rw [← hx]
      rw [E.evaluateWord_nil_apply]
      unfold evaluateNilProfile
      simp only [LinearMap.comp_apply]
      have hcancel := ConcreteCategory.congr_hom
        (nilSummandIsoOriginal X Y
          (nilDegreeProfile X Y n)).inv_hom_id x₀
      simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
      rw [hcancel]
      exact E.evaluateWord_multiplicative_nil_left X Y Z n e x₀ z
  | succ k ih =>
      intro X Y Z intermediate v n m d e x z
      let u := (eqToHom (summandModule_succ d)).hom x
      have hx := ConcreteCategory.congr_hom
        (eqToIso (summandModule_succ d)).hom_inv_id x
      simp only [ModuleCat.comp_apply, eqToIso.hom, eqToIso.inv,
        CategoryTheory.id_apply] at hx
      rw [← hx]
      change E.evaluateWord
          (({ length := k + 1, intermediate := intermediate } :
            DrinfeldWord X Y).append v) (d.append e)
          ((summandCompositionMap d e).hom
            ((eqToHom (summandModule_succ d).symm).hom u ⊗ₜ[ℤ] z)) =
        E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateWord
            ({ length := k + 1, intermediate := intermediate } :
              DrinfeldWord X Y) d
            ((eqToHom (summandModule_succ d).symm).hom u))
          (E.evaluateWord v e z)
      refine TensorProduct.induction_on u ?_ ?_ ?_
      · simp only [map_zero, TensorProduct.zero_tmul]
        change 0 = (E.composeFirstMap X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateWord v e z)) 0
        exact (LinearMap.map_zero _).symm
      · intro a b
        apply E.evaluateWord_multiplicative_positive_step d e a b z
        exact ih (X := (intermediate 0).obj) (Y := Y) (Z := Z)
          (fun i ↦ intermediate i.succ) (tailDegreeProfile d) e b z
      · intro a b ha hb
        simp only [map_add, TensorProduct.add_tmul]
        have hsum := congrArg₂ (· + ·) ha hb
        have hlinear := (E.composeFirstMap X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateWord v e z)).map_add
            (E.evaluateWord
              ({ length := k + 1, intermediate := intermediate } :
                DrinfeldWord X Y) d
              ((eqToHom (summandModule_succ d).symm).hom a))
            (E.evaluateWord
              ({ length := k + 1, intermediate := intermediate } :
                DrinfeldWord X Y) d
              ((eqToHom (summandModule_succ d).symm).hom b))
        exact hsum.trans hlinear.symm

/-- Corrected word evaluation preserves summand composition for arbitrary words. -/
theorem evaluateWord_multiplicative
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : summandModule d) (z : summandModule e) :
    E.evaluateWord (w.append v) (d.append e)
        ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] z)) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateWord w d x) (E.evaluateWord v e z) := by
  cases w with
  | mk k intermediate =>
      exact E.evaluateWord_multiplicative_of_length k intermediate d e x z

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
