/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationMultiplicativity
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationFunctor

/-! # Enriched composition preservation by corrected word evaluation

Word-level multiplicativity is lifted through the large coproduct, universe lift, and coefficient
change, then packaged as the enriched composition law for `evaluateCochainMap`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring
attribute [-instance] ULift.smulLeft
attribute [-instance] ULift.smulZeroClass
attribute [-instance] ULift.distribSMul
attribute [-instance] ULift.mulAction
attribute [-instance] ULift.distribMulAction
attribute [-instance] ULift.smulWithZero
attribute [-instance] ULift.mulActionWithZero
attribute [-instance] ULift.module

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

/-- Graded coproduct evaluation preserves composition on two homogeneous summand inclusions. -/
theorem evaluateGradedValue_composition_inclusions
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : summandModule d) (y : summandModule e) :
    E.evaluateGradedValue X Z (n + m)
        (quotientCompositionMap X Y Z n m
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
            ⟨w, d⟩).hom (ULift.up x))
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
            ⟨v, e⟩).hom (ULift.up y))) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateWord w d x) (E.evaluateWord v e y) := by
  rw [quotientCompositionMap_on_summands]
  rw [largeSummandCompositionMap_eq_inclusion]
  change E.evaluateGradedValue X Z (n + m)
      ((Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z (n + m) ↦ largeSummandModule s)
        ⟨w.append v, d.append e⟩).hom
        (ULift.up ((summandCompositionMap d e).hom (x ⊗ₜ[ℤ] y)))) = _
  rw [E.evaluateGradedValue_inclusion]
  exact E.evaluateWord_multiplicative d e x y

/-- Target composition after applying the two graded coproduct evaluators. -/
def evaluateGradedTargetCompositionMap
    (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientGradedModule X Y n →ₗ[ℤ]
      quotientGradedModule Y Z m →ₗ[ℤ] E.targetIntModule X Z (n + m) := by
  let inner (a : quotientGradedModule X Y n) :=
    (E.composeSecondMap X Y Z n m (n + m)
      (wordEvaluationCompositionDegreeEq n m)
      (E.evaluateGradedValue X Y n a)).comp
        (E.evaluateGradedModule Y Z m).hom
  exact intLinearMapOfAddHom ({
    toFun := inner
    map_zero' := by
      ext b
      change E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateGradedValue X Y n 0)
          (E.evaluateGradedValue Y Z m b) = 0
      have hz := (E.evaluateGradedModule X Y n).hom.map_zero
      change E.evaluateGradedValue X Y n 0 = 0 at hz
      rw [hz]
      exact (E.composeFirstMap X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateGradedValue Y Z m b)).map_zero
    map_add' := by
      intro a b
      ext c
      change E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateGradedValue X Y n (a + b))
          (E.evaluateGradedValue Y Z m c) = _
      rw [E.evaluateGradedValue_add]
      exact (E.composeFirstMap X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateGradedValue Y Z m c)).map_add
          (E.evaluateGradedValue X Y n a)
          (E.evaluateGradedValue X Y n b) } :
      quotientGradedModule X Y n →+
        (quotientGradedModule Y Z m →ₗ[ℤ] E.targetIntModule X Z (n + m)))

/-- Evaluation after graded quotient composition, as an integer-bilinear map. -/
def evaluateGradedCompositionMap
    (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientGradedModule X Y n →ₗ[ℤ]
      quotientGradedModule Y Z m →ₗ[ℤ] E.targetIntModule X Z (n + m) :=
  intBilinearMapPostcomp (quotientCompositionMap X Y Z n m)
    (E.evaluateGradedModule X Z (n + m)).hom

/-- Graded coproduct evaluation preserves composition on arbitrary coproduct elements. -/
theorem evaluateGradedCompositionMap_eq
    (X Y Z : ComplexCategory) (n m : ℤ) :
    E.evaluateGradedCompositionMap X Y Z n m =
      E.evaluateGradedTargetCompositionMap X Y Z n m := by
  let left := E.evaluateGradedCompositionMap X Y Z n m
  let right := E.evaluateGradedTargetCompositionMap X Y Z n m
  have houter : ModuleCat.ofHom left = ModuleCat.ofHom right := by
    apply Limits.Sigma.hom_ext
    rintro ⟨w, d⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hinner : ModuleCat.ofHom
          (left ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
            ⟨w, d⟩).hom x)) =
        ModuleCat.ofHom
          (right ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
            ⟨w, d⟩).hom x)) := by
      apply Limits.Sigma.hom_ext
      rintro ⟨v, e⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      change E.evaluateGradedValue X Z (n + m)
          (quotientCompositionMap X Y Z n m
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
              ⟨w, d⟩).hom (ULift.up x))
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
              ⟨v, e⟩).hom (ULift.up y))) =
        E.composeElement X Y Z n m (n + m)
          (wordEvaluationCompositionDegreeEq n m)
          (E.evaluateGradedValue X Y n
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
              ⟨w, d⟩).hom (ULift.up x)))
          (E.evaluateGradedValue Y Z m
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
              ⟨v, e⟩).hom (ULift.up y)))
      rw [E.evaluateGradedValue_inclusion, E.evaluateGradedValue_inclusion]
      exact E.evaluateGradedValue_composition_inclusions d e x y
    exact congrArg ModuleCat.Hom.hom hinner
  exact congrArg ModuleCat.Hom.hom houter

@[simp]
theorem evaluateGradedValue_composition
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    E.evaluateGradedValue X Z (n + m)
        (quotientCompositionMap X Y Z n m x y) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m)
        (E.evaluateGradedValue X Y n x)
        (E.evaluateGradedValue Y Z m y) := by
  have h := congrArg (fun f ↦ f x y)
    (E.evaluateGradedCompositionMap_eq X Y Z n m)
  exact h

/-- Target homogeneous composition with its inputs in actual arrow order. -/
def targetHomogeneousCompositionMap
    (X Y Z : ComplexCategory) (n m : ℤ) :
    (E.hom X Y).X n ⊗ (E.hom Y Z).X m ⟶
      (E.hom X Z).X (n + m) :=
  (β_ _ _).hom ≫
    HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y)
      m n (n + m) (wordEvaluationCompositionDegreeEq n m) ≫
    (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f (n + m)

@[simp]
theorem targetHomogeneousCompositionMap_tmul
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : (E.hom X Y).X n) (y : (E.hom Y Z).X m) :
    (E.targetHomogeneousCompositionMap X Y Z n m).hom
        (x ⊗ₜ[QuotientCoefficientRing] y) =
      E.composeElement X Y Z n m (n + m)
        (wordEvaluationCompositionDegreeEq n m) x y := by
  unfold targetHomogeneousCompositionMap composeElement
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]

set_option maxHeartbeats 800000 in
-- Tensor extensionality must normalize two universe-lifted coefficient module structures.
/-- After coefficient change, homogeneous word evaluation preserves quotient composition. -/
theorem evaluateCoefficientDegree_composition
    (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientCompositionTensorMap X Y Z n m ≫
        E.evaluateCoefficientDegree X Z (n + m) =
      (E.evaluateCoefficientDegree X Y n ⊗ₘ
          E.evaluateCoefficientDegree Y Z m) ≫
        E.targetHomogeneousCompositionMap X Y Z n m := by
  letI : Module QuotientCoefficientRing
      (quotientCoefficientModule (quotientGradedModule X Y n)) :=
    (quotientCoefficientModule (quotientGradedModule X Y n)).isModule
  letI : Module QuotientCoefficientRing
      (quotientCoefficientModule (quotientGradedModule Y Z m)) :=
    (quotientCoefficientModule (quotientGradedModule Y Z m)).isModule
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a b
  rcases a with ⟨x⟩
  rcases b with ⟨y⟩
  change (quotientCompositionTensorMap X Y Z n m ≫
      E.evaluateCoefficientDegree X Z (n + m)).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
    ((E.evaluateCoefficientDegree X Y n ⊗ₘ
        E.evaluateCoefficientDegree Y Z m) ≫
      E.targetHomogeneousCompositionMap X Y Z n m).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y)
  rw [ModuleCat.comp_apply, quotientCompositionTensorMap_tmul,
    E.evaluateCoefficientDegree_apply_up]
  change E.evaluateGradedValue X Z (n + m)
      (quotientCompositionMap X Y Z n m x y) =
    (E.targetHomogeneousCompositionMap X Y Z n m).hom
      (E.evaluateGradedValue X Y n x ⊗ₜ[QuotientCoefficientRing]
        E.evaluateGradedValue Y Z m y)
  rw [E.targetHomogeneousCompositionMap_tmul,
    E.evaluateGradedValue_composition]

/-- Homogeneous evaluation commutes with equality transport of the total degree. -/
theorem evaluateCoefficientDegree_cast
    (X Y : ComplexCategory) {n m : ℤ} (h : n = m) :
    eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule X Y k)) h) ≫
        E.evaluateCoefficientDegree X Y m =
      E.evaluateCoefficientDegree X Y n ≫
        eqToHom (congrArg (fun k ↦ (E.hom X Y).X k) h) := by
  subst m
  simp

/-- Integer-graded evaluation commutes with equality transport of the total degree. -/
theorem evaluateGradedValue_cast
    (X Y : ComplexCategory) {n m : ℤ} (h : n = m)
    (x : quotientGradedModule X Y n) :
    E.evaluateGradedValue X Y m
        ((eqToHom (congrArg (quotientGradedModule X Y) h)).hom x) =
      (eqToHom (congrArg (fun k ↦ (E.hom X Y).X k) h)).hom
        (E.evaluateGradedValue X Y n x) := by
  have hcast := ConcreteCategory.congr_hom
    (E.evaluateCoefficientDegree_cast X Y h) (ULift.up x)
  change (E.evaluateCoefficientDegree X Y m).hom
      ((eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule X Y k)) h)).hom
        (ULift.up x)) =
    (eqToHom (congrArg (fun k ↦ (E.hom X Y).X k) h)).hom
      ((E.evaluateCoefficientDegree X Y n).hom (ULift.up x)) at hcast
  simpa only [
    quotientCoefficient_eqToHom_apply_up (X := X) (Y := Y) h x,
    E.evaluateCoefficientDegree_apply_up] using hcast

set_option maxHeartbeats 800000 in
-- Pure-tensor extensionality expands both the source and target total-complex inclusions.
/-- The homogeneous component of `quotientDGComposition`, followed by evaluation, agrees with
target enriched composition after evaluating both homogeneous inputs. -/
theorem evaluateCoefficientDegree_composition_of_eq
    (X Y Z : ComplexCategory) (p q r : ℤ) (h : p + q = r) :
    (β_
        (quotientCoefficientModule (quotientGradedModule Y Z p))
        (quotientCoefficientModule (quotientGradedModule X Y q))).hom ≫
        quotientCompositionTensorMap X Y Z q p ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
          ((Int.add_comm q p).trans h)) ≫
        E.evaluateCoefficientDegree X Z r =
      (E.evaluateCoefficientDegree Y Z p ⊗ₘ
          E.evaluateCoefficientDegree X Y q) ≫
        HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y)
          p q r h ≫
        (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f r := by
  letI : Module QuotientCoefficientRing
      (quotientCoefficientModule (quotientGradedModule Y Z p)) :=
    (quotientCoefficientModule (quotientGradedModule Y Z p)).isModule
  letI : Module QuotientCoefficientRing
      (quotientCoefficientModule (quotientGradedModule X Y q)) :=
    (quotientCoefficientModule (quotientGradedModule X Y q)).isModule
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a b
  rcases a with ⟨y⟩
  rcases b with ⟨x⟩
  change (((β_
        (quotientCoefficientModule (quotientGradedModule Y Z p))
        (quotientCoefficientModule (quotientGradedModule X Y q))).hom ≫
      quotientCompositionTensorMap X Y Z q p ≫
      eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
        ((Int.add_comm q p).trans h)) ≫
      E.evaluateCoefficientDegree X Z r).hom
        (ULift.up y ⊗ₜ[QuotientCoefficientRing] ULift.up x)) =
    (((E.evaluateCoefficientDegree Y Z p ⊗ₘ
        E.evaluateCoefficientDegree X Y q) ≫
      HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y)
        p q r h ≫
      (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f r).hom
        (ULift.up y ⊗ₜ[QuotientCoefficientRing] ULift.up x))
  simp only [ModuleCat.comp_apply]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply,
    quotientCompositionTensorMap_tmul]
  change (E.evaluateCoefficientDegree X Z r).hom
      ((eqToHom (congrArg
        (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
        ((Int.add_comm q p).trans h))).hom
        (ULift.up (quotientCompositionMap X Y Z q p x y))) =
    ((HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y)
        p q r h ≫
      (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f r).hom)
      ((E.evaluateCoefficientDegree Y Z p ⊗ₘ
          E.evaluateCoefficientDegree X Y q).hom
        (ULift.up y ⊗ₜ[QuotientCoefficientRing] ULift.up x))
  rw [quotientCoefficient_eqToHom_apply_up
    (X := X) (Y := Z) ((Int.add_comm q p).trans h)
      (quotientCompositionMap X Y Z q p x y),
    E.evaluateCoefficientDegree_apply_up] <;> try omega
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [E.evaluateCoefficientDegree_apply_up,
    E.evaluateCoefficientDegree_apply_up]
  change E.evaluateGradedValue X Z r
      ((eqToHom (congrArg (quotientGradedModule X Z)
        ((Int.add_comm q p).trans h))).hom
        (quotientCompositionMap X Y Z q p x y)) =
    E.composeElement X Y Z q p r h
      (E.evaluateGradedValue X Y q x)
      (E.evaluateGradedValue Y Z p y)
  rw [E.evaluateGradedValue_cast,
    E.evaluateGradedValue_composition]
  simpa using E.composeElement_cast_output X Y Z q p (q + p) r
    (wordEvaluationCompositionDegreeEq q p)
    ((Int.add_comm q p).trans h)
    (E.evaluateGradedValue X Y q x)
    (E.evaluateGradedValue Y Z p y)
  all_goals omega

theorem evaluateCochainMap_component_composition
    (X Y Z : ComplexCategory) (p q r : ℤ) (h : p + q = r) :
    (β_
        ((quotientCoefficientCochainComplex Y Z).X p)
        ((quotientCoefficientCochainComplex X Y).X q)).hom ≫
        quotientCompositionTensorMap X Y Z q p ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
          ((Int.add_comm q p).trans h)) ≫
        (E.evaluateCochainMap X Z).f r =
      ((curriedTensor (ModuleCat QuotientCoefficientRing)).map
          ((E.evaluateCochainMap Y Z).f p)).app
          ((quotientCoefficientCochainComplex X Y).X q) ≫
        ((curriedTensor (ModuleCat QuotientCoefficientRing)).obj
          ((E.hom Y Z).X p)).map ((E.evaluateCochainMap X Y).f q) ≫
        HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y)
          p q r h ≫
        (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f r := by
  simpa only [evaluateCochainMap, quotientCoefficientCochainComplex_X,
    curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, Category.assoc] using
      E.evaluateCoefficientDegree_composition_of_eq X Y Z p q r h

set_option maxHeartbeats 800000 in
-- Total-complex extensionality exposes one homogeneous pair at a time.
/-- The corrected word-evaluation cochain map preserves enriched composition. -/
theorem evaluateCochainMap_comp
    (X Y Z : ComplexCategory) :
    quotientDGComposition X Y Z ≫ E.evaluateCochainMap X Z =
      HomologicalComplex.tensorHom
          (E.evaluateCochainMap Y Z) (E.evaluateCochainMap X Y) ≫
        eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X) := by
  apply HomologicalComplex.hom_ext
  intro r
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, quotientDGComposition_f]
  rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  exact E.evaluateCochainMap_component_composition X Y Z p q r h

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
