/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCore

/-! # Cochain-map evaluation of corrected Drinfeld words

This module lifts the linear evaluation of homogeneous Drinfeld words to the large coproduct and
the universe-matched coefficient modules. It also proves differential compatibility for zero-word
summands. Positive-word compatibility is built by structural induction in the following layer.
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

/-- A target homogeneous Hom module, regarded as an integer module. -/
abbrev targetIntModule (X Y : ComplexCategory) (n : ℤ) : ModuleCat.{1} ℤ :=
  ModuleCat.of ℤ ((E.hom X Y).X n)

/-- Evaluate one universe-lifted homogeneous word summand. -/
def evaluateLargeSummand
    {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) :
    largeSummandModule s →ₗ[ℤ] E.targetIntModule X Y n where
  toFun x := E.evaluateWord s.1 s.2 x.down
  map_add' x y := by
    exact (E.evaluateWord s.1 s.2).map_add x.down y.down
  map_smul' r x := by
    exact (E.evaluateWord s.1 s.2).map_smul r x.down

/-- Evaluate the coproduct of all homogeneous word summands in one quotient degree. -/
def evaluateGradedModule
    (X Y : ComplexCategory) (n : ℤ) :
    quotientGradedModule X Y n ⟶ E.targetIntModule X Y n :=
  Limits.Sigma.desc fun s : GradedSummandIndex X Y n ↦
    ModuleCat.ofHom (E.evaluateLargeSummand s)

/-- The nil summand coordinate is natural with respect to its unique internal differential. -/
theorem nilSummandIsoOriginal_internalDifferential_naturality
    (X Y : ComplexCategory) (n : ℤ) :
    internalDifferentialTensorMap (nilDegreeProfile X Y n) 0 ≫
        (nilSummandIsoOriginal X Y ((nilDegreeProfile X Y n).raise 0)).hom =
      (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).hom ≫
        (dgHomZModuleCochainComplex X Y).d n (n + 1) := by
  let e := nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)
  let e' := nilSummandIsoOriginal X Y ((nilDegreeProfile X Y n).raise 0)
  let T := internalDifferentialTensorMap (nilDegreeProfile X Y n) 0
  let δ := (dgHomZModuleCochainComplex X Y).d n (n + 1)
  have hinv : e.inv ≫ T = δ ≫ e'.inv := by
    simp only [e, e', T, δ, nilSummandIsoOriginal, eqToIso_refl,
      Iso.trans_refl, internalDifferentialTensorMap, TensorMapData.ofFn,
      factorDifferential, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
      Fin.succ_ne_zero, TensorMapData.tensorMap, tensorHom_id]
    exact (MonoidalCategory.rightUnitor_inv_naturality δ).symm
  calc
    T ≫ e'.hom = (e.hom ≫ e.inv) ≫ T ≫ e'.hom := by simp
    _ = e.hom ≫ (e.inv ≫ T) ≫ e'.hom := by simp only [Category.assoc]
    _ = e.hom ≫ (δ ≫ e'.inv) ≫ e'.hom := by rw [hinv]
    _ = e.hom ≫ δ := by simp

/-- The image of an original Hom factor commutes with its cochain differential. -/
theorem factorMap_d
    (X Y : ComplexCategory) (n : ℤ)
    (x : (dgHomZModuleCochainComplex X Y).X n) :
    ((E.hom X Y).d n (n + 1)) (E.factorMap X Y n x) =
      E.factorMap X Y (n + 1)
        (((dgHomZModuleCochainComplex X Y).d n (n + 1)) x) := by
  let K : OriginalCoefficientDGCategory := Opposite.op Y
  let L : OriginalCoefficientDGCategory := Opposite.op X
  have h := ConcreteCategory.congr_hom
    ((E.functor.map K L).comm n (n + 1))
    (ULift.up (ULift.up x))
  change ((E.hom X Y).d n (n + 1))
      ((E.functor.map (Opposite.op Y) (Opposite.op X)).f n
        (ULift.up (ULift.up x))) =
    (E.functor.map (Opposite.op Y) (Opposite.op X)).f (n + 1)
      (ULift.up (ULift.up
        (((dgHomZModuleCochainComplex X Y).d n (n + 1)) x))) at h
  exact h

/-- The nil-word evaluation commutes with the unique internal differential. -/
theorem evaluateNilProfile_d
    (X Y : ComplexCategory) {n : ℤ}
    (d : DegreeProfile (nil X Y) n) (x : summandModule d) :
    ((E.hom X Y).d n (n + 1)) (E.evaluateNilProfile X Y d x) =
      E.evaluateNilProfile X Y (d.raise 0)
        ((internalDifferentialTensorMap d 0).hom x) := by
  have hd := degreeProfile_nil_eq d
  subst d
  unfold evaluateNilProfile
  change ((E.hom X Y).d n (n + 1))
      (E.factorMap X Y n
        ((nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).hom.hom x)) =
    E.factorMap X Y (n + 1)
      ((nilSummandIsoOriginal X Y ((nilDegreeProfile X Y n).raise 0)).hom.hom
        ((internalDifferentialTensorMap (nilDegreeProfile X Y n) 0).hom x))
  rw [factorMap_d]
  have hnat := ConcreteCategory.congr_hom
    (nilSummandIsoOriginal_internalDifferential_naturality X Y n) x
  simp only [ModuleCat.comp_apply] at hnat
  rw [← hnat]

@[simp]
theorem evaluateGradedModule_inclusion
    {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) (x : summandModule s.2) :
    (E.evaluateGradedModule X Y n).hom
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s).hom
            (ULift.up x)) =
      E.evaluateWord s.1 s.2 x := by
  change (Limits.Sigma.ι
      (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        Limits.Sigma.desc (fun t : GradedSummandIndex X Y n ↦
          ModuleCat.ofHom (E.evaluateLargeSummand t))).hom (ULift.up x) = _
  rw [Limits.Sigma.ι_desc]
  rfl

/-- The coproduct evaluation, with its value explicitly viewed in the target Q-module. -/
def evaluateGradedValue
    (X Y : ComplexCategory) (n : ℤ) (x : quotientGradedModule X Y n) :
    (E.hom X Y).X n :=
  (E.evaluateGradedModule X Y n).hom x

@[simp]
theorem evaluateGradedValue_add
    (X Y : ComplexCategory) (n : ℤ) (x y : quotientGradedModule X Y n) :
    E.evaluateGradedValue X Y n (x + y) =
      E.evaluateGradedValue X Y n x + E.evaluateGradedValue X Y n y := by
  exact (E.evaluateGradedModule X Y n).hom.map_add x y

@[simp]
theorem evaluateGradedValue_zsmul
    (X Y : ComplexCategory) (n : ℤ) (r : ℤ) (x : quotientGradedModule X Y n) :
    E.evaluateGradedValue X Y n (r • x) =
      r • E.evaluateGradedValue X Y n x := by
  exact (E.evaluateGradedModule X Y n).hom.toAddMonoidHom.map_zsmul r x

/-- Evaluate one coefficient-changed quotient degree in the target Hom complex. -/
def evaluateCoefficientDegree
    (X Y : ComplexCategory) (n : ℤ) :
    quotientCoefficientModule (quotientGradedModule X Y n) ⟶
      (E.hom X Y).X n := by
  letI : Module QuotientCoefficientRing
      (quotientCoefficientModule (quotientGradedModule X Y n)) :=
    (quotientCoefficientModule (quotientGradedModule X Y n)).isModule
  letI : Module QuotientCoefficientRing ((E.hom X Y).X n) :=
    ((E.hom X Y).X n).isModule
  exact ModuleCat.ofHom {
    toFun := fun x ↦ E.evaluateGradedValue X Y n x.down
    map_add' := fun x y ↦ E.evaluateGradedValue_add X Y n x.down y.down
    map_smul' := by
      intro r x
      rcases r with ⟨r⟩
      rw [RingHom.id_apply]
      have hy : (ULift.up r : QuotientCoefficientRing) •
          E.evaluateGradedValue X Y n x.down =
        r • E.evaluateGradedValue X Y n x.down := by
        change (r : QuotientCoefficientRing) • E.evaluateGradedValue X Y n x.down = _
        exact Int.cast_smul_eq_zsmul QuotientCoefficientRing r
          (E.evaluateGradedValue X Y n x.down)
      rw [hy]
      simp only [ULift.smul_down, ULift.smul_def]
      exact E.evaluateGradedValue_zsmul X Y n r x.down }

@[simp]
theorem evaluateGradedValue_inclusion
    {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) (x : summandModule s.2) :
    E.evaluateGradedValue X Y n
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s).hom
            (ULift.up x)) =
      E.evaluateWord s.1 s.2 x := by
  exact E.evaluateGradedModule_inclusion s x

@[simp]
theorem evaluateCoefficientDegree_apply_up
    (X Y : ComplexCategory) (n : ℤ) (x : quotientGradedModule X Y n) :
    (E.evaluateCoefficientDegree X Y n).hom (ULift.up x) =
      E.evaluateGradedValue X Y n x := rfl

@[simp]
theorem evaluateCoefficientDegree_inclusion
    {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) (x : summandModule s.2) :
    (E.evaluateCoefficientDegree X Y n).hom
        (ULift.up
          ((Limits.Sigma.ι
            (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s).hom
              (ULift.up x))) =
      E.evaluateWord s.1 s.2 x := by
  rw [evaluateCoefficientDegree_apply_up, evaluateGradedValue_inclusion]

end AnnihilatingEnrichedFunctorData

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
