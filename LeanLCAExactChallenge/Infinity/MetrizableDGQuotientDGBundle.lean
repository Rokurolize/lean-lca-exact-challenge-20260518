/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionMerge
import Mathlib.Algebra.Homology.Monoidal

/-! # DG enrichment for the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- The monoidal carrier of the corrected quotient enrichment. -/
abbrev QuotientDGCochain :=
  CochainComplex (ModuleCat.{1} QuotientCoefficientRing) ℤ

/-- The coefficient-changed quotient differential in degree `n`. -/
def quotientCoefficientDifferential
    (X Y : ComplexCategory) (n : ℤ) :
    quotientCoefficientModule (quotientGradedModule X Y n) ⟶
      quotientCoefficientModule (quotientGradedModule X Y (n + 1)) :=
  ModuleCat.ofHom
    (quotientLinearMapChangeScalars (quotientTotalDifferential X Y n).hom)

/-- Quotient composition satisfies the cochain Leibniz identity after coefficient change. -/
theorem quotientCompositionTensorMap_leibniz
    (X Y Z : ComplexCategory) (n m : ℤ) :
  quotientCompositionTensorMap X Y Z n m ≫
      quotientCoefficientDifferential X Z (n + m) =
    ((𝟙 _ ⊗ₘ quotientCoefficientDifferential Y Z m) ≫
        quotientCompositionTensorMap X Y Z n (m + 1) ≫
        eqToHom (congrArg
          (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
          (rightLeibnizDegreeEq n m))) +
      m.negOnePow •
        ((quotientCoefficientDifferential X Y n ⊗ₘ 𝟙 _) ≫
          quotientCompositionTensorMap X Y Z (n + 1) m ≫
          eqToHom (congrArg
            (fun k ↦ quotientCoefficientModule (quotientGradedModule X Z k))
            (leftLeibnizDegreeEq n m))) := by
  apply quotientCoefficientTensorMap_ext_on_summands
  rintro ⟨w, d⟩ ⟨v, e⟩ x y
  have hright :
      (quotientTotalDifferential Y Z m).hom
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u)
            ⟨v, e⟩).hom y) =
        (internalDifferentialFromSummand e +
          contractionDifferentialFromSummand e).hom y := by
    change
      (Limits.Sigma.ι
        (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u)
        ⟨v, e⟩ ≫ quotientTotalDifferential Y Z m).hom y = _
    rw [quotientTotalDifferential_inclusion]
  have hleft :
      (quotientTotalDifferential X Y n).hom
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u)
            ⟨w, d⟩).hom x) =
        (internalDifferentialFromSummand d +
          contractionDifferentialFromSummand d).hom x := by
    change
      (Limits.Sigma.ι
        (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u)
        ⟨w, d⟩ ≫ quotientTotalDifferential X Y n).hom x = _
    rw [quotientTotalDifferential_inclusion]
  unfold quotientCoefficientDifferential
  rw [quotientCompositionTensorMap_comp_changeScalars_tmul]
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  rw [quotientCompositionTensorMap_changeScalars_right_cast_tmul] <;> try omega
  rw [Units.smul_def]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [quotientCompositionTensorMap_changeScalars_left_cast_tmul] <;> try omega
  apply ULift.down_injective
  rw [quotientCompositionMap_on_summands, hright, hleft]
  change _ = _ + (m.negOnePow : ℤ) • _
  simpa only [Units.smul_def] using largeSummandCompositionMap_leibniz d e x y

/-- The coefficient-module span-singleton morphism at the quotient identity element. -/
def quotientIdentitySpan (K : ComplexCategory) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      quotientCoefficientModule (quotientGradedModule K K 0) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton QuotientCoefficientRing _
    (ULift.up (quotientIdentityElement K)))

/-- The quotient identity element, regarded as a chain map from the monoidal unit. -/
def quotientDGIdentity (K : ComplexCategory) :
    𝟙_ QuotientDGCochain ⟶ quotientCoefficientCochainComplex K K :=
  HomologicalComplex.mkHomFromSingle (quotientIdentitySpan K) (by
    rintro _ rfl
    rw [quotientCoefficientCochainComplex_d_succ K K 0]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.down_injective
    change (quotientTotalDifferential K K 0).hom
      (x.down • quotientIdentityElement K) = 0
    calc
      _ = x.down • (quotientTotalDifferential K K 0).hom
          (quotientIdentityElement K) :=
        (quotientTotalDifferential K K 0).hom.toAddMonoidHom.map_zsmul _ _
      _ = 0 := by rw [quotientIdentityElement_closed, zsmul_zero])

@[simp]
theorem quotientDGIdentity_f_zero (K : ComplexCategory) :
    (quotientDGIdentity K).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).hom ≫
        quotientIdentitySpan K := by
  unfold quotientDGIdentity
  apply HomologicalComplex.mkHomFromSingle_f

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
