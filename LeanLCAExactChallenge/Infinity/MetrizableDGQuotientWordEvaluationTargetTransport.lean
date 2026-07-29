/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionMap

/-! # Common positive target transport for corrected Drinfeld word evaluation

The evaluation recursion and the composition recursion construct their positive-word target
coordinates differently.  This module proves that both constructions are equality transports and
that their hom maps coincide exactly.
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

private theorem comp_eqToHom
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (hf : ∃ h : A = B, f = eqToHom h)
    (hg : ∃ h : B = C, g = eqToHom h) :
    ∃ h : A = C, f ≫ g = eqToHom h := by
  obtain ⟨hAB, rfl⟩ := hf
  obtain ⟨hBC, rfl⟩ := hg
  exact ⟨hAB.trans hBC, by simp⟩

private theorem eqToHom_heq_id
    {A B : ModuleCat.{0} ℤ} (h : A = B) :
    HEq (eqToHom h) (𝟙 A) := by
  subst B
  rfl

private theorem summandModuleCastWordIso_hom_eqToHom
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    ∃ hM : summandModule d = summandModule (d.castWord h),
      (summandModuleCastWordIso h d).hom = eqToHom hM := by
  subst v
  exact ⟨rfl, rfl⟩

/-- Transport on a tensor product is the tensor of the two transports. -/
theorem tensor_eqToHom
    {A A' B B' : ModuleCat.{0} ℤ} (hA : A = A') (hB : B = B') :
    eqToHom (congrArg₂ (fun X Y : ModuleCat.{0} ℤ ↦ X ⊗ Y) hA hB) =
      eqToHom hA ⊗ₘ eqToHom hB := by
  subst A'
  subst B'
  exact (MonoidalCategory.id_tensorHom_id A B).symm

/-- The recursive evaluation-side tail transport is one equality transport. -/
theorem positiveAppendTailSummandIso_hom_eqToHom
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    ∃ h : summandModule (tailDegreeProfile (positiveAppendDegreeProfile d e)) =
        summandModule ((tailDegreeProfile d).append e),
      (positiveAppendTailSummandIso d e).hom = eqToHom h := by
  unfold positiveAppendTailSummandIso summandModuleTransportIso
  simp only [Iso.trans_hom, eqToIso.hom]
  exact comp_eqToHom _ _ ⟨_, rfl⟩ ⟨_, rfl⟩

/-- The evaluation-side positive target transport is heterogeneously the identity. -/
theorem positiveAppendSummandIso_hom_heq_id
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq (positiveAppendSummandIso d e).hom
      (𝟙 (summandModule (d.append e))) := by
  unfold positiveAppendSummandIso
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, eqToIso.hom]
  obtain ⟨h₁, hh₁⟩ := summandModuleCastWordIso_hom_eqToHom
    (positiveAppendWord_eq_append intermediate v).symm (d.append e)
  obtain ⟨h₃, hh₃⟩ := positiveAppendTailSummandIso_hom_eqToHom d e
  let h₂ := summandModule_succ (positiveAppendDegreeProfile d e)
  let hHead := positiveAppendFactorModule_zero d e
  have hTensor : ∃ h,
      (eqToHom hHead ⊗ₘ (positiveAppendTailSummandIso d e).hom) = eqToHom h := by
    rw [hh₃]
    exact ⟨congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hHead h₃,
      (tensor_eqToHom hHead h₃).symm⟩
  have hFirst : ∃ h,
      (summandModuleCastWordIso
          (positiveAppendWord_eq_append intermediate v).symm
          (d.append e)).hom ≫ eqToHom h₂ = eqToHom h :=
    comp_eqToHom _ _ ⟨h₁, hh₁⟩ ⟨h₂, rfl⟩
  rw [← Category.assoc]
  obtain ⟨h, hh⟩ := comp_eqToHom _ _ hFirst hTensor
  rw [hh]
  exact eqToHom_heq_id h

/-- The composition-side positive target transport is heterogeneously the identity. -/
theorem positiveCompositionTargetIso_hom_heq_id
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq (positiveCompositionTargetIso d e).hom
      (𝟙 (summandModule (d.append e))) := by
  unfold positiveCompositionTargetIso
  simp only [eqToIso.hom]
  exact eqToHom_heq_id _

/-- Evaluation and composition expose the same positive-word target tensor coordinates. -/
theorem positiveAppendSummandIso_hom_eq_positiveCompositionTargetIso_hom
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    (positiveAppendSummandIso d e).hom =
      (positiveCompositionTargetIso d e).hom := by
  exact eq_of_heq ((positiveAppendSummandIso_hom_heq_id d e).trans
    (positiveCompositionTargetIso_hom_heq_id d e).symm)

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
