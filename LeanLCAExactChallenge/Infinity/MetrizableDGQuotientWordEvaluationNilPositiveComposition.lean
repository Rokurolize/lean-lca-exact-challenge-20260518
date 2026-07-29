/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationNilPositiveCoordinates

/-! # Zero-left/positive-right composition coordinates

This module identifies the boundary operation appearing when a zero-length corrected Drinfeld
word is composed on the left of a positive word.  In the normalized positive coordinates the
boundary factor is exactly ordinary DG composition of the zero-word factor with the positive
word's head factor.
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

/-- The normalized composite head is the ordinary Hom module in the summed degree. -/
theorem nilPositiveHeadFactor_eq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (nilPositiveDegreeProfile (W := W) p d) 0 =
      (dgHomZModuleCochainComplex W (intermediate 0).obj).X
        (p + d.arrowDegree 0) := by
  rw [factorModule_zero_succ,
    nilPositiveDegreeProfile_arrowDegree_zero]

/-- The raw boundary module is the ordinary source-to-first-intermediate Hom module. -/
def nilPositiveBoundaryDirectEq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionBoundaryModule (nilDegreeProfile W X p) d =
      (dgHomZModuleCochainComplex W (intermediate 0).obj).X
        (p + d.arrowDegree 0) := by
  unfold compositionBoundaryModule
  have htarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).arrowTarget 0 = (intermediate 0).obj := by
    unfold arrowTarget vertex object
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
  rw [htarget]
  rfl

/-- The raw boundary source is the tensor product of the two ordinary Hom modules. -/
def nilPositiveBoundarySourceDirectEq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (nilDegreeProfile W X p) 0 ⊗ factorModule d 0 =
      (dgHomZModuleCochainComplex W X).X p ⊗
        (dgHomZModuleCochainComplex X (intermediate 0).obj).X
          (d.arrowDegree 0) :=
  congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
    (factorModule_nilDegreeProfile W X p) (factorModule_zero_succ d)

/-- The generic composition boundary is the first factor of the normalized positive composite. -/
theorem nilPositiveBoundaryModule_eq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionBoundaryModule (nilDegreeProfile W X p) d =
      factorModule (nilPositiveDegreeProfile (W := W) p d) 0 :=
  (nilPositiveBoundaryDirectEq (W := W) p d).trans
    (nilPositiveHeadFactor_eq (W := W) p d).symm

/-- Before normalization, the generic boundary map is transported ordinary DG composition. -/
theorem nilPositiveBoundaryMap_direct
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionBoundaryMap (nilDegreeProfile W X p) d ≫
        eqToHom (nilPositiveBoundaryDirectEq (W := W) p d) =
      eqToHom (nilPositiveBoundarySourceDirectEq (W := W) p d) ≫
        dgCochainCompTensorOfEq W X X (intermediate 0).obj rfl rfl := by
  let v : DrinfeldWord X Y :=
    { length := k + 1, intermediate := intermediate }
  let f := compositionBoundaryMap (nilDegreeProfile W X p) d
  let g := dgCochainCompTensorOfEq W X X (intermediate 0).obj rfl
    (show p + d.arrowDegree 0 = p + d.arrowDegree 0 by rfl)
  have htarget : v.arrowTarget 0 = (intermediate 0).obj := by
    unfold v arrowTarget vertex object
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
  have hfg : HEq f g := by
    unfold f g compositionBoundaryMap
    exact dgCochainCompTensorOfEq_heq rfl rfl
      (arrowSource_zero_eq_source v) htarget
      (show (nil W X).arrowTarget 0 = v.arrowSource 0 by
        rw [nil_arrowTarget_zero, arrowSource_zero_eq_source])
      rfl rfl rfl rfl rfl rfl
  have htransport := map_eq_transport_comp_of_heq
    (nilPositiveBoundarySourceDirectEq (W := W) p d)
    (nilPositiveBoundaryDirectEq (W := W) p d) f g hfg
  calc
    f ≫ eqToHom (nilPositiveBoundaryDirectEq (W := W) p d) =
        (eqToHom (nilPositiveBoundarySourceDirectEq (W := W) p d) ≫
          g ≫ eqToHom (nilPositiveBoundaryDirectEq (W := W) p d).symm) ≫
            eqToHom (nilPositiveBoundaryDirectEq (W := W) p d) := by
      rw [htransport]
    _ = eqToHom (nilPositiveBoundarySourceDirectEq (W := W) p d) ≫ g := by
      simp

/-- Ordinary DG composition, with its codomain expressed as the normalized composite head. -/
def nilPositiveHeadCompositionMap
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (nilDegreeProfile W X p) 0 ⊗ factorModule d 0 ⟶
      factorModule (nilPositiveDegreeProfile (W := W) p d) 0 :=
  compositionBoundaryMap (nilDegreeProfile W X p) d ≫
    eqToHom (nilPositiveBoundaryModule_eq (W := W) p d)

/-- In ordinary Hom-module coordinates the normalized head map is precisely DG composition. -/
theorem nilPositiveHeadCompositionMap_eq
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B)
        (factorModule_nilDegreeProfile W X p)
        (factorModule_zero_succ d)) ≫
        dgCochainCompTensorOfEq W X X (intermediate 0).obj rfl rfl =
      nilPositiveHeadCompositionMap (W := W) p d ≫
        eqToHom (nilPositiveHeadFactor_eq (W := W) p d) := by
  rw [← nilPositiveBoundaryMap_direct (W := W) p d]
  unfold nilPositiveHeadCompositionMap
  simp only [Category.assoc, eqToHom_trans]

private theorem nilPositiveEqToHom_tensor_apply
    {M M' N N' : ModuleCat.{0} ℤ}
    (hM : M = M') (hN : N = N') (x : M) (y : N) :
    (eqToHom (congrArg₂ (fun A B : ModuleCat.{0} ℤ ↦ A ⊗ B) hM hN)).hom
        (x ⊗ₜ[ℤ] y) =
      (eqToHom hM).hom x ⊗ₜ[ℤ] (eqToHom hN).hom y := by
  subst M'
  subst N'
  rfl

/-- Pure tensors are sent to ordinary DG composition in normalized head coordinates. -/
theorem nilPositiveHeadCompositionMap_apply
    {W X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ} (p : ℤ)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule (nilDegreeProfile W X p) 0)
    (y : factorModule d 0) :
    (eqToHom (nilPositiveHeadFactor_eq (W := W) p d)).hom
      ((nilPositiveHeadCompositionMap (W := W) p d).hom
        (x ⊗ₜ[ℤ] y)) =
      (dgCochainCompTensorOfEq W X X (intermediate 0).obj rfl rfl).hom
        ((eqToHom (factorModule_nilDegreeProfile W X p)).hom x ⊗ₜ[ℤ]
          (eqToHom (factorModule_zero_succ d)).hom y) := by
  have h := ConcreteCategory.congr_hom
    (nilPositiveHeadCompositionMap_eq (W := W) p d)
      (x ⊗ₜ[ℤ] y)
  simp only [ModuleCat.comp_apply] at h
  rw [nilPositiveEqToHom_tensor_apply] at h
  exact h.symm

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
