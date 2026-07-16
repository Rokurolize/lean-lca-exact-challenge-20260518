/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGBundle

/-! # Laws for the corrected quotient DG composition -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

@[reassoc]
private lemma ιTensorObj_tensorHom_local
    {K₁ K₂ L₁ L₂ : QuotientDGCochain} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

theorem quotientDGIdentity_comp (K L : ComplexCategory) :
    (λ_ (quotientCoefficientCochainComplex L K)).inv ≫
        quotientDGIdentity K ▷ quotientCoefficientCochainComplex L K ≫
        quotientDGComposition L K K =
      𝟙 (quotientCoefficientCochainComplex L K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (((HomologicalComplex.leftUnitor'
      (quotientCoefficientCochainComplex L K)).inv n ≫ _) ≫ _) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (quotientDGIdentity K)
      (𝟙 (quotientCoefficientCochainComplex L K))).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  rw [quotientDGIdentity_f_zero]
  slice_lhs 4 5 =>
    rw [quotientDGComposition_f]
    apply HomologicalComplex.ι_mapBifunctorDesc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
    have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : QuotientCoefficientRing)
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [hone]
  change (eqToHom (congrArg
      (fun k ↦ quotientCoefficientModule (quotientGradedModule L K k))
      ((Int.add_comm n 0).trans (zero_add n)))).hom
        ((quotientCompositionTensorMap L K K n 0).hom
          ((((β_
              (quotientCoefficientModule (quotientGradedModule K K 0))
              (quotientCoefficientModule (quotientGradedModule L K n))).hom :
                quotientCoefficientModule (quotientGradedModule K K 0) ⊗
                    quotientCoefficientModule (quotientGradedModule L K n) ⟶
                  quotientCoefficientModule (quotientGradedModule L K n) ⊗
                    quotientCoefficientModule (quotientGradedModule K K 0))).hom
            ((quotientIdentitySpan K).hom 1 ⊗ₜ[QuotientCoefficientRing]
              ULift.up x))) = ULift.up x
  rw [show (quotientIdentitySpan K).hom 1 =
      ULift.up (quotientIdentityElement K) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply]
  rw [quotientCompositionTensorMap_tmul]
  rw [quotientCoefficient_eqToHom_apply_up] <;> try omega
  change ULift.up
      ((eqToHom (congrArg (quotientGradedModule L K)
        ((Int.add_comm n 0).trans (zero_add n)))).hom
          (quotientCompositionMap L K K n 0 x (quotientIdentityElement K))) =
    ULift.up x
  apply ULift.down_injective
  exact quotientCompositionMap_right_unit L K n x

theorem quotientDG_comp_identity (K L : ComplexCategory) :
    (ρ_ (quotientCoefficientCochainComplex L K)).inv ≫
        quotientCoefficientCochainComplex L K ◁ quotientDGIdentity L ≫
        quotientDGComposition L L K =
      𝟙 (quotientCoefficientCochainComplex L K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (((HomologicalComplex.rightUnitor'
      (quotientCoefficientCochainComplex L K)).inv n ≫ _) ≫ _) = _
  rw [HomologicalComplex.rightUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (𝟙 (quotientCoefficientCochainComplex L K))
      (quotientDGIdentity L)).f n
    rw [ιTensorObj_tensorHom_local]
  simp only [Category.assoc, HomologicalComplex.id_f]
  rw [quotientDGIdentity_f_zero]
  slice_lhs 4 5 =>
    rw [quotientDGComposition_f]
    apply HomologicalComplex.ι_mapBifunctorDesc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x⟩
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
    have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : QuotientCoefficientRing)
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [hone]
  change (eqToHom (congrArg
      (fun k ↦ quotientCoefficientModule (quotientGradedModule L K k))
      ((Int.add_comm 0 n).trans (add_zero n)))).hom
        ((quotientCompositionTensorMap L L K 0 n).hom
          ((β_ ((quotientCoefficientCochainComplex L K).X n)
            ((quotientCoefficientCochainComplex L L).X 0)).hom.hom
            (ULift.up x ⊗ₜ[QuotientCoefficientRing]
              (quotientIdentitySpan L).hom 1))) = ULift.up x
  rw [show (quotientIdentitySpan L).hom 1 =
      ULift.up (quotientIdentityElement L) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply]
  rw [quotientCompositionTensorMap_tmul]
  rw [quotientCoefficient_eqToHom_apply_up] <;> try omega
  change ULift.up
      ((eqToHom (congrArg (quotientGradedModule L K)
        ((Int.add_comm 0 n).trans (add_zero n)))).hom
          (quotientCompositionMap L L K 0 n (quotientIdentityElement L) x)) =
    ULift.up x
  apply ULift.down_injective
  exact quotientCompositionMap_left_unit L K n x

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
