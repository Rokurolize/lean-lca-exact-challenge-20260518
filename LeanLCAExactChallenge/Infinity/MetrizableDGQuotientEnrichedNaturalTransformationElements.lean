/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedNaturalTransformation

/-! # Elementwise formulas for unit-graded enriched transformations -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

/-- The canonical tensor-unit half-braiding sends `1 ⊗ x` to `x ⊗ 1`. -/
theorem quotientDGCentralUnit_apply
    (K : QuotientDGCochain) (p : ℤ) (x : K.X p) :
    ((((λ_ K).hom ≫ (ρ_ K).inv).f p).hom)
      ((HomologicalComplex.ιTensorObj (𝟙_ QuotientDGCochain) K
        0 p p (zero_add p)).hom
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1
          ⊗ₜ[QuotientCoefficientRing] x)) =
    (HomologicalComplex.ιTensorObj K (𝟙_ QuotientDGCochain)
      p 0 p (add_zero p)).hom
      (x ⊗ₜ[QuotientCoefficientRing]
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1) := by
  have hleftComp :
      (λ_ K).inv.f p = (HomologicalComplex.leftUnitor' K).inv p := rfl
  have hrightComp :
      (ρ_ K).inv.f p = (HomologicalComplex.rightUnitor' K).inv p := rfl
  have hin :
      ((λ_ K).inv.f p).hom x =
        (HomologicalComplex.ιTensorObj (𝟙_ QuotientDGCochain) K
          0 p p (zero_add p)).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1
            ⊗ₜ[QuotientCoefficientRing] x) := by
    rw [hleftComp, HomologicalComplex.leftUnitor'_inv]
    simp only [ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply]
    rfl
  have hout :
      ((ρ_ K).inv.f p).hom x =
        (HomologicalComplex.ιTensorObj K (𝟙_ QuotientDGCochain)
          p 0 p (add_zero p)).hom
          (x ⊗ₜ[QuotientCoefficientRing]
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1) := by
    rw [hrightComp, HomologicalComplex.rightUnitor'_inv]
    simp only [ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply]
    rfl
  rw [← hin, ← hout]
  have hc := (λ_ K).inv_hom_id_assoc (ρ_ K).inv
  have hcp := congrArg (fun f ↦ f.f p) hc
  exact ConcreteCategory.congr_hom hcp x

/-- Enriched naturality evaluated on one homogeneous source element. -/
theorem quotientDGUnitGradedNatTrans_naturality_element
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G)
    (X Y : C) (p : ℤ)
    (x : (X ⟶[QuotientDGCochain] Y).X p) :
    quotientDGComposeElement (F.obj X) (F.obj Y) (G.obj Y)
        p 0 p (by omega) ((F.map X Y).f p x)
        (quotientDGUnitGradedNatTransElement α Y) =
      quotientDGComposeElement (F.obj X) (G.obj X) (G.obj Y)
        0 p p (by omega) (quotientDGUnitGradedNatTransElement α X)
        ((G.map X Y).f p x) := by
  let I := 𝟙_ QuotientDGCochain
  let A := X ⟶[QuotientDGCochain] Y
  let B := F.obj X ⟶[QuotientDGCochain] F.obj Y
  let C' := F.obj Y ⟶[QuotientDGCochain] G.obj Y
  let E := F.obj X ⟶[QuotientDGCochain] G.obj X
  let H := G.obj X ⟶[QuotientDGCochain] G.obj Y
  let T := F.obj X ⟶[QuotientDGCochain] G.obj Y
  let f := F.map X Y
  let g := G.map X Y
  let aY := α.app Y
  let aX := α.app X
  let μL := eComp QuotientDGCochain (F.obj X) (F.obj Y) (G.obj Y)
  let μR := eComp QuotientDGCochain (F.obj X) (G.obj X) (G.obj Y)
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  let u := e.inv.hom (1 : QuotientCoefficientRing)
  let input := (HomologicalComplex.ιTensorObj I A 0 p p (zero_add p)).hom
    (u ⊗ₜ[QuotientCoefficientRing] x)
  have hnat := α.naturality X Y
  rw [Center.tensorUnit_β] at hnat
  simp only [Iso.trans_hom, Iso.symm_hom] at hnat
  have hp := congrArg (fun k : I ⊗ A ⟶ T ↦ k.f p) hnat
  have happ := ConcreteCategory.congr_hom hp input
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at happ
  have hc := quotientDGCentralUnit_apply A p x
  change ((((λ_ A).hom ≫ (ρ_ A).inv).f p).hom input) = _ at hc
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hc
  have hc' :
      (ConcreteCategory.hom ((ρ_ (X ⟶[QuotientDGCochain] Y)).inv.f p))
          ((ConcreteCategory.hom ((λ_ (X ⟶[QuotientDGCochain] Y)).hom.f p))
            input) =
        (HomologicalComplex.ιTensorObj (X ⟶[QuotientDGCochain] Y)
          (𝟙_ QuotientDGCochain) p 0 p (add_zero p)).hom
          (x ⊗ₜ[QuotientCoefficientRing] u) := by
    simpa only [A, u, e] using hc
  have hcmap := congrArg
    (fun z ↦ ((eComp QuotientDGCochain
      (F.obj X) (F.obj Y) (G.obj Y)).f p).hom
        (((F.map X Y ⊗ₘ α.app Y).f p).hom z)) hc'
  have happ1 := hcmap.symm.trans happ
  have hιL := GradedObject.Monoidal.ι_tensorHom f.f aY.f
    p 0 p (add_zero p)
  have hιLapp := ConcreteCategory.congr_hom hιL
    (x ⊗ₜ[QuotientCoefficientRing] u)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιLapp
  have hιR := GradedObject.Monoidal.ι_tensorHom aX.f g.f
    0 p p (zero_add p)
  have hιRapp := ConcreteCategory.congr_hom hιR
    (u ⊗ₜ[QuotientCoefficientRing] x)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιRapp
  have hleft := congrArg (fun z ↦ μL.f p z) hιLapp
  have hright := congrArg (fun z ↦ μR.f p z) hιRapp
  have hfinal := hleft.symm.trans (happ1.trans hright)
  change quotientDGComposeElement (F.obj X) (F.obj Y) (G.obj Y)
      p 0 p (by omega) (f.f p x)
      (quotientDGUnitGradedNatTransElement α Y) =
    quotientDGComposeElement (F.obj X) (G.obj X) (G.obj Y)
      0 p p (by omega) (quotientDGUnitGradedNatTransElement α X)
      (g.f p x) at hfinal
  exact hfinal

/-- Construct a unit-graded enriched transformation from its components and homogeneous
elementwise naturality equations. -/
noncomputable def quotientDGUnitGradedNatTransOfElements
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (app : ∀ X : C, 𝟙_ QuotientDGCochain ⟶
      (F.obj X ⟶[QuotientDGCochain] G.obj X))
    (h : ∀ (X Y : C) (p : ℤ) (x : (X ⟶[QuotientDGCochain] Y).X p),
      quotientDGComposeElement (F.obj X) (F.obj Y) (G.obj Y)
        p 0 p (by omega) ((F.map X Y).f p x)
        (((app Y).f 0).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)) =
      quotientDGComposeElement (F.obj X) (G.obj X) (G.obj Y)
        0 p p (by omega)
        (((app X).f 0).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1))
        ((G.map X Y).f p x)) :
    QuotientDGUnitGradedNatTrans F G where
  app := app
  naturality X Y := by
    rw [Center.tensorUnit_β]
    simp only [Iso.trans_hom, Iso.symm_hom]
    let A := X ⟶[QuotientDGCochain] Y
    rw [← cancel_epi (λ_ A).inv]
    dsimp only [A]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    have hleftComp :
        (ρ_ A).inv.f p = (HomologicalComplex.rightUnitor' A).inv p := rfl
    have hrightComp :
        (λ_ A).inv.f p = (HomologicalComplex.leftUnitor' A).inv p := rfl
    rw [hleftComp, HomologicalComplex.rightUnitor'_inv,
      hrightComp, HomologicalComplex.leftUnitor'_inv]
    simp only [ModuleCat.comp_apply]
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
    let u := e.inv.hom (1 : QuotientCoefficientRing)
    have hιL := GradedObject.Monoidal.ι_tensorHom
      (F.map X Y).f (app Y).f p 0 p (add_zero p)
    have hιLapp := ConcreteCategory.congr_hom hιL
      (x ⊗ₜ[QuotientCoefficientRing] u)
    simp only [ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at hιLapp
    have hιR := GradedObject.Monoidal.ι_tensorHom
      (app X).f (G.map X Y).f 0 p p (zero_add p)
    have hιRapp := ConcreteCategory.congr_hom hιR
      (u ⊗ₜ[QuotientCoefficientRing] x)
    simp only [ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul] at hιRapp
    have hleft := congrArg
      (fun z ↦ ((eComp QuotientDGCochain
        (F.obj X) (F.obj Y) (G.obj Y)).f p).hom z) hιLapp
    have hright := congrArg
      (fun z ↦ ((eComp QuotientDGCochain
        (F.obj X) (G.obj X) (G.obj Y)).f p).hom z) hιRapp
    exact hleft.trans ((h X Y p x).trans hright.symm)

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
