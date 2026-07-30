/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedCoefficientUniqueness
import Mathlib.CategoryTheory.Enriched.Basic

/-! # Unit-graded transformations for the corrected Drinfeld quotient

The ambient cochain category is monoidal but is not currently bundled as braided.  The tensor
unit nevertheless has its canonical half-braiding, so it is an object of the Drinfeld center.
Transformations graded by this center object are the strict enriched natural transformations
needed by the quotient universal property.
-/

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

/-- The canonical central tensor unit of the quotient cochain category. -/
noncomputable abbrev QuotientDGCentralUnit : Center QuotientDGCochain :=
  𝟙_ (Center QuotientDGCochain)

/-- A strict unit-graded enriched natural transformation. -/
abbrev QuotientDGUnitGradedNatTrans
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F G : EnrichedFunctor QuotientDGCochain C D) :=
  GradedNatTrans QuotientDGCentralUnit F G

/-- The degree-zero element represented by one component of a unit-graded transformation. -/
def quotientDGUnitGradedNatTransElement
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G) (X : C) :
    (F.obj X ⟶[QuotientDGCochain] G.obj X).X 0 :=
  (α.app X).f 0
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)

/-- The identity unit-graded enriched natural transformation. -/
noncomputable def quotientDGUnitGradedNatTransId
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F : EnrichedFunctor QuotientDGCochain C D) :
    QuotientDGUnitGradedNatTrans F F where
  app X := eId QuotientDGCochain (F.obj X)
  naturality X Y := by
    change ((𝟙_ (Center QuotientDGCochain)).2.β
        (X ⟶[QuotientDGCochain] Y)).hom ≫
        (F.map X Y ⊗ₘ eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain _ _ _ =
      (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
        eComp QuotientDGCochain _ _ _
    rw [Center.tensorUnit_β]
    simp only [Iso.trans_hom, Iso.symm_hom]
    change ((λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫
        (ρ_ (X ⟶[QuotientDGCochain] Y)).inv) ≫
        (F.map X Y ⊗ₘ eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain _ _ _ =
      (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
        eComp QuotientDGCochain _ _ _
    have hid :
        (eId QuotientDGCochain (F.obj X) ▷
            (F.obj X ⟶[QuotientDGCochain] F.obj Y)) ≫
            eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) =
          (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).hom := by
      rw [← cancel_epi (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv]
      simp only [e_id_comp, Iso.inv_hom_id]
    have hcomp :
        (ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) =
        𝟙 (F.obj X ⟶[QuotientDGCochain] F.obj Y) :=
      e_comp_id QuotientDGCochain (F.obj X) (F.obj Y)
    calc
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫
          (ρ_ (X ⟶[QuotientDGCochain] Y)).inv ≫
          (F.map X Y ▷ 𝟙_ QuotientDGCochain) ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) := by
            rw [MonoidalCategory.tensorHom_def]
            simp only [Category.assoc]
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y ≫
          (ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) := by
            rw [← MonoidalCategory.rightUnitor_inv_naturality_assoc]
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y ≫
          ((ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y)) := by
            rfl
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y := by
            rw [hcomp, Category.comp_id]
      _ = (𝟙_ QuotientDGCochain ◁ F.map X Y) ≫
          (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).hom := by
            exact (MonoidalCategory.leftUnitor_naturality (F.map X Y)).symm
      _ = (𝟙_ QuotientDGCochain ◁ F.map X Y) ≫
          (eId QuotientDGCochain (F.obj X) ▷
            (F.obj X ⟶[QuotientDGCochain] F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) := by
            rw [hid]
      _ = (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) := by
            rw [MonoidalCategory.tensorHom_def']
            simp only [Category.assoc]

@[simp]
theorem quotientDGUnitGradedNatTransId_element
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F : EnrichedFunctor QuotientDGCochain C D) (X : C) :
    quotientDGUnitGradedNatTransElement
        (quotientDGUnitGradedNatTransId F) X =
      targetDGIdentityElement (F.obj X) :=
  rfl

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
