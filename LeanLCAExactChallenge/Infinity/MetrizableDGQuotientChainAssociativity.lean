/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainAssociativityTransport

/-! # Associativity for the smart-truncated corrected quotient enrichment -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

theorem quotientDGChainEnrichedComp_assoc (W X Y Z : CorrectedQuotientDGCategory) :
    (α_ (quotientDGChainEnrichedHom W X)
      (quotientDGChainEnrichedHom X Y)
      (quotientDGChainEnrichedHom Y Z)).inv ≫
        quotientDGChainEnrichedComp W X Y ▷ quotientDGChainEnrichedHom Y Z ≫
        quotientDGChainEnrichedComp W Y Z =
      quotientDGChainEnrichedHom W X ◁ quotientDGChainEnrichedComp X Y Z ≫
        quotientDGChainEnrichedComp W X Z := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono (((quotientDGEnrichedHom W Z).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f]
  apply GradedObject.Monoidal.tensorObj₃_ext
  intro p q r h
  have hassoc :
      (α_ (quotientDGChainEnrichedHom W X)
        (quotientDGChainEnrichedHom X Y)
        (quotientDGChainEnrichedHom Y Z)).inv.f n =
        (GradedObject.Monoidal.associator
          (quotientDGChainEnrichedHom W X).X
          (quotientDGChainEnrichedHom X Y).X
          (quotientDGChainEnrichedHom Y Z).X).inv n := rfl
  rw [hassoc]
  simp only [Category.assoc]
  set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
      rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc]
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq
    (quotientDGChainEnrichedHom W X).X
    (quotientDGChainEnrichedHom X Y).X
    (quotientDGChainEnrichedHom Y Z).X p q r n h (p + q) rfl]
  rw [GradedObject.Monoidal.ιTensorObj₃_eq
    (quotientDGChainEnrichedHom W X).X
    (quotientDGChainEnrichedHom X Y).X
    (quotientDGChainEnrichedHom Y Z).X p q r n h (q + r) rfl]
  have hwr :
      (quotientDGChainEnrichedComp W X Y ▷ (quotientDGChainEnrichedHom Y Z)).f n =
        (HomologicalComplex.tensorHom
          (quotientDGChainEnrichedComp W X Y) (𝟙 (quotientDGChainEnrichedHom Y Z))).f n := rfl
  have hwl :
      ((quotientDGChainEnrichedHom W X) ◁ quotientDGChainEnrichedComp X Y Z).f n =
        (HomologicalComplex.tensorHom (𝟙 (quotientDGChainEnrichedHom W X))
          (quotientDGChainEnrichedComp X Y Z)).f n := rfl
  rw [hwr, hwl]
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj
              (quotientDGChainEnrichedHom W X).X
              (quotientDGChainEnrichedHom X Y).X)
            (quotientDGChainEnrichedHom Y Z).X
            (p + q) r n h ≫
          (HomologicalComplex.tensorHom
            (quotientDGChainEnrichedComp W X Y) (𝟙 (quotientDGChainEnrichedHom Y Z))).f n =
        ((quotientDGChainEnrichedComp W X Y).f (p + q) ⊗ₘ
            𝟙 ((quotientDGChainEnrichedHom Y Z).X r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (quotientDGChainEnrichedHom W Y).X (quotientDGChainEnrichedHom Y Z).X
            (p + q) r n h := by
    exact quotientChain_ιTensorObj_tensorHom
      (quotientDGChainEnrichedComp W X Y) (𝟙 (quotientDGChainEnrichedHom Y Z)) h
  have houterR :
      GradedObject.Monoidal.ιTensorObj
            (quotientDGChainEnrichedHom W X).X
            (GradedObject.Monoidal.tensorObj
              (quotientDGChainEnrichedHom X Y).X
              (quotientDGChainEnrichedHom Y Z).X)
            p (q + r) n (show p + (q + r) = n by omega) ≫
          (HomologicalComplex.tensorHom (𝟙 (quotientDGChainEnrichedHom W X))
            (quotientDGChainEnrichedComp X Y Z)).f n =
        (𝟙 ((quotientDGChainEnrichedHom W X).X p) ⊗ₘ
            (quotientDGChainEnrichedComp X Y Z).f (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj (quotientDGChainEnrichedHom W X).X
            (quotientDGChainEnrichedHom X Z).X p (q + r) n
              (show p + (q + r) = n by omega) := by
    exact quotientChain_ιTensorObj_tensorHom
      (𝟙 (quotientDGChainEnrichedHom W X)) (quotientDGChainEnrichedComp X Y Z)
      (show p + (q + r) = n by omega)
  simp only [Category.assoc]
  have hleftRaw := congrArg
    (fun t =>
      (α_ ((quotientDGChainEnrichedHom W X).X p)
          ((quotientDGChainEnrichedHom X Y).X q)
          ((quotientDGChainEnrichedHom Y Z).X r)).inv ≫
        (GradedObject.Monoidal.ιTensorObj
            (quotientDGChainEnrichedHom W X).X
            (quotientDGChainEnrichedHom X Y).X p q (p + q) rfl ▷
          (quotientDGChainEnrichedHom Y Z).X r) ≫
        t ≫ (quotientDGChainEnrichedComp W Y Z).f n ≫
          ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n)
    houterL
  have hrightRaw := congrArg
    (fun t =>
      ((quotientDGChainEnrichedHom W X).X p ◁
          GradedObject.Monoidal.ιTensorObj
            (quotientDGChainEnrichedHom X Y).X
            (quotientDGChainEnrichedHom Y Z).X
          q r (q + r) rfl) ≫
        t ≫ (quotientDGChainEnrichedComp W X Z).f n ≫
          ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n)
    houterR
  have hleft := hleftRaw
  have hright := hrightRaw
  simp only [Category.assoc] at hleft hright
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  have hcompL₀ :=
    ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp W X Y) (show p + q = p + q by rfl)
  have hcompL := congrArg
    (fun t => t ▷ (quotientDGChainEnrichedHom Y Z).X r) hcompL₀
  simp only [MonoidalCategory.comp_whiskerRight] at hcompL
  have houterCompL :
      HomologicalComplex.ιTensorObj
          ((quotientDGEnrichedHom W Y).truncLE' ComplexShape.embeddingDownNat)
          ((quotientDGEnrichedHom Y Z).truncLE' ComplexShape.embeddingDownNat)
          (p + q) r n h ≫
        quotientTruncatedMapDegree (quotientDGEnrichedComp W Y Z) n ≫
        ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((quotientDGEnrichedHom W Y).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f (p + q) ⊗ₘ
        ((quotientDGEnrichedHom Y Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f r) ≫
        quotientDGCompositionComponent Z.unop Y.unop W.unop (by
          change (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ)
          omega) := by
    have hi := ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp W Y Z) h
    have hi' := congrArg (fun t => t ≫
      ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n) hi
    have hr := quotientTruncatedCompositionComponent_to_raw W Y Z h
    simpa only [Category.assoc] using hi'.trans hr
  have hcompR₀ :=
    ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp X Y Z) (show q + r = q + r by rfl)
  have hcompR := congrArg
    (fun t => (quotientDGChainEnrichedHom W X).X p ◁ t) hcompR₀
  simp only [MonoidalCategory.whiskerLeft_comp] at hcompR
  have houterCompR :
      HomologicalComplex.ιTensorObj
          ((quotientDGEnrichedHom W X).truncLE' ComplexShape.embeddingDownNat)
          ((quotientDGEnrichedHom X Z).truncLE' ComplexShape.embeddingDownNat)
          p (q + r) n (by omega) ≫
        quotientTruncatedMapDegree (quotientDGEnrichedComp W X Z) n ≫
        ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((quotientDGEnrichedHom W X).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((quotientDGEnrichedHom X Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f (q + r)) ≫
        quotientDGCompositionComponent Z.unop X.unop W.unop (by
          change (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ)
          omega) := by
    have hi := ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp W X Z) (show p + (q + r) = n by omega)
    have hi' := congrArg (fun t => t ≫
      ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n) hi
    have hr := quotientTruncatedCompositionComponent_to_raw W X Z
      (show p + (q + r) = n by omega)
    simpa only [Category.assoc] using hi'.trans hr
  have hL₁Raw := congrArg
    (fun t =>
      (α_ ((quotientDGChainEnrichedHom W X).X p)
          ((quotientDGChainEnrichedHom X Y).X q)
          ((quotientDGChainEnrichedHom Y Z).X r)).inv ≫
        t ≫
        GradedObject.Monoidal.ιTensorObj
          (quotientDGChainEnrichedHom W Y).X
          (quotientDGChainEnrichedHom Y Z).X (p + q) r n h ≫
        (quotientDGChainEnrichedComp W Y Z).f n ≫
        ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n)
    hcompL
  have hL₂Raw := congrArg
    (fun t =>
      (α_ ((quotientDGChainEnrichedHom W X).X p)
          ((quotientDGChainEnrichedHom X Y).X q)
          ((quotientDGChainEnrichedHom Y Z).X r)).inv ≫
        (quotientTruncatedMapComponent
          (quotientDGEnrichedComp W X Y) rfl ▷
            (quotientDGChainEnrichedHom Y Z).X r) ≫ t)
    houterCompL
  have hR₁Raw := congrArg
    (fun t =>
      t ≫
        GradedObject.Monoidal.ιTensorObj
          (quotientDGChainEnrichedHom W X).X
          (quotientDGChainEnrichedHom X Z).X p (q + r) n (by omega) ≫
        (quotientDGChainEnrichedComp W X Z).f n ≫
        ((quotientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n)
    hcompR
  have hR₂Raw := congrArg
    (fun t =>
      ((quotientDGChainEnrichedHom W X).X p ◁
          quotientTruncatedMapComponent
            (quotientDGEnrichedComp X Y Z) rfl) ≫ t)
    houterCompR
  have hL₁ := hL₁Raw
  have hL₂ := hL₂Raw
  have hR₁ := hR₁Raw
  have hR₂ := hR₂Raw
  simp only [Category.assoc] at hL₁ hL₂ hR₁ hR₂
  have hleftComponents := hL₁.trans hL₂
  have hrightComponents := hR₁.trans hR₂
  refine hleftComponents.trans ?_
  refine Eq.trans ?_ hrightComponents.symm
  have hraw := quotientDGCompositionComponent_assoc_natNeg
    W.unop X.unop Y.unop Z.unop h
  have htransport := quotientDGChain_assoc_transport
    (V := ModuleCat.{1} QuotientCoefficientRing)
    (A₀ := (quotientDGChainEnrichedHom W X).X p)
    (B₀ := (quotientDGChainEnrichedHom X Y).X q)
    (C₀ := (quotientDGChainEnrichedHom Y Z).X r)
    (A := (quotientDGEnrichedHom W X).X (-(p : ℤ)))
    (B := (quotientDGEnrichedHom X Y).X (-(q : ℤ)))
    (C' := (quotientDGEnrichedHom Y Z).X (-(r : ℤ)))
    (AB₀ := (quotientDGChainEnrichedHom W Y).X (p + q))
    (BC₀ := (quotientDGChainEnrichedHom X Z).X (q + r))
    (AB := (quotientDGEnrichedHom W Y).X (-((p + q : ℕ) : ℤ)))
    (BC := (quotientDGEnrichedHom X Z).X (-((q + r : ℕ) : ℤ)))
    (D := (quotientDGEnrichedHom W Z).X (-(n : ℤ)))
    (((quotientDGEnrichedHom W X).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f p)
    (((quotientDGEnrichedHom X Y).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f q)
    (((quotientDGEnrichedHom Y Z).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f r)
    (quotientTruncatedMapComponent (quotientDGEnrichedComp W X Y) rfl)
    (((quotientDGEnrichedHom W Y).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f (p + q))
    (quotientDGCompositionComponent Y.unop X.unop W.unop (by omega))
    (quotientTruncatedMapComponent (quotientDGEnrichedComp X Y Z) rfl)
    (((quotientDGEnrichedHom X Z).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f (q + r))
    (quotientDGCompositionComponent Z.unop Y.unop X.unop (by omega))
    (quotientDGCompositionComponent Z.unop Y.unop W.unop (by omega))
    (quotientDGCompositionComponent Z.unop X.unop W.unop (by omega))
    (quotientTruncatedCompositionComponent_to_raw W X Y rfl)
    (quotientTruncatedCompositionComponent_to_raw X Y Z rfl)
    hraw
  simpa only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using htransport

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
