/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientOriginalChainCategory
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainAssociativityTransport

/-! # Associativity for the smart-truncated coefficient-changed original DG category -/

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

lemma originalTruncatedCompositionComponent_to_raw
    (K L M : OriginalCoefficientDGCategory)
    {p q n : ℕ} (h : p + q = n) :
    quotientTruncatedMapComponent (originalCoefficientDGEnrichedComp K L M) h ≫
        ((originalCoefficientDGEnrichedHom K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((originalCoefficientDGEnrichedHom L M).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f q) ≫
        originalDGCompositionComponent M.unop L.unop K.unop (by
          change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
          omega) := by
  rw [quotientTruncatedMapComponent_toRestriction]
  dsimp only [quotientTruncatedMapToCochain,
    originalCoefficientDGEnrichedComp, originalCoefficientDGEnrichedHom]
  simp only [Category.assoc]
  congr 1
  exact ιTensorObj_originalDGComposition M.unop L.unop K.unop (by
    change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
    omega)

theorem originalDGCompositionComponent_assoc_natNeg
    (W X Y Z : ComplexCategory) {p q r n : ℕ} (h : p + q + r = n) :
    (α_ ((OriginalMappingCochain X W).X (-(p : ℤ)))
          ((OriginalMappingCochain Y X).X (-(q : ℤ)))
          ((OriginalMappingCochain Z Y).X (-(r : ℤ)))).inv ≫
        (originalDGCompositionComponent Y X W
              (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega) ⊗ₘ
            𝟙 ((OriginalMappingCochain Z Y).X (-(r : ℤ)))) ≫
        originalDGCompositionComponent Z Y W
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega) =
      (𝟙 ((OriginalMappingCochain X W).X (-(p : ℤ))) ⊗ₘ
          originalDGCompositionComponent Z Y X
            (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega)) ≫
        originalDGCompositionComponent Z X W
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro a b c
  rcases a with ⟨a⟩
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases b with ⟨b⟩
  rcases c with ⟨c⟩
  rcases c with ⟨c⟩
  change
    originalDGCompositionComponent Z Y W
          (show (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ) by omega)
        (originalDGCompositionComponent Y X W
            (show (-(p : ℤ)) + (-(q : ℤ)) = -((p + q : ℕ) : ℤ) by omega)
              (ULift.up (ULift.up a) ⊗ₜ[QuotientCoefficientRing]
                ULift.up (ULift.up b)) ⊗ₜ
            ULift.up (ULift.up c)) =
      originalDGCompositionComponent Z X W
          (show (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ) by omega)
        (ULift.up (ULift.up a) ⊗ₜ
          originalDGCompositionComponent Z Y X
            (show (-(q : ℤ)) + (-(r : ℤ)) = -((q + r : ℕ) : ℤ) by omega)
              (ULift.up (ULift.up b) ⊗ₜ[QuotientCoefficientRing]
                ULift.up (ULift.up c)))
  simp only [originalDGCompositionComponent]
  apply ULift.down_injective
  apply ULift.down_injective
  exact (CochainComplex.HomComplex.Cochain.comp_assoc c b a
    (by omega) (by omega) (by omega)).symm

set_option maxHeartbeats 2000000 in
-- Expanding the threefold tensor coproduct and smart-truncation transports needs extra budget.
theorem originalCoefficientDGChainEnrichedComp_assoc
    (W X Y Z : OriginalCoefficientDGCategory) :
    (α_ (originalCoefficientDGChainEnrichedHom W X)
      (originalCoefficientDGChainEnrichedHom X Y)
      (originalCoefficientDGChainEnrichedHom Y Z)).inv ≫
        originalCoefficientDGChainEnrichedComp W X Y ▷
          originalCoefficientDGChainEnrichedHom Y Z ≫
        originalCoefficientDGChainEnrichedComp W Y Z =
      originalCoefficientDGChainEnrichedHom W X ◁
          originalCoefficientDGChainEnrichedComp X Y Z ≫
        originalCoefficientDGChainEnrichedComp W X Z := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono (((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
    ComplexShape.embeddingDownNat).f n)).1
  simp only [HomologicalComplex.comp_f]
  apply GradedObject.Monoidal.tensorObj₃_ext
  intro p q r h
  have hassoc :
      (α_ (originalCoefficientDGChainEnrichedHom W X)
        (originalCoefficientDGChainEnrichedHom X Y)
        (originalCoefficientDGChainEnrichedHom Y Z)).inv.f n =
        (GradedObject.Monoidal.associator
          (originalCoefficientDGChainEnrichedHom W X).X
          (originalCoefficientDGChainEnrichedHom X Y).X
          (originalCoefficientDGChainEnrichedHom Y Z).X).inv n := rfl
  rw [hassoc]
  simp only [Category.assoc]
  set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
      rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc]
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq
    (originalCoefficientDGChainEnrichedHom W X).X
    (originalCoefficientDGChainEnrichedHom X Y).X
    (originalCoefficientDGChainEnrichedHom Y Z).X p q r n h (p + q) rfl]
  rw [GradedObject.Monoidal.ιTensorObj₃_eq
    (originalCoefficientDGChainEnrichedHom W X).X
    (originalCoefficientDGChainEnrichedHom X Y).X
    (originalCoefficientDGChainEnrichedHom Y Z).X p q r n h (q + r) rfl]
  have hwr :
      (originalCoefficientDGChainEnrichedComp W X Y ▷
          originalCoefficientDGChainEnrichedHom Y Z).f n =
        (HomologicalComplex.tensorHom
          (originalCoefficientDGChainEnrichedComp W X Y)
          (𝟙 (originalCoefficientDGChainEnrichedHom Y Z))).f n := rfl
  have hwl :
      (originalCoefficientDGChainEnrichedHom W X ◁
          originalCoefficientDGChainEnrichedComp X Y Z).f n =
        (HomologicalComplex.tensorHom
          (𝟙 (originalCoefficientDGChainEnrichedHom W X))
          (originalCoefficientDGChainEnrichedComp X Y Z)).f n := rfl
  rw [hwr, hwl]
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj
              (originalCoefficientDGChainEnrichedHom W X).X
              (originalCoefficientDGChainEnrichedHom X Y).X)
            (originalCoefficientDGChainEnrichedHom Y Z).X
            (p + q) r n h ≫
          (HomologicalComplex.tensorHom
            (originalCoefficientDGChainEnrichedComp W X Y)
            (𝟙 (originalCoefficientDGChainEnrichedHom Y Z))).f n =
        ((originalCoefficientDGChainEnrichedComp W X Y).f (p + q) ⊗ₘ
            𝟙 ((originalCoefficientDGChainEnrichedHom Y Z).X r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (originalCoefficientDGChainEnrichedHom W Y).X
            (originalCoefficientDGChainEnrichedHom Y Z).X
            (p + q) r n h := by
    exact originalChain_ιTensorObj_tensorHom
      (originalCoefficientDGChainEnrichedComp W X Y)
      (𝟙 (originalCoefficientDGChainEnrichedHom Y Z)) h
  have houterR :
      GradedObject.Monoidal.ιTensorObj
            (originalCoefficientDGChainEnrichedHom W X).X
            (GradedObject.Monoidal.tensorObj
              (originalCoefficientDGChainEnrichedHom X Y).X
              (originalCoefficientDGChainEnrichedHom Y Z).X)
            p (q + r) n (show p + (q + r) = n by omega) ≫
          (HomologicalComplex.tensorHom
            (𝟙 (originalCoefficientDGChainEnrichedHom W X))
            (originalCoefficientDGChainEnrichedComp X Y Z)).f n =
        (𝟙 ((originalCoefficientDGChainEnrichedHom W X).X p) ⊗ₘ
            (originalCoefficientDGChainEnrichedComp X Y Z).f (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (originalCoefficientDGChainEnrichedHom W X).X
            (originalCoefficientDGChainEnrichedHom X Z).X p (q + r) n
              (show p + (q + r) = n by omega) := by
    exact originalChain_ιTensorObj_tensorHom
      (𝟙 (originalCoefficientDGChainEnrichedHom W X))
      (originalCoefficientDGChainEnrichedComp X Y Z)
      (show p + (q + r) = n by omega)
  simp only [Category.assoc]
  have hleftRaw := congrArg
    (fun t ↦
      (α_ ((originalCoefficientDGChainEnrichedHom W X).X p)
          ((originalCoefficientDGChainEnrichedHom X Y).X q)
          ((originalCoefficientDGChainEnrichedHom Y Z).X r)).inv ≫
        (GradedObject.Monoidal.ιTensorObj
            (originalCoefficientDGChainEnrichedHom W X).X
            (originalCoefficientDGChainEnrichedHom X Y).X p q (p + q) rfl ▷
          (originalCoefficientDGChainEnrichedHom Y Z).X r) ≫
        t ≫ (originalCoefficientDGChainEnrichedComp W Y Z).f n ≫
          ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n)
    houterL
  have hrightRaw := congrArg
    (fun t ↦
      ((originalCoefficientDGChainEnrichedHom W X).X p ◁
          GradedObject.Monoidal.ιTensorObj
            (originalCoefficientDGChainEnrichedHom X Y).X
            (originalCoefficientDGChainEnrichedHom Y Z).X
          q r (q + r) rfl) ≫
        t ≫ (originalCoefficientDGChainEnrichedComp W X Z).f n ≫
          ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f n)
    houterR
  have hleft := hleftRaw
  have hright := hrightRaw
  simp only [Category.assoc] at hleft hright
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  have hcompL₀ :=
    ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp W X Y) (show p + q = p + q by rfl)
  have hcompL := congrArg
    (fun t ↦ t ▷ (originalCoefficientDGChainEnrichedHom Y Z).X r) hcompL₀
  simp only [MonoidalCategory.comp_whiskerRight] at hcompL
  have houterCompL :
      HomologicalComplex.ιTensorObj
          ((originalCoefficientDGEnrichedHom W Y).truncLE' ComplexShape.embeddingDownNat)
          ((originalCoefficientDGEnrichedHom Y Z).truncLE' ComplexShape.embeddingDownNat)
          (p + q) r n h ≫
        quotientTruncatedMapDegree (originalCoefficientDGEnrichedComp W Y Z) n ≫
        ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((originalCoefficientDGEnrichedHom W Y).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f (p + q) ⊗ₘ
        ((originalCoefficientDGEnrichedHom Y Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f r) ≫
        originalDGCompositionComponent Z.unop Y.unop W.unop (by
          change (-((p + q : ℕ) : ℤ)) + (-(r : ℤ)) = -(n : ℤ)
          omega) := by
    have hi := ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp W Y Z) h
    have hi' := congrArg (fun t ↦ t ≫
      ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n) hi
    have hr := originalTruncatedCompositionComponent_to_raw W Y Z h
    simpa only [Category.assoc] using hi'.trans hr
  have hcompR₀ :=
    ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp X Y Z) (show q + r = q + r by rfl)
  have hcompR := congrArg
    (fun t ↦ (originalCoefficientDGChainEnrichedHom W X).X p ◁ t) hcompR₀
  simp only [MonoidalCategory.whiskerLeft_comp] at hcompR
  have houterCompR :
      HomologicalComplex.ιTensorObj
          ((originalCoefficientDGEnrichedHom W X).truncLE' ComplexShape.embeddingDownNat)
          ((originalCoefficientDGEnrichedHom X Z).truncLE' ComplexShape.embeddingDownNat)
          p (q + r) n (by omega) ≫
        quotientTruncatedMapDegree (originalCoefficientDGEnrichedComp W X Z) n ≫
        ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      (((originalCoefficientDGEnrichedHom W X).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((originalCoefficientDGEnrichedHom X Z).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f (q + r)) ≫
        originalDGCompositionComponent Z.unop X.unop W.unop (by
          change (-(p : ℤ)) + (-((q + r : ℕ) : ℤ)) = -(n : ℤ)
          omega) := by
    have hi := ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp W X Z)
      (show p + (q + r) = n by omega)
    have hi' := congrArg (fun t ↦ t ≫
      ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n) hi
    have hr := originalTruncatedCompositionComponent_to_raw W X Z
      (show p + (q + r) = n by omega)
    simpa only [Category.assoc] using hi'.trans hr
  have hL₁Raw := congrArg
    (fun t ↦
      (α_ ((originalCoefficientDGChainEnrichedHom W X).X p)
          ((originalCoefficientDGChainEnrichedHom X Y).X q)
          ((originalCoefficientDGChainEnrichedHom Y Z).X r)).inv ≫
        t ≫
        GradedObject.Monoidal.ιTensorObj
          (originalCoefficientDGChainEnrichedHom W Y).X
          (originalCoefficientDGChainEnrichedHom Y Z).X (p + q) r n h ≫
        (originalCoefficientDGChainEnrichedComp W Y Z).f n ≫
        ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n)
    hcompL
  have hL₂Raw := congrArg
    (fun t ↦
      (α_ ((originalCoefficientDGChainEnrichedHom W X).X p)
          ((originalCoefficientDGChainEnrichedHom X Y).X q)
          ((originalCoefficientDGChainEnrichedHom Y Z).X r)).inv ≫
        (quotientTruncatedMapComponent
          (originalCoefficientDGEnrichedComp W X Y) rfl ▷
            (originalCoefficientDGChainEnrichedHom Y Z).X r) ≫ t)
    houterCompL
  have hR₁Raw := congrArg
    (fun t ↦
      t ≫
        GradedObject.Monoidal.ιTensorObj
          (originalCoefficientDGChainEnrichedHom W X).X
          (originalCoefficientDGChainEnrichedHom X Z).X p (q + r) n (by omega) ≫
        (originalCoefficientDGChainEnrichedComp W X Z).f n ≫
        ((originalCoefficientDGEnrichedHom W Z).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n)
    hcompR
  have hR₂Raw := congrArg
    (fun t ↦
      ((originalCoefficientDGChainEnrichedHom W X).X p ◁
          quotientTruncatedMapComponent
            (originalCoefficientDGEnrichedComp X Y Z) rfl) ≫ t)
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
  have hraw := originalDGCompositionComponent_assoc_natNeg
    W.unop X.unop Y.unop Z.unop h
  have htransport := quotientDGChain_assoc_transport
    (V := ModuleCat.{1} QuotientCoefficientRing)
    (A₀ := (originalCoefficientDGChainEnrichedHom W X).X p)
    (B₀ := (originalCoefficientDGChainEnrichedHom X Y).X q)
    (C₀ := (originalCoefficientDGChainEnrichedHom Y Z).X r)
    (A := (originalCoefficientDGEnrichedHom W X).X (-(p : ℤ)))
    (B := (originalCoefficientDGEnrichedHom X Y).X (-(q : ℤ)))
    (C' := (originalCoefficientDGEnrichedHom Y Z).X (-(r : ℤ)))
    (AB₀ := (originalCoefficientDGChainEnrichedHom W Y).X (p + q))
    (BC₀ := (originalCoefficientDGChainEnrichedHom X Z).X (q + r))
    (AB := (originalCoefficientDGEnrichedHom W Y).X (-((p + q : ℕ) : ℤ)))
    (BC := (originalCoefficientDGEnrichedHom X Z).X (-((q + r : ℕ) : ℤ)))
    (D := (originalCoefficientDGEnrichedHom W Z).X (-(n : ℤ)))
    (((originalCoefficientDGEnrichedHom W X).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f p)
    (((originalCoefficientDGEnrichedHom X Y).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f q)
    (((originalCoefficientDGEnrichedHom Y Z).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f r)
    (quotientTruncatedMapComponent (originalCoefficientDGEnrichedComp W X Y) rfl)
    (((originalCoefficientDGEnrichedHom W Y).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f (p + q))
    (originalDGCompositionComponent Y.unop X.unop W.unop (by omega))
    (quotientTruncatedMapComponent (originalCoefficientDGEnrichedComp X Y Z) rfl)
    (((originalCoefficientDGEnrichedHom X Z).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f (q + r))
    (originalDGCompositionComponent Z.unop Y.unop X.unop (by omega))
    (originalDGCompositionComponent Z.unop Y.unop W.unop (by omega))
    (originalDGCompositionComponent Z.unop X.unop W.unop (by omega))
    (originalTruncatedCompositionComponent_to_raw W X Y rfl)
    (originalTruncatedCompositionComponent_to_raw X Y Z rfl)
    hraw
  simpa only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] using htransport

/-- The smart-truncated coefficient-changed original category. -/
@[implicit_reducible]
noncomputable instance originalCoefficientDGChainEnrichedCategory :
    EnrichedCategory QuotientDGChain OriginalCoefficientDGCategory where
  Hom := originalCoefficientDGChainEnrichedHom
  id := originalCoefficientDGChainEnrichedId
  comp := originalCoefficientDGChainEnrichedComp
  id_comp := originalCoefficientDGChainEnrichedId_comp
  comp_id := originalCoefficientDGChainEnriched_comp_id
  assoc := originalCoefficientDGChainEnrichedComp_assoc

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
