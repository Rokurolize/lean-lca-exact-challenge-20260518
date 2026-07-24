/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientOriginalChainAssociativity

/-! # The zero-word functor after smart truncation -/

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

/-- The zero-word inclusion after applying nonpositive smart truncation. -/
def originalCoefficientDGChainHomToQuotient
    (K L : OriginalCoefficientDGCategory) :
    originalCoefficientDGChainEnrichedHom K L ⟶
      quotientDGChainEnrichedHom (Opposite.op K.unop) (Opposite.op L.unop) :=
  HomologicalComplex.truncLE'Map
    (OriginalCoefficientHomToQuotient L.unop K.unop)
    ComplexShape.embeddingDownNat

@[simp]
theorem originalCoefficientDGChainHomToQuotient_f
    (K L : OriginalCoefficientDGCategory) (n : ℕ) :
    (originalCoefficientDGChainHomToQuotient K L).f n =
      (HomologicalComplex.truncLE'Map
        (OriginalCoefficientHomToQuotient L.unop K.unop)
        ComplexShape.embeddingDownNat).f n :=
  rfl

lemma originalCoefficientDGChainHomToQuotient_toRestriction
    (K L : OriginalCoefficientDGCategory) (n : ℕ) :
    (originalCoefficientDGChainHomToQuotient K L).f n ≫
        ((quotientDGEnrichedHom (Opposite.op K.unop) (Opposite.op L.unop)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      ((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n ≫
        (HomologicalComplex.restrictionMap
          (OriginalCoefficientHomToQuotient L.unop K.unop)
          ComplexShape.embeddingDownNat).f n := by
  change ComplexCategoryᵒᵖ at K L
  change (HomologicalComplex.truncLE'Map
        (OriginalCoefficientHomToQuotient L.unop K.unop)
        ComplexShape.embeddingDownNat).f n ≫
      ((quotientCoefficientCochainComplex L.unop K.unop).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f n =
    ((OriginalCoefficientCochainComplex L.unop K.unop).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n ≫
      (HomologicalComplex.restrictionMap
        (OriginalCoefficientHomToQuotient L.unop K.unop)
        ComplexShape.embeddingDownNat).f n
  have hnat := congrArg (fun t ↦ t.f n)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      (OriginalCoefficientHomToQuotient L.unop K.unop)
      ComplexShape.embeddingDownNat)
  simpa only [HomologicalComplex.comp_f] using hnat

@[simp]
lemma restrictionMap_OriginalCoefficientHomToQuotient_f_raw
    (K L : ComplexCategory) (n : ℕ) :
    (HomologicalComplex.restrictionMap
      (OriginalCoefficientHomToQuotient K L)
      ComplexShape.embeddingDownNat).f n =
      (OriginalCoefficientHomToQuotient K L).f (-(n : ℤ)) :=
  rfl

@[simp]
lemma restrictionMap_OriginalCoefficientHomToQuotient_f
    (K L : OriginalCoefficientDGCategory) (n : ℕ) :
    (HomologicalComplex.restrictionMap
      (OriginalCoefficientHomToQuotient L.unop K.unop)
      ComplexShape.embeddingDownNat).f n =
      (OriginalCoefficientHomToQuotient L.unop K.unop).f (-(n : ℤ)) :=
  rfl

lemma originalCoefficientDGChainHomToQuotient_tensor_toRestriction
    (K L M : OriginalCoefficientDGCategory) (p q : ℕ) :
    ((originalCoefficientDGChainHomToQuotient K L).f p ⊗ₘ
        (originalCoefficientDGChainHomToQuotient L M).f q) ≫
      (((quotientDGEnrichedHom (Opposite.op K.unop) (Opposite.op L.unop)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((quotientDGEnrichedHom (Opposite.op L.unop) (Opposite.op M.unop)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) =
    (((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((originalCoefficientDGEnrichedHom L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) ≫
      ((OriginalCoefficientHomToQuotient L.unop K.unop).f (-(p : ℤ)) ⊗ₘ
        (OriginalCoefficientHomToQuotient M.unop L.unop).f (-(q : ℤ))) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    originalCoefficientDGChainHomToQuotient_toRestriction,
    originalCoefficientDGChainHomToQuotient_toRestriction,
    restrictionMap_OriginalCoefficientHomToQuotient_f,
    restrictionMap_OriginalCoefficientHomToQuotient_f]
  exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

lemma OriginalCoefficientDGIdentitySpan_map (K : ComplexCategory) :
    OriginalCoefficientDGIdentitySpan K ≫
        (OriginalCoefficientHomToQuotient K K).f 0 =
      quotientIdentitySpan K := by
  apply ModuleCat.hom_ext
  change (quotientLinearMapChangeScalars
        (originalHomInclusion K K 0).hom).comp
      (LinearMap.toSpanSingleton QuotientCoefficientRing _
        (ULift.up (ULift.up (identityCochain K)))) =
    LinearMap.toSpanSingleton QuotientCoefficientRing _
      (ULift.up (quotientIdentityElement K))
  rw [LinearMap.comp_toSpanSingleton]
  rfl

/-- The smart-truncated zero-word inclusion preserves the identity. -/
theorem originalCoefficientDGChainIdentity_map
    (K : OriginalCoefficientDGCategory) :
    originalCoefficientDGChainEnrichedId K ≫
        originalCoefficientDGChainHomToQuotient K K =
      quotientDGChainEnrichedId (Opposite.op K.unop) := by
  change ComplexCategoryᵒᵖ at K
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  rw [originalCoefficientDGChainEnrichedId_f_zero,
    quotientDGChainEnrichedId_f_zero]
  apply (cancel_mono
    (((quotientDGEnrichedHom (Opposite.op K.unop) (Opposite.op K.unop)).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0)).1
  simp only [Category.assoc]
  have hnat := congrArg (fun t ↦ t.f 0)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      (OriginalCoefficientHomToQuotient K.unop K.unop)
      ComplexShape.embeddingDownNat)
  simp only [HomologicalComplex.comp_f] at hnat
  change (originalCoefficientDGChainHomToQuotient K K).f 0 ≫
      ((quotientDGEnrichedHom (Opposite.op K.unop) (Opposite.op K.unop)).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0 =
    ((originalCoefficientDGEnrichedHom K K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0 ≫
      (OriginalCoefficientHomToQuotient K.unop K.unop).f 0 at hnat
  slice_lhs 2 3 => rw [hnat]
  slice_lhs 1 2 =>
    rw [originalCoefficientDGChainIdentityDegreeZero_toRestriction]
  rw [quotientDGChainIdentityDegreeZero_toRestriction]
  exact OriginalCoefficientDGIdentitySpan_map K.unop

/-- The smart-truncated zero-word inclusion preserves composition. -/
theorem originalCoefficientDGChainComposition_map
    (K L M : OriginalCoefficientDGCategory) :
    originalCoefficientDGChainEnrichedComp K L M ≫
        originalCoefficientDGChainHomToQuotient K M =
      (originalCoefficientDGChainHomToQuotient K L ⊗ₘ
          originalCoefficientDGChainHomToQuotient L M) ≫
        quotientDGChainEnrichedComp
          (Opposite.op K.unop) (Opposite.op L.unop) (Opposite.op M.unop) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono
    (((quotientDGEnrichedHom (Opposite.op K.unop) (Opposite.op M.unop)).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f n)).1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  simp only [HomologicalComplex.comp_f, Category.assoc]
  dsimp only [originalCoefficientDGChainEnrichedComp,
    quotientDGChainEnrichedComp]
  slice_lhs 1 2 =>
    change HomologicalComplex.ιTensorObj
      (originalCoefficientDGChainEnrichedHom K L)
      (originalCoefficientDGChainEnrichedHom L M) p q n hpq ≫
        quotientTruncatedMapDegree (originalCoefficientDGEnrichedComp K L M) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp K L M) hpq
  slice_lhs 2 3 =>
    rw [originalCoefficientDGChainHomToQuotient_toRestriction]
  slice_lhs 1 2 =>
    rw [originalTruncatedCompositionComponent_to_raw]
  change ((((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
        ((originalCoefficientDGEnrichedHom L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) ≫
      originalDGCompositionComponent M.unop L.unop K.unop (by
        change (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)
        omega)) ≫
      (OriginalCoefficientHomToQuotient M.unop K.unop).f (-(n : ℤ)) = _
  slice_lhs 2 3 =>
    rw [originalDGCompositionComponent_map M.unop L.unop K.unop]
  slice_rhs 1 2 =>
    change HomologicalComplex.ιTensorObj
      (originalCoefficientDGChainEnrichedHom K L)
      (originalCoefficientDGChainEnrichedHom L M) p q n hpq ≫
        (HomologicalComplex.tensorHom
          (originalCoefficientDGChainHomToQuotient K L)
          (originalCoefficientDGChainHomToQuotient L M)).f n
    exact originalChain_ιTensorObj_tensorHom
      (originalCoefficientDGChainHomToQuotient K L)
      (originalCoefficientDGChainHomToQuotient L M) hpq
  slice_rhs 2 3 =>
    change HomologicalComplex.ιTensorObj
      (quotientDGChainEnrichedHom (Opposite.op K.unop) (Opposite.op L.unop))
      (quotientDGChainEnrichedHom (Opposite.op L.unop) (Opposite.op M.unop))
      p q n hpq ≫
        quotientTruncatedMapDegree
          (quotientDGEnrichedComp
            (Opposite.op K.unop) (Opposite.op L.unop) (Opposite.op M.unop)) n
    exact ιTensorObj_quotientTruncatedMapDegree
      (quotientDGEnrichedComp
        (Opposite.op K.unop) (Opposite.op L.unop) (Opposite.op M.unop)) hpq
  slice_rhs 2 3 =>
    rw [quotientTruncatedCompositionComponent_to_raw]
  slice_rhs 1 2 =>
    rw [originalCoefficientDGChainHomToQuotient_tensor_toRestriction]
  let a := (((originalCoefficientDGEnrichedHom K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f p ⊗ₘ
    ((originalCoefficientDGEnrichedHom L M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f q)
  let b := ((OriginalCoefficientHomToQuotient L.unop K.unop).f (-(p : ℤ)) ⊗ₘ
    (OriginalCoefficientHomToQuotient M.unop L.unop).f (-(q : ℤ)))
  let c := quotientDGCompositionComponent M.unop L.unop K.unop
    (p := -(p : ℤ)) (q := -(q : ℤ)) (n := -(n : ℤ)) (by omega)
  change a ≫ (b ≫ c) = (a ≫ b) ≫ c
  exact (Category.assoc a b c).symm

/-- The canonical chain-enriched functor from the coefficient-changed original category to the
smart-truncated corrected quotient. -/
noncomputable def originalToCorrectedQuotientDGChain :
    EnrichedFunctor QuotientDGChain
      OriginalCoefficientDGCategory CorrectedQuotientDGCategory where
  obj K := Opposite.op K.unop
  map K L := originalCoefficientDGChainHomToQuotient K L
  map_id K := originalCoefficientDGChainIdentity_map K
  map_comp K L M := originalCoefficientDGChainComposition_map K L M

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
