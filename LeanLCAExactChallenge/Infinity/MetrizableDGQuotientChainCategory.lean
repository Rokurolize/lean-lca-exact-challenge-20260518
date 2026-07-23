/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientTruncation

/-!
# The corrected quotient enriched in nonnegative chain complexes

This file constructs the smart-truncated Hom objects, composition, and identity chain maps.
-/

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

/-- The corrected quotient Hom object after nonpositive smart truncation. -/
def quotientDGChainEnrichedHom
    (K L : CorrectedQuotientDGCategory) : QuotientDGChain :=
  (quotientDGEnrichedHom K L).truncLE' ComplexShape.embeddingDownNat

/-- Corrected quotient composition after nonpositive smart truncation. -/
def quotientDGChainEnrichedComp
    (K L M : CorrectedQuotientDGCategory) :
    quotientDGChainEnrichedHom K L ⊗ quotientDGChainEnrichedHom L M ⟶
      quotientDGChainEnrichedHom K M :=
  quotientTruncatedMap (quotientDGEnrichedComp K L M)

lemma quotientIdentitySpan_d (K : ComplexCategory) :
    quotientIdentitySpan K ≫
      (quotientCoefficientCochainComplex K K).d 0 1 = 0 := by
  erw [quotientCoefficientCochainComplex_d_succ K K 0]
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
    _ = 0 := by rw [quotientIdentityElement_closed, zsmul_zero]

/-- The quotient identity cocycle in smart-truncation degree zero. -/
def quotientDGChainIdentityDegreeZero (K : CorrectedQuotientDGCategory) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (quotientDGChainEnrichedHom K K).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  exact
    (quotientDGEnrichedHom K K).liftCycles'
        (quotientIdentitySpan K.unop) 1 rfl
        (quotientIdentitySpan_d K.unop) ≫
      ((quotientDGEnrichedHom K K).truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv

lemma quotientDGChainIdentityDegreeZero_toRestriction
    (K : CorrectedQuotientDGCategory) :
    quotientDGChainIdentityDegreeZero K ≫
        ((quotientDGEnrichedHom K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      quotientIdentitySpan K.unop := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [quotientTruncLEToRestriction_f_zero _ hb]
  dsimp [quotientDGChainIdentityDegreeZero]
  simp only [Category.assoc]
  erw [quotientTruncLEIsoCycles_inv_hom_of_proofs_assoc
    (quotientDGEnrichedHom K K) 0 0 rfl rfl hb hb]
  simp

/-- The identity chain map for the smart-truncated corrected quotient. -/
def quotientDGChainEnrichedId (K : CorrectedQuotientDGCategory) :
    𝟙_ QuotientDGChain ⟶ quotientDGChainEnrichedHom K K :=
  (ChainComplex.fromSingle₀Equiv
    (quotientDGChainEnrichedHom K K)
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).symm
      (quotientDGChainIdentityDegreeZero K)

@[simp]
lemma quotientDGChainEnrichedId_f_zero (K : CorrectedQuotientDGCategory) :
    (quotientDGChainEnrichedId K).f 0 =
      quotientDGChainIdentityDegreeZero K := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (quotientDGChainIdentityDegreeZero K)

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
