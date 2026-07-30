/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionPreservation

/-! # Enriched extension from the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- Word evaluation packages an annihilating enriched functor as an enriched functor out of the
corrected Drinfeld quotient. -/
def enrichedExtension :
    EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D where
  obj K := E.functor.obj K
  map K L := E.evaluateCochainMap L.unop K.unop
  map_id K := E.evaluateCochainMap_id K.unop
  map_comp K L M := E.evaluateCochainMap_comp M.unop L.unop K.unop

@[simp]
theorem enrichedExtension_obj (K : CorrectedQuotientDGCategory) :
    E.enrichedExtension.obj K = E.functor.obj K :=
  rfl

@[simp]
theorem enrichedExtension_map (K L : CorrectedQuotientDGCategory) :
    E.enrichedExtension.map K L = E.evaluateCochainMap L.unop K.unop :=
  rfl

/-- Restricting the enriched extension to zero-word morphisms recovers the supplied original
enriched functor on every Hom complex. -/
theorem enrichedExtension_restricts
    (K L : OriginalCoefficientDGCategory) :
    OriginalCoefficientHomToQuotient L.unop K.unop ≫
        E.enrichedExtension.map K L =
      E.functor.map K L := by
  exact E.evaluateCochainMap_original L.unop K.unop

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
