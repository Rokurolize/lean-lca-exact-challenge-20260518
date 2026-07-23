/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainAssociativity
import Mathlib.CategoryTheory.Enriched.Basic

/-! # The corrected quotient enriched in nonnegative chain complexes -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

/-- The smart-truncated corrected quotient as a category enriched in nonnegative chain complexes. -/
@[implicit_reducible]
noncomputable instance correctedQuotientDGChainEnrichedCategory :
    EnrichedCategory QuotientDGChain CorrectedQuotientDGCategory where
  Hom := quotientDGChainEnrichedHom
  id := quotientDGChainEnrichedId
  comp := quotientDGChainEnrichedComp
  id_comp := quotientDGChainEnrichedId_comp
  comp_id := quotientDGChainEnriched_comp_id
  assoc := quotientDGChainEnrichedComp_assoc

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
