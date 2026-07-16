/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGLaws
import Mathlib.CategoryTheory.Enriched.Basic

/-! # The corrected Drinfeld quotient as a DG-enriched category -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- A distinct carrier synonym for the opposite of the bounded-complex category. -/
def CorrectedQuotientDGCategory := ComplexCategoryᵒᵖ

/-- The quotient cochain complex in the orientation required by the opposite carrier. -/
def quotientDGEnrichedHom
    (K L : CorrectedQuotientDGCategory) : QuotientDGCochain :=
  quotientCoefficientCochainComplex L.unop K.unop

/-- The quotient identity in the orientation required by the opposite carrier. -/
def quotientDGEnrichedId (K : CorrectedQuotientDGCategory) :
    𝟙_ QuotientDGCochain ⟶ quotientDGEnrichedHom K K :=
  quotientDGIdentity K.unop

/-- Quotient composition in the orientation required by the opposite carrier. -/
def quotientDGEnrichedComp (K L M : CorrectedQuotientDGCategory) :
    quotientDGEnrichedHom K L ⊗ quotientDGEnrichedHom L M ⟶
      quotientDGEnrichedHom K M :=
  quotientDGComposition M.unop L.unop K.unop

/-- The corrected Drinfeld quotient packaged as a category enriched in cochain complexes. -/
@[implicit_reducible]
noncomputable instance correctedQuotientDGEnrichedCategory :
    EnrichedCategory QuotientDGCochain CorrectedQuotientDGCategory where
  Hom := quotientDGEnrichedHom
  id := quotientDGEnrichedId
  comp := quotientDGEnrichedComp
  id_comp K L := quotientDGIdentity_comp K.unop L.unop
  comp_id K L := quotientDG_comp_identity K.unop L.unop
  assoc W X Y Z := quotientDGComposition_assoc W.unop X.unop Y.unop Z.unop

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
