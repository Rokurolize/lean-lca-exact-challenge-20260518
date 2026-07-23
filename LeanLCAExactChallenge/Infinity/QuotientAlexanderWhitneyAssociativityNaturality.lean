/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyAssociativityCore

/-!
# Alexander--Whitney associator naturality

This file records the associator naturality identity needed to transport the normalized Moore
retractions through an iterated Alexander--Whitney map.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory

theorem alternatingAlexanderWhitney_whisker_associator_retractions
    (X Y Z : SimplicialObject (QuotientModule)) :
    (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
          HomologicalComplex.tensorHom
            (HomologicalComplex.tensorHom
              (DoldKan.PInftyToNormalizedMooreComplex X)
              (DoldKan.PInftyToNormalizedMooreComplex Y))
            (DoldKan.PInftyToNormalizedMooreComplex Z) ≫
          (α_ (normalizedChainsForAssociativity X)
            (normalizedChainsForAssociativity Y)
            (normalizedChainsForAssociativity Z)).hom =
      (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
        (α_ (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z)).hom ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
            (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
  slice_lhs 2 3 =>
    erw [MonoidalCategory.associator_naturality
      (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.PInftyToNormalizedMooreComplex Y)
      (DoldKan.PInftyToNormalizedMooreComplex Z)]
  rfl

end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
