/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitneyAssociativityNaturality

/-!
# Left normalized Alexander--Whitney associativity expansion

This file expands the left side of normalized Alexander--Whitney associativity into the
unnormalized coassociativity composite followed by normalized Moore retractions.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory

theorem normalizedAlexanderWhitney_eq
    (X Y : SimplicialObject (ModuleCat.{0} ℤ)) :
    normalizedAlexanderWhitney X Y =
      inclusionOfMooreComplexMap (X ⊗ Y) ≫
        alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) := rfl

theorem normalizedAlexanderWhitney_associativity_left_expansion
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    normalizedAlexanderWhitney (X ⊗ Y) Z ≫
          (normalizedAlexanderWhitney X Y ▷
            normalizedChainsForAssociativity Z) ≫
          (α_ (normalizedChainsForAssociativity X)
            (normalizedChainsForAssociativity Y)
            (normalizedChainsForAssociativity Z)).hom =
      inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        alternatingAlexanderWhitney (X ⊗ Y) Z ≫
        (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
        (α_ (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z)).hom ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
          (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
  calc
    _ = (inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
          alternatingAlexanderWhitney (X ⊗ Y) Z ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y))
            (DoldKan.PInftyToNormalizedMooreComplex Z)) ≫
        (normalizedAlexanderWhitney X Y ▷
          normalizedChainsForAssociativity Z) ≫
        (α_ (normalizedChainsForAssociativity X)
          (normalizedChainsForAssociativity Y)
          (normalizedChainsForAssociativity Z)).hom := by
      rw [normalizedAlexanderWhitney_eq (X ⊗ Y) Z]
      rfl
    _ = inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        alternatingAlexanderWhitney (X ⊗ Y) Z ≫
        (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y))
            (DoldKan.PInftyToNormalizedMooreComplex Z) ≫
          (normalizedAlexanderWhitney X Y ▷
            normalizedChainsForAssociativity Z)) ≫
        (α_ (normalizedChainsForAssociativity X)
          (normalizedChainsForAssociativity Y)
          (normalizedChainsForAssociativity Z)).hom := by
      simp only [Category.assoc]
    _ = inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        alternatingAlexanderWhitney (X ⊗ Y) Z ≫
        ((alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
          HomologicalComplex.tensorHom
            (HomologicalComplex.tensorHom
              (DoldKan.PInftyToNormalizedMooreComplex X)
              (DoldKan.PInftyToNormalizedMooreComplex Y))
            (DoldKan.PInftyToNormalizedMooreComplex Z)) ≫
        (α_ (normalizedChainsForAssociativity X)
          (normalizedChainsForAssociativity Y)
          (normalizedChainsForAssociativity Z)).hom := by
      erw [normalizedAlexanderWhitney_inner_left X Y Z]
      rfl
    _ = _ := by
      simp only [Category.assoc]
      erw [alternatingAlexanderWhitney_whisker_associator_retractions X Y Z]
      rfl

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
