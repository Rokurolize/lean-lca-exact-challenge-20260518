/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitneyAssociativityRight
import LeanLCAExactChallenge.Infinity.AlexanderWhitneyCoassociativity
import LeanLCAExactChallenge.Infinity.AlexanderWhitneyUnits

/-!
# Normalized Alexander--Whitney associativity

This file transports unnormalized Alexander--Whitney coassociativity through the normalized
Moore retractions. Together with the unit laws, it packages the normalized Moore functor as
an oplax monoidal functor.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory

theorem alternatingAlexanderWhitney_coassociativity_whiskered
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    alternatingAlexanderWhitney (X ⊗ Y) Z ≫
          (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
          (α_ (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z)).hom =
      (alternatingFaceMapComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) := by
  rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom]
  exact alternatingAlexanderWhitney_coassociativity X Y Z

theorem alternatingAlexanderWhitney_coassociativity_with_retractions
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
          alternatingAlexanderWhitney (X ⊗ Y) Z ≫
          (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
          (α_ (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z)).hom ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (HomologicalComplex.tensorHom
              (DoldKan.PInftyToNormalizedMooreComplex Y)
              (DoldKan.PInftyToNormalizedMooreComplex Z)) =
      inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        (alternatingFaceMapComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
            (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
  have h := congrArg
    (fun t => inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫ t ≫
      HomologicalComplex.tensorHom
        (DoldKan.PInftyToNormalizedMooreComplex X)
        (HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex Y)
          (DoldKan.PInftyToNormalizedMooreComplex Z)))
    (alternatingAlexanderWhitney_coassociativity_whiskered X Y Z)
  simpa only [Category.assoc] using h

theorem normalizedAlexanderWhitney_associativity
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    normalizedAlexanderWhitney (X ⊗ Y) Z ≫
          (normalizedAlexanderWhitney X Y ▷
            normalizedChainsForAssociativity Z) ≫
          (α_ (normalizedChainsForAssociativity X)
            (normalizedChainsForAssociativity Y)
            (normalizedChainsForAssociativity Z)).hom =
      (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        normalizedAlexanderWhitney X (Y ⊗ Z) ≫
        (normalizedChainsForAssociativity X ◁
          normalizedAlexanderWhitney Y Z) := by
  exact (normalizedAlexanderWhitney_associativity_left_expansion X Y Z).trans
    ((alternatingAlexanderWhitney_coassociativity_with_retractions X Y Z).trans
      (normalizedAlexanderWhitney_associativity_right_expansion X Y Z).symm)

@[implicit_reducible]
def normalizedMooreOplaxMonoidal : NormalizedMooreOplaxMonoidal :=
  normalizedMooreOplaxMonoidalCandidate
    normalizedAlexanderWhitney_associativity
    normalizedAlexanderWhitney_left_unitality
    normalizedAlexanderWhitney_right_unitality

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
