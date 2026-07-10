import LeanLCAExactChallenge.Infinity.AlexanderWhitneyAssociativityLeft

/-!
# Right normalized Alexander--Whitney associativity expansion

This file expands the right side of normalized Alexander--Whitney associativity into the
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

theorem normalizedMoore_associator_inclusion_naturality
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        inclusionOfMooreComplexMap (X ⊗ (Y ⊗ Z)) =
      inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        (alternatingFaceMapComplex (ModuleCat ℤ)).map (α_ X Y Z).hom :=
  (inclusionOfMooreComplex (ModuleCat ℤ)).naturality (α_ X Y Z).hom

theorem normalizedAlexanderWhitney_associativity_right_expansion
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
          normalizedAlexanderWhitney X (Y ⊗ Z) ≫
          (normalizedChainsForAssociativity X ◁
            normalizedAlexanderWhitney Y Z) =
      inclusionOfMooreComplexMap ((X ⊗ Y) ⊗ Z) ≫
        (alternatingFaceMapComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
            (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
  calc
    _ = (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        (inclusionOfMooreComplexMap (X ⊗ (Y ⊗ Z)) ≫
          alternatingAlexanderWhitney X (Y ⊗ Z) ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex (Y ⊗ Z))) ≫
        (normalizedChainsForAssociativity X ◁
          normalizedAlexanderWhitney Y Z) := by
      rw [normalizedAlexanderWhitney_eq X (Y ⊗ Z)]
      rfl
    _ = (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        inclusionOfMooreComplexMap (X ⊗ (Y ⊗ Z)) ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex (Y ⊗ Z)) ≫
          (normalizedChainsForAssociativity X ◁
            normalizedAlexanderWhitney Y Z)) := by
      simp only [Category.assoc]
    _ = (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        inclusionOfMooreComplexMap (X ⊗ (Y ⊗ Z)) ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        ((alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (HomologicalComplex.tensorHom
              (DoldKan.PInftyToNormalizedMooreComplex Y)
              (DoldKan.PInftyToNormalizedMooreComplex Z))) := by
      erw [normalizedAlexanderWhitney_inner_right X Y Z]
      rfl
    _ = (normalizedMooreComplex (ModuleCat ℤ)).map (α_ X Y Z).hom ≫
        inclusionOfMooreComplexMap (X ⊗ (Y ⊗ Z)) ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
            (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
      rfl
    _ = _ := by
      rw [← Category.assoc]
      erw [normalizedMoore_associator_inclusion_naturality X Y Z]
      rw [Category.assoc]

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
