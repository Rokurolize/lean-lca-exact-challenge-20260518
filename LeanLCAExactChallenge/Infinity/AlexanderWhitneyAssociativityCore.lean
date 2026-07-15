/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.AlexanderWhitneyProjectors

/-!
# Normalized Alexander--Whitney associativity core

This file relates normalized Alexander--Whitney maps to the corresponding unnormalized maps
followed by the normalized Moore retractions. These identities are the algebraic core of the
normalized associativity proof.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory

abbrev normalizedChainsForAssociativity
    (X : SimplicialObject (ModuleCat.{0} ℤ)) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (normalizedMooreComplex (ModuleCat ℤ)).obj X

theorem pInftyToNormalized_comp_normalizedAlexanderWhitney
    (X Y : SimplicialObject (ModuleCat.{0} ℤ)) :
    DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y) ≫
        normalizedAlexanderWhitney X Y =
      alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex Y) := by
  let pXY := DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y)
  let tail := HomologicalComplex.tensorHom
    (DoldKan.PInftyToNormalizedMooreComplex X)
    (DoldKan.PInftyToNormalizedMooreComplex Y)
  have hdef :
      pXY ≫ normalizedAlexanderWhitney X Y =
        (pXY ≫ inclusionOfMooreComplexMap (X ⊗ Y)) ≫
          alternatingAlexanderWhitney X Y ≫ tail := by
    dsimp only [pXY, tail, normalizedAlexanderWhitney]
    rfl
  have hinc :
      (pXY ≫ inclusionOfMooreComplexMap (X ⊗ Y)) ≫
          alternatingAlexanderWhitney X Y ≫ tail =
        (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
            alternatingChains (X ⊗ Y)) ≫
          alternatingAlexanderWhitney X Y ≫ tail := by
    rw [show pXY ≫ inclusionOfMooreComplexMap (X ⊗ Y) =
      (DoldKan.PInfty : alternatingChains (X ⊗ Y) ⟶
        alternatingChains (X ⊗ Y)) by
      simpa only [pXY] using
        DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap
          (X ⊗ Y)]
    rfl
  exact hdef.trans (hinc.trans
    (pInfty_comp_compressedAlexanderWhitneyToNormalized X Y))

theorem normalizedAlexanderWhitney_inner_left
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y))
          (DoldKan.PInftyToNormalizedMooreComplex Z) ≫
        (normalizedAlexanderWhitney X Y ▷
          normalizedChainsForAssociativity Z) =
      (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
        HomologicalComplex.tensorHom
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex Y))
          (DoldKan.PInftyToNormalizedMooreComplex Z) := by
  let pX := DoldKan.PInftyToNormalizedMooreComplex X
  let pY := DoldKan.PInftyToNormalizedMooreComplex Y
  let pZ := DoldKan.PInftyToNormalizedMooreComplex Z
  let pXY := DoldKan.PInftyToNormalizedMooreComplex (X ⊗ Y)
  have hcore :
      HomologicalComplex.tensorHom pXY pZ ≫
          (normalizedAlexanderWhitney X Y ▷
            normalizedChainsForAssociativity Z) =
        HomologicalComplex.tensorHom
          (alternatingAlexanderWhitney X Y ≫
            HomologicalComplex.tensorHom pX pY) pZ := by
    calc
      HomologicalComplex.tensorHom pXY pZ ≫
          (normalizedAlexanderWhitney X Y ▷
            normalizedChainsForAssociativity Z) =
        HomologicalComplex.tensorHom pXY pZ ≫
          HomologicalComplex.tensorHom
            (normalizedAlexanderWhitney X Y)
            (𝟙 (normalizedChainsForAssociativity Z)) := by
        exact congrArg (fun t => HomologicalComplex.tensorHom pXY pZ ≫ t)
          (MonoidalCategory.tensorHom_id
            (normalizedAlexanderWhitney X Y)
            (normalizedChainsForAssociativity Z)).symm
      _ = HomologicalComplex.tensorHom
          (pXY ≫ normalizedAlexanderWhitney X Y)
          (pZ ≫ 𝟙 (normalizedChainsForAssociativity Z)) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = HomologicalComplex.tensorHom
          (alternatingAlexanderWhitney X Y ≫
            HomologicalComplex.tensorHom pX pY) pZ := by
        rw [pInftyToNormalized_comp_normalizedAlexanderWhitney X Y]
        exact congrArg
          (fun t => HomologicalComplex.tensorHom
            (alternatingAlexanderWhitney X Y ≫
              HomologicalComplex.tensorHom pX pY) t)
          (Category.comp_id pZ)
  have hsplit :
      HomologicalComplex.tensorHom
          (alternatingAlexanderWhitney X Y ≫
            HomologicalComplex.tensorHom pX pY) pZ =
        HomologicalComplex.tensorHom
            (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z)) ≫
          HomologicalComplex.tensorHom
            (HomologicalComplex.tensorHom pX pY) pZ := by
    calc
      HomologicalComplex.tensorHom
          (alternatingAlexanderWhitney X Y ≫
            HomologicalComplex.tensorHom pX pY) pZ =
        HomologicalComplex.tensorHom
          (alternatingAlexanderWhitney X Y ≫
            HomologicalComplex.tensorHom pX pY)
          ((𝟙 (alternatingChains Z)) ≫ pZ) := by
            exact congrArg
              (fun t => HomologicalComplex.tensorHom
                (alternatingAlexanderWhitney X Y ≫
                  HomologicalComplex.tensorHom pX pY) t)
              (Category.id_comp pZ).symm
      _ = _ := (MonoidalCategory.tensorHom_comp_tensorHom
        (alternatingAlexanderWhitney X Y) (𝟙 (alternatingChains Z))
        (HomologicalComplex.tensorHom pX pY) pZ).symm
  have hlast :
      HomologicalComplex.tensorHom
            (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z)) ≫
          HomologicalComplex.tensorHom
            (HomologicalComplex.tensorHom pX pY) pZ =
        (alternatingAlexanderWhitney X Y ▷ alternatingChains Z) ≫
          HomologicalComplex.tensorHom
            (HomologicalComplex.tensorHom pX pY) pZ := by
    exact congrArg
      (fun t => t ≫ HomologicalComplex.tensorHom
        (HomologicalComplex.tensorHom pX pY) pZ)
      (MonoidalCategory.tensorHom_id
        (alternatingAlexanderWhitney X Y) (alternatingChains Z))
  exact hcore.trans (hsplit.trans hlast)

theorem normalizedAlexanderWhitney_inner_right
    (X Y Z : SimplicialObject (ModuleCat.{0} ℤ)) :
    HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (DoldKan.PInftyToNormalizedMooreComplex (Y ⊗ Z)) ≫
        (normalizedChainsForAssociativity X ◁
          normalizedAlexanderWhitney Y Z) =
      (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X)
          (HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex Y)
            (DoldKan.PInftyToNormalizedMooreComplex Z)) := by
  let pX := DoldKan.PInftyToNormalizedMooreComplex X
  let pY := DoldKan.PInftyToNormalizedMooreComplex Y
  let pZ := DoldKan.PInftyToNormalizedMooreComplex Z
  let pYZ := DoldKan.PInftyToNormalizedMooreComplex (Y ⊗ Z)
  have hcore :
      HomologicalComplex.tensorHom pX pYZ ≫
          (normalizedChainsForAssociativity X ◁
            normalizedAlexanderWhitney Y Z) =
        HomologicalComplex.tensorHom pX
          (alternatingAlexanderWhitney Y Z ≫
            HomologicalComplex.tensorHom pY pZ) := by
    calc
      HomologicalComplex.tensorHom pX pYZ ≫
          (normalizedChainsForAssociativity X ◁
            normalizedAlexanderWhitney Y Z) =
        HomologicalComplex.tensorHom pX pYZ ≫
          HomologicalComplex.tensorHom
            (𝟙 (normalizedChainsForAssociativity X))
            (normalizedAlexanderWhitney Y Z) := by
        exact congrArg (fun t => HomologicalComplex.tensorHom pX pYZ ≫ t)
          (MonoidalCategory.id_tensorHom
            (normalizedChainsForAssociativity X)
            (normalizedAlexanderWhitney Y Z)).symm
      _ = HomologicalComplex.tensorHom
          (pX ≫ 𝟙 (normalizedChainsForAssociativity X))
          (pYZ ≫ normalizedAlexanderWhitney Y Z) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = HomologicalComplex.tensorHom pX
          (alternatingAlexanderWhitney Y Z ≫
            HomologicalComplex.tensorHom pY pZ) := by
        rw [pInftyToNormalized_comp_normalizedAlexanderWhitney Y Z]
        exact congrArg
          (fun t => HomologicalComplex.tensorHom t
            (alternatingAlexanderWhitney Y Z ≫
              HomologicalComplex.tensorHom pY pZ))
          (Category.comp_id pX)
  have hsplit :
      HomologicalComplex.tensorHom pX
          (alternatingAlexanderWhitney Y Z ≫
            HomologicalComplex.tensorHom pY pZ) =
        HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
            (alternatingAlexanderWhitney Y Z) ≫
          HomologicalComplex.tensorHom pX
            (HomologicalComplex.tensorHom pY pZ) := by
    calc
      HomologicalComplex.tensorHom pX
          (alternatingAlexanderWhitney Y Z ≫
            HomologicalComplex.tensorHom pY pZ) =
        HomologicalComplex.tensorHom
          ((𝟙 (alternatingChains X)) ≫ pX)
          (alternatingAlexanderWhitney Y Z ≫
            HomologicalComplex.tensorHom pY pZ) := by
              exact congrArg
                (fun t => HomologicalComplex.tensorHom t
                  (alternatingAlexanderWhitney Y Z ≫
                    HomologicalComplex.tensorHom pY pZ))
                (Category.id_comp pX).symm
      _ = _ := (MonoidalCategory.tensorHom_comp_tensorHom
        (𝟙 (alternatingChains X)) (alternatingAlexanderWhitney Y Z)
        pX (HomologicalComplex.tensorHom pY pZ)).symm
  have hlast :
      HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
            (alternatingAlexanderWhitney Y Z) ≫
          HomologicalComplex.tensorHom pX
            (HomologicalComplex.tensorHom pY pZ) =
        (alternatingChains X ◁ alternatingAlexanderWhitney Y Z) ≫
          HomologicalComplex.tensorHom pX
            (HomologicalComplex.tensorHom pY pZ) := by
    exact congrArg
      (fun t => t ≫ HomologicalComplex.tensorHom pX
        (HomologicalComplex.tensorHom pY pZ))
      (MonoidalCategory.id_tensorHom
        (alternatingChains X) (alternatingAlexanderWhitney Y Z))
  exact hcore.trans (hsplit.trans hlast)

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
