/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainEnrichedCategory

/-!
# Inclusion into the corrected quotient DG category

This file includes the original bounded-complex Hom cochain complex into the zero-word summand of
its corrected Drinfeld quotient Hom complex.
-/

set_option autoImplicit false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

/-- The universe-lifted module category used before changing coefficients to the quotient ring. -/
abbrev OriginalLargeZModule := ModuleCat.{1} ℤ

/-- The original DG Hom complex after lifting its module universe. -/
def originalLargeCochainComplex (X Y : ComplexCategory) :
    CochainComplex OriginalLargeZModule ℤ :=
  ((ModuleCat.uliftFunctor.{1} ℤ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (dgHomZModuleCochainComplex X Y)

/-- The original DG Hom complex after changing coefficients to the quotient coefficient ring. -/
def originalCoefficientCochainComplex (X Y : ComplexCategory) : QuotientDGCochain :=
  (quotientCoefficientChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (originalLargeCochainComplex X Y)

/-- The original Hom complex included into the zero-word summand before coefficient change. -/
def originalLargeHomToQuotientZ (X Y : ComplexCategory) :
    originalLargeCochainComplex X Y ⟶ quotientDGMappingCochainComplex X Y where
  f n := originalHomInclusion X Y n
  comm' n m hnm := by
    have hm : n + 1 = m := by simpa [ComplexShape.up] using hnm
    subst m
    rw [quotientDGMappingCochainComplex_d_succ]
    exact originalHomInclusion_comp_totalDifferential X Y n

/-- Inclusion of the original Hom complex into the corrected quotient. -/
def originalHomToQuotient (X Y : ComplexCategory) :
    originalCoefficientCochainComplex X Y ⟶ quotientCoefficientCochainComplex X Y :=
  (quotientCoefficientChange.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (originalLargeHomToQuotientZ X Y)

@[simp]
theorem originalHomToQuotient_f (X Y : ComplexCategory) (n : ℤ) :
    (originalHomToQuotient X Y).f n =
      ModuleCat.ofHom
        (quotientLinearMapChangeScalars (originalHomInclusion X Y n).hom) := rfl

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
