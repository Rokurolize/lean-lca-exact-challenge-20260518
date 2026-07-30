/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientLocalizationComparison
import LeanLCAExactChallenge.Infinity.MetrizableDGRouteBMappingToEquivalence

/-! # Uniqueness boundary for the corrected Drinfeld localization

This module identifies the exact all-dimensional localization statement which turns the strict
ordinary-to-Drinfeld comparison into a bicategorical equivalence.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord

open CategoryTheory

/-- The corrected Drinfeld quotient has the required localization property when restriction
along the original bounded-complex nerve is an equivalence on every mapping quasicategory. -/
abbrev MetrizableCorrectedQuotientMappingLocalizationProperty : Prop :=
  MappingQuasicategoryLocalizationProperty
    (relativeNerveEdgeMarking relativeCategory)
    (ObjectProperty.homMk metrizableComplexNerveToCorrectedQuotientDG :
      metrizableComplexNerveQCat ⟶ correctedQuotientDGQCat)

/-- The all-dimensional localization property of the corrected quotient makes the strict
ordinary-to-Drinfeld comparison a bicategorical equivalence. -/
theorem metrizableEquivalenceForcingToCorrectedQuotientDG_isBicategoricalEquivalence
    (h : MetrizableCorrectedQuotientMappingLocalizationProperty) :
    IsBicategoricalEquivalence
      metrizableEquivalenceForcingToCorrectedQuotientDGQCatMap := by
  apply mappingLocalizationTriangleUniqueness
    (relativeNerveEdgeMarking relativeCategory)
    metrizableEquivalenceForcingQCatMap
    (ObjectProperty.homMk metrizableComplexNerveToCorrectedQuotientDG :
      metrizableComplexNerveQCat ⟶ correctedQuotientDGQCat)
  · apply ObjectProperty.hom_ext SSet.Quasicategory
    exact metrizableEquivalenceForcingToCorrectedQuotientDG_triangle
  · exact metrizableEquivalenceForcingMappingLocalizationProperty_direct
  · exact h

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
