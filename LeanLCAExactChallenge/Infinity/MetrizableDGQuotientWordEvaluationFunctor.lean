/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationDifferentialCompletion

/-! # Functorial corrected Drinfeld word evaluation -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- The word-evaluation cochain map restricts to the supplied original enriched functor. -/
theorem evaluateCochainMap_original
    (X Y : ComplexCategory) :
    OriginalCoefficientHomToQuotient X Y ≫ E.evaluateCochainMap X Y =
      E.functor.map (Opposite.op Y) (Opposite.op X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rcases z with ⟨z⟩
  rcases z with ⟨x⟩
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [OriginalCoefficientHomToQuotient_apply_up]
  change (E.evaluateCoefficientDegree X Y n).hom
      (ULift.up ((originalHomInclusion X Y n).hom (ULift.up x))) = _
  rw [E.evaluateCoefficientDegree_apply_up]
  rw [originalHomInclusion_apply_up X Y n x]
  rw [E.evaluateGradedValue_inclusion]
  rw [E.evaluateWord_nil_apply]
  unfold evaluateNilProfile factorMap
  simp only [LinearMap.comp_apply]
  have hcancel := ConcreteCategory.congr_hom
    (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv_hom_id x
  simp only [ModuleCat.comp_apply, CategoryTheory.id_apply] at hcancel
  rw [hcancel]
  rfl

/-- Word evaluation preserves the quotient enriched identity. -/
theorem evaluateCochainMap_id (X : ComplexCategory) :
    quotientDGIdentity X ≫ E.evaluateCochainMap X X =
      eId QuotientDGCochain (E.obj X) := by
  rw [← OriginalCoefficientDGIdentity_map X]
  simp only [Category.assoc, E.evaluateCochainMap_original]
  exact E.functor.map_id (Opposite.op X)

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
