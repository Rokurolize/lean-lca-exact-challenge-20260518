import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites

/-!
Audit boundary for the opposite-localization finite-colimits route.

This file records the formal pieces that are already available without claiming finite
colimits for `Dbounded C`. The remaining mathematical input is finite limits on the
opposite localized category, which in practice must still come from finite-product stability
and an equalizer/pullback transfer on the opposite side.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace OppositeLocalizationFiniteColimitsBoundary

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
The opposite of the existing bounded-derived localization functor is already a localization
for the opposite weak-equivalence class.
-/
theorem dboundedLocalization_op_isLocalization [HasBinaryBiproducts C] :
    ((Dbounded.localization C).op).IsLocalization (boundedExactWeakEquivalence C).op := by
  infer_instance

/-- The opposite of the direct bounded localization functor. -/
abbrev oppositeDirectLocalization [HasBinaryBiproducts C] :
    (BoundedComplexCategory C)ᵒᵖ ⥤ (Dbounded C)ᵒᵖ :=
  (Dbounded.localization C).op

/--
Canonical comparison from the abstract opposite localization model to `(Dbounded C)ᵒᵖ`.
-/
abbrev oppositeModelEquivalence [HasBinaryBiproducts C] :
    (boundedExactWeakEquivalence C).op.Localization ≌ (Dbounded C)ᵒᵖ :=
  Localization.equivalenceFromModel
    (oppositeDirectLocalization C) (boundedExactWeakEquivalence C).op

/--
The abstract opposite localization functor agrees with the concrete opposite localization
after applying the comparison equivalence.
-/
abbrev oppositeModelLocalizationIso [HasBinaryBiproducts C] :
    (boundedExactWeakEquivalence C).op.Q ⋙ (oppositeModelEquivalence C).functor ≅
      oppositeDirectLocalization C :=
  Localization.qCompEquivalenceFromModelFunctorIso
    (oppositeDirectLocalization C) (boundedExactWeakEquivalence C).op

/--
Finite limits on the opposite of `Dbounded C` would be exactly the missing ordinary finite
colimits on `Dbounded C`.
-/
theorem hasFiniteColimits_dbounded_of_op_hasFiniteLimits [HasBinaryBiproducts C]
    [HasFiniteLimits (Dbounded C)ᵒᵖ] :
    HasFiniteColimits (Dbounded C) := by
  exact Limits.hasFiniteLimits_opposite_iff.mp inferInstance

/--
Finite limits transfer from the abstract opposite localization model to `(Dbounded C)ᵒᵖ`
through the canonical comparison equivalence.
-/
theorem dboundedOp_hasFiniteLimits_of_oppositeLocalization_hasFiniteLimits
    [HasBinaryBiproducts C]
    [HasFiniteLimits (boundedExactWeakEquivalence C).op.Localization] :
    HasFiniteLimits (Dbounded C)ᵒᵖ where
  out J _ _ := by
    haveI : HasLimitsOfShape J (boundedExactWeakEquivalence C).op.Localization := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence
      (oppositeModelEquivalence C).inverse

/--
Finite limits on the abstract opposite localization are enough to obtain finite colimits on
`Dbounded C`.
-/
theorem hasFiniteColimits_dbounded_of_oppositeLocalization_hasFiniteLimits
    [HasBinaryBiproducts C]
    [HasFiniteLimits (boundedExactWeakEquivalence C).op.Localization] :
    HasFiniteColimits (Dbounded C) := by
  haveI : HasFiniteLimits (Dbounded C)ᵒᵖ :=
    dboundedOp_hasFiniteLimits_of_oppositeLocalization_hasFiniteLimits C
  exact hasFiniteColimits_dbounded_of_op_hasFiniteLimits C

/--
Mathlib's finite-products localization theorem applies to the opposite localizer under the
expected opposite-side finite-product stability hypotheses.
-/
noncomputable abbrev oppositeLocalizationHasFiniteProducts_of_stableFiniteProducts
    [HasBinaryBiproducts C]
    [HasFiniteProducts (BoundedComplexCategory C)ᵒᵖ]
    [((boundedExactWeakEquivalence C).op).ContainsIdentities]
    [((boundedExactWeakEquivalence C).op).IsStableUnderFiniteProducts] :
    HasFiniteProducts ((boundedExactWeakEquivalence C).op.Localization) := by
  infer_instance

/--
Named remaining input for downstream work: finite limits on the abstract opposite
localization model.
-/
structure OppositeLocalizationFiniteLimitInput [HasBinaryBiproducts C] : Prop where
  finiteLimits : HasFiniteLimits (boundedExactWeakEquivalence C).op.Localization

/-- Wrapped form for callers that prefer carrying the remaining input as one structure. -/
theorem hasFiniteColimits_dbounded_of_oppositeFiniteLimitInput
    [HasBinaryBiproducts C] (h : OppositeLocalizationFiniteLimitInput C) :
    HasFiniteColimits (Dbounded C) := by
  haveI : HasFiniteLimits (boundedExactWeakEquivalence C).op.Localization := h.finiteLimits
  exact hasFiniteColimits_dbounded_of_oppositeLocalization_hasFiniteLimits C

end OppositeLocalizationFiniteColimitsBoundary

end LeanLCAExactChallenge
