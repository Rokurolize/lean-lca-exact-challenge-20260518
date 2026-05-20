import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.Opposite

/-!
Audit boundary for the opposite-localization finite-colimits route.

This file records the formal pieces that are already available without claiming finite
colimits for `Dbounded C`. The remaining mathematical input is finite limits on the
opposite localized category, which in practice must still come from finite-product stability
and an equalizer/pullback transfer on the opposite side.
-/

set_option autoImplicit false

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

/--
Finite limits on the opposite of `Dbounded C` would be exactly the missing ordinary finite
colimits on `Dbounded C`.
-/
theorem hasFiniteColimits_dbounded_of_op_hasFiniteLimits [HasBinaryBiproducts C]
    [HasFiniteLimits (Dbounded C)ᵒᵖ] :
    HasFiniteColimits (Dbounded C) := by
  exact Limits.hasFiniteLimits_opposite_iff.mp inferInstance

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

end OppositeLocalizationFiniteColimitsBoundary

end LeanLCAExactChallenge
