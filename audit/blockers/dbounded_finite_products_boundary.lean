import Mathlib.CategoryTheory.Localization.FiniteProducts
import LeanLCAExactChallenge.Derived.Bounded

/-!
Finite-products boundary audit for the semantic stable `Dbounded` route.

Mathlib currently supplies a localization API for finite products:
`Localization.hasFiniteProducts`.  This file records the exact conditional input needed to
apply that API to the strict `Dbounded` localization.  It does not construct finite limits or
finite colimits for `Dbounded C`; it reduces finite products to stability of the weak
equivalences under finite products.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedFiniteProductsBoundary

/--
Conditional finite-products constructor for `Dbounded C`.

The source category of bounded complexes now has finite products when `C` has finite limits.
Under finite-product stability of the bounded exact weak equivalences, mathlib's localization
API supplies finite products in the localized category.
-/
noncomputable abbrev hasFiniteProductsOfLocalizationInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasFiniteProducts (Dbounded C) :=
  Dbounded.hasFiniteProductsOfStableFiniteProducts C

/-- The finite-products route now has one remaining product-specific localization input. -/
def remainingFiniteProductsInputNames : List String :=
  ["(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts"]

theorem finiteProductsLocalizationInputNames_count :
    remainingFiniteProductsInputNames.length = 1 := rfl

/--
Current audit state for the finite-products subroute.

The fields are intentionally optional strings: this blocker file records whether the target
has named constructors for the inputs, rather than assuming those constructors exist.
-/
structure FiniteProductsBoundaryState : Type where
  sourceFiniteProductsConstructor : String
  weakEquivalenceStableFiniteProductsConstructor : Option String
  localizationApi : String

/-- Current state: source finite products are supplied; weak-equivalence stability remains open. -/
def currentFiniteProductsBoundaryState : FiniteProductsBoundaryState where
  sourceFiniteProductsConstructor := "BoundedComplexCategory.hasFiniteLimits"
  weakEquivalenceStableFiniteProductsConstructor := none
  localizationApi := "CategoryTheory.Localization.hasFiniteProducts"

theorem currentFiniteProductsBoundaryState_source_supplied :
    currentFiniteProductsBoundaryState.sourceFiniteProductsConstructor =
      "BoundedComplexCategory.hasFiniteLimits" := rfl

theorem currentFiniteProductsBoundaryState_stability_missing :
    currentFiniteProductsBoundaryState.weakEquivalenceStableFiniteProductsConstructor = none := rfl

section Checks

#check hasFiniteProductsOfLocalizationInputs
#check remainingFiniteProductsInputNames
#check finiteProductsLocalizationInputNames_count
#check FiniteProductsBoundaryState
#check currentFiniteProductsBoundaryState
#check currentFiniteProductsBoundaryState_source_supplied
#check currentFiniteProductsBoundaryState_stability_missing
#check CategoryTheory.Localization.hasFiniteProducts
#check CategoryTheory.Localization.preservesFiniteProducts
#check CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts
#check BoundedComplexCategory.hasFiniteLimits
#check BoundedComplexCategory.hasFiniteColimits
#check BoundedComplexCategory
#check boundedExactWeakEquivalence
#check Dbounded
#check Dbounded.localization
#check Dbounded.hasFiniteProductsOfStableFiniteProducts

end Checks

end DboundedFiniteProductsBoundary

end LeanLCAExactChallenge
