import Mathlib.CategoryTheory.Localization.FiniteProducts
import LeanLCAExactChallenge.Derived.Bounded

/-!
Finite-products boundary audit for the semantic stable `Dbounded` route.

Mathlib currently supplies a localization API for finite products:
`Localization.hasFiniteProducts`.  This file records the exact conditional input needed to
apply that API to the strict `Dbounded` localization.  It does not construct finite limits or
finite colimits for `Dbounded C`; it only isolates a smaller finite-products subgoal.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedFiniteProductsBoundary

/--
Conditional finite-products constructor for `Dbounded C`.

The source category of bounded complexes must already have finite products, and the bounded
exact weak equivalences must be stable under finite products.  Under those two inputs,
mathlib's localization API supplies finite products in the localized category.
-/
noncomputable abbrev hasFiniteProductsOfLocalizationInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    [HasFiniteProducts (BoundedComplexCategory C)]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasFiniteProducts (Dbounded C) := by
  change HasFiniteProducts (boundedExactWeakEquivalence C).Localization
  infer_instance

/-- The finite-products route still needs these two product-specific localization inputs. -/
def finiteProductsLocalizationInputNames : List String :=
  ["HasFiniteProducts (BoundedComplexCategory C)",
    "(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts"]

theorem finiteProductsLocalizationInputNames_count :
    finiteProductsLocalizationInputNames.length = 2 := rfl

/--
Current audit state for the finite-products subroute.

The fields are intentionally optional strings: this blocker file records whether the target
has named constructors for the inputs, rather than assuming those constructors exist.
-/
structure FiniteProductsBoundaryState : Type where
  sourceFiniteProductsConstructor : Option String
  weakEquivalenceStableFiniteProductsConstructor : Option String
  localizationApi : String

/-- Current state: the localization API is known, but the two route inputs are not supplied here. -/
def currentFiniteProductsBoundaryState : FiniteProductsBoundaryState where
  sourceFiniteProductsConstructor := none
  weakEquivalenceStableFiniteProductsConstructor := none
  localizationApi := "CategoryTheory.Localization.hasFiniteProducts"

theorem currentFiniteProductsBoundaryState_source_missing :
    currentFiniteProductsBoundaryState.sourceFiniteProductsConstructor = none := rfl

theorem currentFiniteProductsBoundaryState_stability_missing :
    currentFiniteProductsBoundaryState.weakEquivalenceStableFiniteProductsConstructor = none := rfl

section Checks

#check hasFiniteProductsOfLocalizationInputs
#check finiteProductsLocalizationInputNames
#check finiteProductsLocalizationInputNames_count
#check FiniteProductsBoundaryState
#check currentFiniteProductsBoundaryState
#check currentFiniteProductsBoundaryState_source_missing
#check currentFiniteProductsBoundaryState_stability_missing
#check CategoryTheory.Localization.hasFiniteProducts
#check CategoryTheory.Localization.preservesFiniteProducts
#check CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts
#check BoundedComplexCategory
#check boundedExactWeakEquivalence
#check Dbounded
#check Dbounded.localization

end Checks

end DboundedFiniteProductsBoundary

end LeanLCAExactChallenge
