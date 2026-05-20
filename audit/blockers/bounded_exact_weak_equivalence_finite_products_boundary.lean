import LeanLCAExactChallenge.Derived.Bounded

/-!
Bounded exact weak equivalence finite-product boundary.

The MetrizableLCA route is currently blocked below this level by the degreewise comparison
between mapping cones and products.  This file records the exact upper interface: once finite
products of bounded morphisms are known to have exact-acyclic mapping cones, mathlib's
`MorphismProperty.IsStableUnderFiniteProducts` instance follows immediately.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedExactWeakEquivalenceFiniteProductsBoundary

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/--
The remaining finite-product mapping-cone input for `boundedExactWeakEquivalence`.

It is intentionally stated at the `Limits.Pi.map` level because that is exactly the API used by
`MorphismProperty.IsStableUnderProductsOfShape.mk`.
-/
abbrev FiniteProductMappingConeInput : Prop :=
  ∀ (J : Type) [Finite J]
    (X₁ X₂ : J → BoundedComplexCategory C) [HasProduct X₁] [HasProduct X₂]
    (f : ∀ j, X₁ j ⟶ X₂ j),
    (∀ j, boundedExactWeakEquivalence C (f j)) →
      boundedExactWeakEquivalence C (Limits.Pi.map f)

/--
The upper closure step for finite products of bounded exact weak equivalences.

This does not prove the mapping-cone comparison.  It proves that no further localization API is
missing above that comparison: the input above directly gives the class required by
`Dbounded.hasFiniteProductsOfStableFiniteProducts`.
-/
theorem isStableUnderFiniteProducts_of_finiteProductMappingConeInput
    (h : FiniteProductMappingConeInput C) :
    (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ := by
    exact MorphismProperty.IsStableUnderProductsOfShape.mk
      (boundedExactWeakEquivalence C) J
      (h J)

/-- The Dbounded finite-product API that becomes available after the same input is installed. -/
noncomputable abbrev dboundedHasFiniteProductsOf_finiteProductMappingConeInput
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    (h : FiniteProductMappingConeInput C) :
    HasFiniteProducts (Dbounded C) := by
  haveI : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts :=
    isStableUnderFiniteProducts_of_finiteProductMappingConeInput C h
  exact Dbounded.hasFiniteProductsOfStableFiniteProducts C

section Checks

#check FiniteProductMappingConeInput
#check isStableUnderFiniteProducts_of_finiteProductMappingConeInput
#check dboundedHasFiniteProductsOf_finiteProductMappingConeInput
#check Dbounded.hasFiniteProductsOfStableFiniteProducts
#check MorphismProperty.IsStableUnderProductsOfShape.mk
#check boundedExactWeakEquivalence

end Checks

end BoundedExactWeakEquivalenceFiniteProductsBoundary

end LeanLCAExactChallenge
