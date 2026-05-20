import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
Conditional ordinary `Pretriangulated (Dbounded C)` wrapper for the direct bounded
localization.

This is deliberately hypothesis-first: it does not assert that the direct bounded weak
equivalences currently have a calculus of fractions or are compatible with a triangulation.
It records the exact mathlib inputs that would let the existing
`Triangulated.Localization.pretriangulated` API apply to `Dbounded.localization`.
-/
noncomputable abbrev pretriangulatedOfDirectLocalizationHypotheses
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasZeroObject (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [Preadditive (Dbounded C)]
    [HasZeroObject (Dbounded C)]
    [HasShift (Dbounded C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (Dbounded C) n).Additive]
    [(Dbounded.localization C).CommShift ℤ]
    [(Dbounded.localization C).Additive]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsCompatibleWithTriangulation] :
    Pretriangulated (Dbounded C) := by
  let W : MorphismProperty (BoundedComplexCategory C) := boundedExactWeakEquivalence C
  exact Triangulated.Localization.pretriangulated (Dbounded.localization C) W

end Dbounded

section Checks

#check Dbounded.pretriangulatedOfDirectLocalizationHypotheses
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.localization_additiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check boundedExactWeakEquivalence_isCompatibleWithShift
#check CategoryTheory.Triangulated.Localization.pretriangulated

end Checks

end LeanLCAExactChallenge
