import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
Conditional ordinary triangulated package for the direct bounded localization.

This is an audit declaration: it deliberately keeps every source-category and direct
weak-equivalence hypothesis explicit. The existing target source proves shift
compatibility for `boundedExactWeakEquivalence C`, but the stronger
`IsCompatibleWithTriangulation` input and an ordinary triangulated structure on
`BoundedComplexCategory C` are not currently available unconditionally.
-/
noncomputable abbrev isTriangulatedOfDirectLocalizationHypotheses
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [Preadditive (BoundedComplexCategory C)]
    [HasZeroObject (BoundedComplexCategory C)]
    [HasShift (BoundedComplexCategory C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (BoundedComplexCategory C) n).Additive]
    [Pretriangulated (BoundedComplexCategory C)]
    [IsTriangulated (BoundedComplexCategory C)]
    [Preadditive (Dbounded C)]
    [HasZeroObject (Dbounded C)]
    [HasShift (Dbounded C) ℤ]
    [∀ (n : ℤ), (shiftFunctor (Dbounded C) n).Additive]
    [(Dbounded.localization C).CommShift ℤ]
    [(Dbounded.localization C).Additive]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsCompatibleWithTriangulation] :
    letI : Pretriangulated (Dbounded C) :=
      Triangulated.Localization.pretriangulated
        (Dbounded.localization C) (boundedExactWeakEquivalence C)
    IsTriangulated (Dbounded C) := by
  let W : MorphismProperty (BoundedComplexCategory C) := boundedExactWeakEquivalence C
  letI : Pretriangulated (Dbounded C) :=
    Triangulated.Localization.pretriangulated (Dbounded.localization C) W
  haveI : (Dbounded.localization C).IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor (Dbounded.localization C) W
  exact Triangulated.Localization.isTriangulated (Dbounded.localization C) W

end Dbounded

section Checks

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check Dbounded.isTriangulatedOfDirectLocalizationHypotheses
#check Dbounded.homotopyComparison C
#check Dbounded.homotopyComparisonLocalizationIso C
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.localization_additiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check boundedExactWeakEquivalence_isCompatibleWithShift C
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C
#check CategoryTheory.Triangulated.Localization.pretriangulated
#check CategoryTheory.Triangulated.Localization.isTriangulated_functor
#check CategoryTheory.Triangulated.Localization.isTriangulated

end Checks

end LeanLCAExactChallenge
