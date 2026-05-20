import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Audit for W233: bounded homotopy localized adjunction input.

W228 identified the available mathlib route: if the localized composite
`F ⋙ W.Q` has a right adjoint and the adjunction unit is in the inverse-image
class, then `W.inverseImage F` has a left calculus of fractions.  This file
records the exact local input for the bounded homotopy/Verdier composite and
keeps the downstream theorem conditional, rather than asserting an adjunction
that is not exposed in the local API.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedHomotopyLocalizedAdjunctionW233

/--
For an ambient class `W` with a left calculus, the composite with the localization
functor inverts the inverse-image class.
-/
theorem inverseImage_isInvertedBy_localizedFunctor
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions] :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

/--
Adjunction-specialized inverse-image transfer.  This is the smaller theorem
showing that a right adjoint to the localized composite, plus the unit-membership
condition required by mathlib, implies left calculus for the inverse-image class.
-/
theorem inverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions]
    (R : MorphismProperty.Localization W ⥤ D)
    (adj : F ⋙ W.Q ⊣ R)
    (hunit : (W.inverseImage F).functorCategory D adj.unit) :
    (W.inverseImage F).HasLeftCalculusOfFractions :=
  CategoryTheory.Adjunction.hasLeftCalculusOfFractions adj (W.inverseImage F)
    (inverseImage_isInvertedBy_localizedFunctor F W) hunit

/-- The localized bounded homotopy/Verdier composite whose right adjoint is the missing input. -/
abbrev boundedHomotopyLocalizedFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

/--
The exact local input giving the required right adjoint route for W233.  The
`unit_mem` field is explicit because `Adjunction.hasLeftCalculusOfFractions`
requires the adjunction unit to lie in the weak-equivalence class.
-/
structure BoundedHomotopyLocalizedAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] : Type (max u v) where
  rightAdjoint :
    MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  adjunction :
    boundedHomotopyLocalizedFunctor C ⊣ rightAdjoint
  unit_mem :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).functorCategory
        (BoundedComplexCategory C) adjunction.unit

/-- Existing local input: triangulated closedness gives the ambient Verdier left calculus. -/
theorem ambientIsoClosureLeftCalculus_of_closed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/--
The bounded inverse-image class has a left calculus once the localized composite
has the right-adjoint input packaged above.
-/
theorem boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedAdjunctionInput C) :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).HasLeftCalculusOfFractions :=
  inverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    I.rightAdjoint I.adjunction I.unit_mem

/--
Since `boundedHomotopyExactWeakEquivalence` is definitionally this inverse image,
the same localized adjunction input proves the bounded homotopy target.
-/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedAdjunctionInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction C I

/-- Concrete finite-product target, still conditional on the localized adjunction input. -/
theorem metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions
    [((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedAdjunctionInput MetrizableLCA.{0}) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_localizedAdjunction
    MetrizableLCA.{0} I

/-- Search findings recorded as checked data. -/
def localizedAdjunctionSearchFindings : List String :=
  ["CategoryTheory.Adjunction.hasLeftCalculusOfFractions applies to W.inverseImage F once F composed with W.Q has a right adjoint and its unit lies in W.inverseImage F",
    "for any W with left calculus, W.inverseImage F is inverted by F composed with W.Q",
    "the exact bounded homotopy input is a right adjoint to BoundedComplexCategory.homotopyQuotient C composed with exactAcyclicHomotopyIsoClosure C trW localization, plus unit membership",
    "exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 supplies the ambient Verdier left calculus",
    "no local right adjoint was found for the bounded homotopy localized composite, so the theorem is intentionally conditional"]

theorem localizedAdjunctionSearchFindings_count :
    localizedAdjunctionSearchFindings.length = 5 := rfl

section Checks

#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions
#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions'
#check MorphismProperty.inverseImage
#check BoundedComplexCategory.homotopyQuotient
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check inverseImage_isInvertedBy_localizedFunctor
#check inverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyLocalizedFunctor
#check BoundedHomotopyLocalizedAdjunctionInput
#check ambientIsoClosureLeftCalculus_of_closed2
#check boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_localizedAdjunction
#check metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions
#check localizedAdjunctionSearchFindings
#check localizedAdjunctionSearchFindings_count

end Checks

end BoundedHomotopyLocalizedAdjunctionW233

end LeanLCAExactChallenge
