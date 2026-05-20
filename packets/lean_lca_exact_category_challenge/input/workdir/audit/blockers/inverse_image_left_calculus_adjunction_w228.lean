import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Audit for W228: inverse-image left calculus via adjunctions.

W226 isolated the arbitrary inverse-image transfer
`W.HasLeftCalculusOfFractions → (W.inverseImage F).HasLeftCalculusOfFractions`.
Mathlib does not provide that transfer for an arbitrary functor. The available
adjunction theorem does give a usable special case: if the composite
`F ⋙ W.Q` has a right adjoint and the adjunction unit lies in `W.inverseImage F`,
then `W.inverseImage F` has a left calculus of fractions.

For the bounded homotopy route, this reduces the remaining categorical input to a
right adjoint for
`BoundedComplexCategory.homotopyQuotient C ⋙ (exactAcyclicHomotopyIsoClosure C).trW.Q`
plus the explicit unit-membership field below. No such adjunction is currently
exposed for `BoundedComplexCategory.homotopyQuotient C` in the local API.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace InverseImageLeftCalculusAdjunctionW228

/--
If `W` already has a left calculus, the localized composite `F ⋙ W.Q` inverts
the pullback class `W.inverseImage F`.
-/
theorem inverseImage_isInvertedBy_localizedFunctor
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions] :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

/--
Adjunction-specialized inverse-image transfer. This is the provable bridge found
in mathlib: apply `CategoryTheory.Adjunction.hasLeftCalculusOfFractions` to
`W.inverseImage F`, using the localized composite as the left adjoint.
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

/-- The localized functor whose adjunction would discharge the bounded homotopy case. -/
abbrev boundedHomotopyLocalizedFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

/-- The explicit adjunction-style input left after applying the mathlib theorem. -/
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

/-- The ambient Verdier left calculus supplied by the existing local theorem. -/
theorem ambientIsoClosureLeftCalculus_of_closed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/--
The bounded inverse-image class follows from the ambient left calculus and the
localized adjunction input.
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
the same adjunction input discharges W226's bounded homotopy target.
-/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedAdjunctionInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_localizedAdjunction C I

/-- Concrete finite-product target, still conditional on the adjunction-style input. -/
theorem metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions
    [((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedAdjunctionInput MetrizableLCA.{0}) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_localizedAdjunction
    MetrizableLCA.{0} I

/-- Search findings recorded as checked data. -/
def adjunctionSearchFindings : List String :=
  ["CategoryTheory.Adjunction.hasLeftCalculusOfFractions proves a pullback left calculus when the pullback class is inverted by a left adjoint and the adjunction unit lies in that class",
    "for any W with left calculus, W.inverseImage F is inverted by F composed with W.Q",
    "therefore the bounded homotopy case reduces to a right adjoint for BoundedComplexCategory.homotopyQuotient C composed with the Verdier localization plus the explicit unit membership field",
    "the existing theorem exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 supplies the ambient Verdier left calculus",
    "no local adjunction was found for BoundedComplexCategory.homotopyQuotient C or for its composite with the Verdier localization"]

theorem adjunctionSearchFindings_count :
    adjunctionSearchFindings.length = 5 := rfl

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
#check adjunctionSearchFindings
#check adjunctionSearchFindings_count

end Checks

end InverseImageLeftCalculusAdjunctionW228

end LeanLCAExactChallenge
