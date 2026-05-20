import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Audit for the right-calculus analogue of the W233 localized-adjunction route.

The opposite finite-limit route needs right calculus for the direct bounded exact weak
equivalences.  The existing `boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed`
reduces this to right calculus for `boundedHomotopyExactWeakEquivalence C`.  This file records
the mathlib adjunction route for that right calculus: a left adjoint to the localized bounded
homotopy/Verdier composite, plus counit membership, is enough.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedHomotopyLocalizedLeftAdjointW250

/--
For an ambient class `W`, the composite with the localization functor inverts the
inverse-image class.  This is shared by the left- and right-calculus adjunction routes.
-/
theorem inverseImage_isInvertedBy_localizedFunctor
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

/--
Adjunction-specialized inverse-image transfer for right calculus.  If the localized
composite has a left adjoint and the adjunction counit lies in the inverse-image class,
mathlib gives right calculus for that inverse image.
-/
theorem inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasRightCalculusOfFractions]
    (L : MorphismProperty.Localization W ⥤ D)
    (adj : L ⊣ F ⋙ W.Q)
    (hcounit : (W.inverseImage F).functorCategory D adj.counit) :
    (W.inverseImage F).HasRightCalculusOfFractions :=
  CategoryTheory.Adjunction.hasRightCalculusOfFractions adj (W.inverseImage F)
    (inverseImage_isInvertedBy_localizedFunctor F W) hcounit

/-- The localized bounded homotopy/Verdier composite whose left adjoint is the missing input. -/
abbrev boundedHomotopyLocalizedFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

/--
The exact local input for the right-calculus route.  It is dual to W233's right-adjoint
input for left calculus.
-/
structure BoundedHomotopyLocalizedLeftAdjointInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions] : Type (max u v) where
  leftAdjoint :
    MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  adjunction :
    leftAdjoint ⊣ boundedHomotopyLocalizedFunctor C
  counit_mem :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).functorCategory
        (BoundedComplexCategory C) adjunction.counit

/-- Existing local input: triangulated closedness gives the ambient Verdier right calculus. -/
theorem ambientIsoClosureRightCalculus_of_closed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2 C

/--
The bounded inverse-image class has a right calculus once the localized composite has the
left-adjoint input packaged above.
-/
theorem boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : BoundedHomotopyLocalizedLeftAdjointInput C) :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).HasRightCalculusOfFractions :=
  inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    I.leftAdjoint I.adjunction I.counit_mem

/--
Since `boundedHomotopyExactWeakEquivalence` is definitionally this inverse image, the same
localized adjunction input proves the bounded homotopy right-calculus target.
-/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : BoundedHomotopyLocalizedLeftAdjointInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction C I

/--
Concrete opposite-route consumer: after exact-acyclic homotopy-object iso-closedness, the
localized left-adjoint input gives right calculus for direct bounded exact weak equivalences.
-/
theorem boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedLeftAdjoint
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : BoundedHomotopyLocalizedLeftAdjointInput C) :
    (boundedExactWeakEquivalence C).HasRightCalculusOfFractions := by
  haveI : (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
    boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction C I
  exact boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed C

/-- Concrete default-universe target, still conditional on the localized left-adjoint input. -/
theorem metrizableLCABoundedExactWeakEquivalence_hasRightCalculusOfFractions
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW).HasRightCalculusOfFractions]
    (I : BoundedHomotopyLocalizedLeftAdjointInput MetrizableLCA.{0}) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasRightCalculusOfFractions :=
  boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedLeftAdjoint
    MetrizableLCA.{0} I

/-- Search findings recorded as checked data. -/
def localizedLeftAdjointSearchFindings : List String :=
  ["CategoryTheory.Adjunction.hasRightCalculusOfFractions is the dual of the W233 theorem and applies to W.inverseImage F",
    "right calculus for boundedExactWeakEquivalence C is needed by the opposite finite-limit route",
    "boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed already transfers right calculus from boundedHomotopyExactWeakEquivalence C",
    "the exact bounded homotopy input is a left adjoint to the localized homotopy quotient composite, plus counit membership",
    "this file does not construct that left adjoint or claim product success"]

theorem localizedLeftAdjointSearchFindings_count :
    localizedLeftAdjointSearchFindings.length = 5 := rfl

section Checks

#check CategoryTheory.Adjunction.hasRightCalculusOfFractions
#check MorphismProperty.inverseImage
#check BoundedComplexCategory.homotopyQuotient
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed
#check inverseImage_isInvertedBy_localizedFunctor
#check inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyLocalizedFunctor
#check BoundedHomotopyLocalizedLeftAdjointInput
#check ambientIsoClosureRightCalculus_of_closed2
#check boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction
#check boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedLeftAdjoint
#check metrizableLCABoundedExactWeakEquivalence_hasRightCalculusOfFractions
#check localizedLeftAdjointSearchFindings
#check localizedLeftAdjointSearchFindings_count

end Checks

end BoundedHomotopyLocalizedLeftAdjointW250

end LeanLCAExactChallenge
