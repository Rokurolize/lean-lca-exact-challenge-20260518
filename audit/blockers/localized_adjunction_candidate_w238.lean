import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
W238 localized-adjunction candidate surface.

This audit consolidates the bounded homotopy/Verdier inverse-image calculus frontier:
a right adjoint plus unit membership gives left calculus, while a left adjoint plus
counit membership gives right calculus.  It is intentionally conditional and does
not claim a concrete adjunction or product success.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizedAdjunctionCandidateW238

theorem inverseImage_isInvertedBy_localizedFunctor
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions] :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

theorem inverseImage_hasLeftCalculusOfFractions_of_rightAdjoint
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions]
    (R : MorphismProperty.Localization W ⥤ D)
    (adj : F ⋙ W.Q ⊣ R)
    (hunit : (W.inverseImage F).functorCategory D adj.unit) :
    (W.inverseImage F).HasLeftCalculusOfFractions :=
  CategoryTheory.Adjunction.hasLeftCalculusOfFractions adj (W.inverseImage F)
    (inverseImage_isInvertedBy_localizedFunctor F W) hunit

theorem inverseImage_hasRightCalculusOfFractions_of_leftAdjoint
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions]
    (L : MorphismProperty.Localization W ⥤ D)
    (adj : L ⊣ F ⋙ W.Q)
    (hcounit : (W.inverseImage F).functorCategory D adj.counit) :
    (W.inverseImage F).HasRightCalculusOfFractions :=
  CategoryTheory.Adjunction.hasRightCalculusOfFractions adj (W.inverseImage F)
    (inverseImage_isInvertedBy_localizedFunctor F W) hcounit

abbrev boundedHomotopyLocalizedFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

abbrev boundedHomotopyInverseImageClass
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  ((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
    (BoundedComplexCategory.homotopyQuotient C)

structure BoundedHomotopyLocalizedAdjunctionSurface
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] :
    Type (max u v) where
  rightAdjointForLeftCalculus :
    MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  rightAdjunction :
    boundedHomotopyLocalizedFunctor C ⊣ rightAdjointForLeftCalculus
  unit_mem :
    boundedHomotopyInverseImageClass C |>.functorCategory
      (BoundedComplexCategory C) rightAdjunction.unit
  leftAdjointForRightCalculus :
    MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  leftAdjunction :
    leftAdjointForRightCalculus ⊣ boundedHomotopyLocalizedFunctor C
  counit_mem :
    boundedHomotopyInverseImageClass C |>.functorCategory
      (BoundedComplexCategory C) leftAdjunction.counit

theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_surface
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (S : BoundedHomotopyLocalizedAdjunctionSurface C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  inverseImage_hasLeftCalculusOfFractions_of_rightAdjoint
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    S.rightAdjointForLeftCalculus S.rightAdjunction S.unit_mem

theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_surface
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (S : BoundedHomotopyLocalizedAdjunctionSurface C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  inverseImage_hasRightCalculusOfFractions_of_leftAdjoint
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    S.leftAdjointForRightCalculus S.leftAdjunction S.counit_mem

structure LocalizedAdjunctionCandidateState : Type where
  route : String
  concreteAdjunctionFound : Bool
  productSuccessClaimed : Bool

def currentLocalizedAdjunctionCandidateState : LocalizedAdjunctionCandidateState where
  route := "two-sided-localized-adjunction-surface"
  concreteAdjunctionFound := false
  productSuccessClaimed := false

theorem currentLocalizedAdjunctionCandidateState_not_productSuccess :
    currentLocalizedAdjunctionCandidateState.productSuccessClaimed = false := rfl

section Checks

#check inverseImage_hasLeftCalculusOfFractions_of_rightAdjoint
#check inverseImage_hasRightCalculusOfFractions_of_leftAdjoint
#check boundedHomotopyLocalizedFunctor
#check boundedHomotopyInverseImageClass
#check BoundedHomotopyLocalizedAdjunctionSurface
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_surface
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_surface
#check currentLocalizedAdjunctionCandidateState_not_productSuccess

end Checks

end LocalizedAdjunctionCandidateW238

end LeanLCAExactChallenge
