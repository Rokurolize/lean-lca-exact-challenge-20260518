import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Verdier comparison adjunction API search.

The available API exposes the factorization of the bounded homotopy localized
composite through `BoundedHomotopyDerivedCategory.verdierComparison`, but not
the factorized adjunctions or unit/counit membership proofs needed by mathlib's
calculus-of-fractions transfer theorems. This audit records the exact missing
input shape and the checked consumers.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD uJ uC

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace VerdierComparisonAdjunctionApiSearchW254

abbrev boundedHomotopyLocalizedComposite
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
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

abbrev factorizedLocalizedComposite
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  (boundedHomotopyExactWeakEquivalence C).Q ⋙
    BoundedHomotopyDerivedCategory.verdierComparison C

def localizedComposite_factorizationIso
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedHomotopyLocalizedComposite C ≅ factorizedLocalizedComposite C :=
  BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso C

theorem inverseImage_isInvertedBy_localizedComposite
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

theorem functorCategory_postcomp_iso_mem
    {J : Type uJ} {C : Type uC} [Category.{vD} J] [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso]
    {F G H : J ⥤ C} (α : F ⟶ G) (e : G ≅ H)
    (hα : W.functorCategory J α) :
    W.functorCategory J (α ≫ e.hom) := by
  intro j
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.postcomp W (e.hom.app j) (α.app j) (hα j)

theorem functorCategory_precomp_iso_mem
    {J : Type uJ} {C : Type uC} [Category.{vD} J] [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso]
    {F G H : J ⥤ C} (e : F ≅ G) (α : G ⟶ H)
    (hα : W.functorCategory J α) :
    W.functorCategory J (e.hom ≫ α) := by
  intro j
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.precomp W (e.hom.app j) (α.app j) (hα j)

structure RightRouteInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    factorizedLocalizedComposite C ⊣ rightAdjoint
  factorized_unit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) factorizedAdjunction.unit
  localizedAdjunction :
    boundedHomotopyLocalizedComposite C ⊣ rightAdjoint
  transported_unit_eq :
    localizedAdjunction.unit =
      factorizedAdjunction.unit ≫
        (Functor.isoWhiskerRight (localizedComposite_factorizationIso C).symm rightAdjoint).hom

structure LeftRouteInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    leftAdjoint ⊣ factorizedLocalizedComposite C
  factorized_counit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) factorizedAdjunction.counit
  localizedAdjunction :
    leftAdjoint ⊣ boundedHomotopyLocalizedComposite C
  transported_counit_eq :
    localizedAdjunction.counit =
      (Functor.isoWhiskerRight (localizedComposite_factorizationIso C).symm leftAdjoint).symm.hom ≫
        factorizedAdjunction.counit

theorem rightRoute_localized_unit_mem
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyInverseImageClass C).RespectsIso]
    (I : RightRouteInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.unit := by
  rw [I.transported_unit_eq]
  exact functorCategory_postcomp_iso_mem (boundedHomotopyInverseImageClass C)
    I.factorizedAdjunction.unit
    (Functor.isoWhiskerRight (localizedComposite_factorizationIso C).symm I.rightAdjoint)
    I.factorized_unit_mem

theorem leftRoute_localized_counit_mem
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyInverseImageClass C).RespectsIso]
    (I : LeftRouteInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.counit := by
  rw [I.transported_counit_eq]
  exact functorCategory_precomp_iso_mem (boundedHomotopyInverseImageClass C)
    (Functor.isoWhiskerRight (localizedComposite_factorizationIso C).symm I.leftAdjoint).symm
    I.factorizedAdjunction.counit
    I.factorized_counit_mem

theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_rightRoute
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    [(boundedHomotopyInverseImageClass C).RespectsIso]
    (I : RightRouteInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  CategoryTheory.Adjunction.hasLeftCalculusOfFractions I.localizedAdjunction
    (boundedHomotopyInverseImageClass C)
    (inverseImage_isInvertedBy_localizedComposite
      (BoundedComplexCategory.homotopyQuotient C)
      ((exactAcyclicHomotopyIsoClosure C).trW))
    (rightRoute_localized_unit_mem C I)

theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_leftRoute
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    [(boundedHomotopyInverseImageClass C).RespectsIso]
    (I : LeftRouteInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  CategoryTheory.Adjunction.hasRightCalculusOfFractions I.localizedAdjunction
    (boundedHomotopyInverseImageClass C)
    (inverseImage_isInvertedBy_localizedComposite
      (BoundedComplexCategory.homotopyQuotient C)
      ((exactAcyclicHomotopyIsoClosure C).trW))
    (leftRoute_localized_counit_mem C I)

structure ApiEntry : Type where
  declarationName : String
  found : Bool
  role : String

def verdierComparisonAdjunctionApiMap : List ApiEntry :=
  [{ declarationName := "BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso",
      found := true,
      role := "available factorization iso for the localized composite" },
    { declarationName := "CategoryTheory.Adjunction.hasLeftCalculusOfFractions",
      found := true,
      role := "consumer after localized right adjunction and unit membership" },
    { declarationName := "CategoryTheory.Adjunction.hasRightCalculusOfFractions",
      found := true,
      role := "consumer after localized left adjunction and counit membership" },
    { declarationName := "BoundedHomotopyDerivedCategory.verdierComparisonFactorizedRightAdjunction",
      found := false,
      role := "missing: factorizedLocalizedComposite C has a right adjoint" },
    { declarationName := "BoundedHomotopyDerivedCategory.verdierComparisonFactorizedUnitMem",
      found := false,
      role := "missing: factorized right-adjunction unit lies in boundedHomotopyInverseImageClass C" },
    { declarationName := "BoundedHomotopyDerivedCategory.verdierComparisonFactorizedLeftAdjunction",
      found := false,
      role := "missing: factorizedLocalizedComposite C has a left adjoint" },
    { declarationName := "BoundedHomotopyDerivedCategory.verdierComparisonFactorizedCounitMem",
      found := false,
      role := "missing: factorized left-adjunction counit lies in boundedHomotopyInverseImageClass C" }]

theorem verdierComparisonAdjunctionApiMap_length :
    verdierComparisonAdjunctionApiMap.length = 7 := rfl

structure SearchState : Type where
  route : String
  factorizationIsoFound : Bool
  factorizedRightAdjunctionFound : Bool
  factorizedLeftAdjunctionFound : Bool
  factorizedUnitMembershipFound : Bool
  factorizedCounitMembershipFound : Bool
  leftCalculusConsumerPackaged : Bool
  rightCalculusConsumerPackaged : Bool
  productSuccessClaimed : Bool

def currentSearchState : SearchState where
  route := "w254-right-route-api-packaging"
  factorizationIsoFound := true
  factorizedRightAdjunctionFound := false
  factorizedLeftAdjunctionFound := false
  factorizedUnitMembershipFound := false
  factorizedCounitMembershipFound := false
  leftCalculusConsumerPackaged := true
  rightCalculusConsumerPackaged := true
  productSuccessClaimed := false

theorem currentSearchState_missing_adjunctions :
    currentSearchState.factorizedRightAdjunctionFound = false ∧
      currentSearchState.factorizedLeftAdjunctionFound = false := by
  exact ⟨rfl, rfl⟩

theorem currentSearchState_missing_membership_inputs :
    currentSearchState.factorizedUnitMembershipFound = false ∧
      currentSearchState.factorizedCounitMembershipFound = false := by
  exact ⟨rfl, rfl⟩

theorem currentSearchState_has_consumers :
    currentSearchState.leftCalculusConsumerPackaged = true ∧
      currentSearchState.rightCalculusConsumerPackaged = true := by
  exact ⟨rfl, rfl⟩

theorem currentSearchState_not_productSuccess :
    currentSearchState.productSuccessClaimed = false := rfl

section Checks

#check BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso
#check Adjunction.ofNatIsoLeft
#check Adjunction.ofNatIsoRight
#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions
#check CategoryTheory.Adjunction.hasRightCalculusOfFractions
#check boundedHomotopyLocalizedComposite
#check factorizedLocalizedComposite
#check localizedComposite_factorizationIso
#check RightRouteInput
#check LeftRouteInput
#check rightRoute_localized_unit_mem
#check leftRoute_localized_counit_mem
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_rightRoute
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_leftRoute
#check verdierComparisonAdjunctionApiMap_length
#check currentSearchState_not_productSuccess

end Checks

end VerdierComparisonAdjunctionApiSearchW254

end LeanLCAExactChallenge
