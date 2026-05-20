import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Factorized localized adjunction and membership inputs.

This audit keeps the focus on the factorized composite
`(boundedHomotopyExactWeakEquivalence C).Q ⋙
  BoundedHomotopyDerivedCategory.verdierComparison C`.
The local API exposes the factorization isomorphism and generic transport
operations, but no concrete factorized right/left adjunction or unit/counit
membership theorem was found.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂ v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace FactorizedLocalizedAdjunctionMembershipW257

section GenericTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

theorem functorCategory_postcomp_iso_mem
    (W : MorphismProperty C) [W.RespectsIso]
    {F G H : C ⥤ C} (α : F ⟶ G) (e : G ≅ H)
    (hα : W.functorCategory C α) :
    W.functorCategory C (α ≫ e.hom) := by
  intro X
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.postcomp W (e.hom.app X) (α.app X) (hα X)

theorem functorCategory_precomp_iso_mem
    (W : MorphismProperty D) [W.RespectsIso]
    {F G H : D ⥤ D} (e : F ≅ G) (α : G ⟶ H)
    (hα : W.functorCategory D α) :
    W.functorCategory D (e.hom ≫ α) := by
  intro X
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.precomp W (e.hom.app X) (α.app X) (hα X)

structure GenericRightAdjunctionTransportInput
    (W : MorphismProperty C) [W.RespectsIso]
    {F F' : C ⥤ D} (e : F ≅ F') (R : D ⥤ C) : Type (max u₁ u₂ v₁ v₂) where
  factorizedAdjunction : F' ⊣ R
  factorized_unit_mem : W.functorCategory C factorizedAdjunction.unit
  localizedAdjunction : F ⊣ R
  localized_unit_mem : W.functorCategory C localizedAdjunction.unit

def genericRightAdjunctionTransportInput
    (W : MorphismProperty C) [W.RespectsIso]
    {F F' : C ⥤ D} (e : F ≅ F') {R : D ⥤ C}
    (adj : F' ⊣ R) (hunit : W.functorCategory C adj.unit) :
    GenericRightAdjunctionTransportInput W e R where
  factorizedAdjunction := adj
  factorized_unit_mem := hunit
  localizedAdjunction := adj.ofNatIsoLeft e.symm
  localized_unit_mem := by
    rw [show (adj.ofNatIsoLeft e.symm).unit =
        adj.unit ≫ (Functor.isoWhiskerRight e.symm R).hom by
      simp [Adjunction.ofNatIsoLeft, Functor.isoWhiskerRight_hom]]
    exact functorCategory_postcomp_iso_mem W adj.unit (Functor.isoWhiskerRight e.symm R)
      hunit

structure GenericLeftAdjunctionTransportInput
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ C} (e : F ≅ F') (L : C ⥤ D) : Type (max u₁ u₂ v₁ v₂) where
  factorizedAdjunction : L ⊣ F'
  factorized_counit_mem : W.functorCategory D factorizedAdjunction.counit
  localizedAdjunction : L ⊣ F
  localized_counit_mem : W.functorCategory D localizedAdjunction.counit

def genericLeftAdjunctionTransportInput
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ C} (e : F ≅ F') {L : C ⥤ D}
    (adj : L ⊣ F') (hcounit : W.functorCategory D adj.counit) :
    GenericLeftAdjunctionTransportInput W e L where
  factorizedAdjunction := adj
  factorized_counit_mem := hcounit
  localizedAdjunction := adj.ofNatIsoRight e.symm
  localized_counit_mem := by
    rw [show (adj.ofNatIsoRight e.symm).counit =
        (Functor.isoWhiskerRight e.symm L).symm.hom ≫ adj.counit by
      simp [Adjunction.ofNatIsoRight, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerRight_symm]]
    exact functorCategory_precomp_iso_mem W (Functor.isoWhiskerRight e.symm L).symm
      adj.counit hcounit

end GenericTransport

section FactorizedRoute

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

structure FactorizedRightAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    factorizedLocalizedComposite C ⊣ rightAdjoint

structure FactorizedLeftAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    leftAdjoint ⊣ factorizedLocalizedComposite C

structure FactorizedUnitMembershipInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightInput : FactorizedRightAdjunctionInput C
  factorized_unit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) rightInput.factorizedAdjunction.unit

structure FactorizedCounitMembershipInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftInput : FactorizedLeftAdjunctionInput C
  factorized_counit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) leftInput.factorizedAdjunction.counit

structure ComparisonFactorRightTransportInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    factorizedLocalizedComposite C ⊣ rightAdjoint
  factorized_unit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) factorizedAdjunction.unit
  transported :
    GenericRightAdjunctionTransportInput (boundedHomotopyInverseImageClass C)
      (localizedComposite_factorizationIso C) rightAdjoint :=
    genericRightAdjunctionTransportInput (boundedHomotopyInverseImageClass C)
      (localizedComposite_factorizationIso C) factorizedAdjunction factorized_unit_mem

structure ComparisonFactorLeftTransportInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    leftAdjoint ⊣ factorizedLocalizedComposite C
  factorized_counit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) factorizedAdjunction.counit
  transported :
    GenericLeftAdjunctionTransportInput (boundedHomotopyInverseImageClass C)
      (localizedComposite_factorizationIso C) leftAdjoint :=
    genericLeftAdjunctionTransportInput (boundedHomotopyInverseImageClass C)
      (localizedComposite_factorizationIso C) factorizedAdjunction factorized_counit_mem

def FactorizedUnitMembershipInput.toComparisonFactorRightTransportInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedUnitMembershipInput C) :
    ComparisonFactorRightTransportInput C where
  rightAdjoint := I.rightInput.rightAdjoint
  factorizedAdjunction := I.rightInput.factorizedAdjunction
  factorized_unit_mem := I.factorized_unit_mem

def FactorizedCounitMembershipInput.toComparisonFactorLeftTransportInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedCounitMembershipInput C) :
    ComparisonFactorLeftTransportInput C where
  leftAdjoint := I.leftInput.leftAdjoint
  factorizedAdjunction := I.leftInput.factorizedAdjunction
  factorized_counit_mem := I.factorized_counit_mem

def ComparisonFactorRightTransportInput.localizedAdjunction
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ComparisonFactorRightTransportInput C) :
    boundedHomotopyLocalizedComposite C ⊣ I.rightAdjoint :=
  I.transported.localizedAdjunction

theorem ComparisonFactorRightTransportInput.localized_unit_mem
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ComparisonFactorRightTransportInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.unit :=
  I.transported.localized_unit_mem

def ComparisonFactorLeftTransportInput.localizedAdjunction
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ComparisonFactorLeftTransportInput C) :
    I.leftAdjoint ⊣ boundedHomotopyLocalizedComposite C :=
  I.transported.localizedAdjunction

theorem ComparisonFactorLeftTransportInput.localized_counit_mem
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ComparisonFactorLeftTransportInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.counit :=
  I.transported.localized_counit_mem

def localized_right_transport_input_of_factorized_unit
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedUnitMembershipInput C) :
    ComparisonFactorRightTransportInput C :=
  I.toComparisonFactorRightTransportInput

theorem localized_unit_mem_of_factorized_unit
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedUnitMembershipInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C)
      (localized_right_transport_input_of_factorized_unit I).localizedAdjunction.unit :=
  (localized_right_transport_input_of_factorized_unit I).localized_unit_mem

def localized_left_transport_input_of_factorized_counit
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedCounitMembershipInput C) :
    ComparisonFactorLeftTransportInput C :=
  I.toComparisonFactorLeftTransportInput

theorem localized_counit_mem_of_factorized_counit
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedCounitMembershipInput C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C)
      (localized_left_transport_input_of_factorized_counit I).localizedAdjunction.counit :=
  (localized_left_transport_input_of_factorized_counit I).localized_counit_mem

end FactorizedRoute

structure FactorizedLocalizedAdjunctionApiMap : Type where
  route : String
  seedHash : String
  foundDeclarations : List String
  absentDeclarations : List String
  shortestNextTheoremStatement : String
  productSuccessClaimed : Bool

def currentFactorizedLocalizedAdjunctionApiMap :
    FactorizedLocalizedAdjunctionApiMap where
  route := "factorized-localized-adjunction-membership-w257"
  seedHash := "3eefdc248401042c02418bc35fa00bef008dee748221c4833826c6cdd8e17818"
  foundDeclarations :=
    ["boundedHomotopyExactWeakEquivalence",
      "BoundedHomotopyDerivedCategory.verdierComparison",
      "BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso",
      "Adjunction.ofNatIsoLeft",
      "Adjunction.ofNatIsoRight",
      "MorphismProperty.functorCategory",
      "MorphismProperty.RespectsIso.postcomp",
      "MorphismProperty.RespectsIso.precomp"]
  absentDeclarations :=
    ["factorizedLocalizedComposite right adjunction",
      "factorizedLocalizedComposite left adjunction",
      "factorizedLocalizedComposite unit membership in boundedHomotopyInverseImageClass",
      "factorizedLocalizedComposite counit membership in boundedHomotopyInverseImageClass"]
  shortestNextTheoremStatement :=
    "theorem factorizedLocalizedComposite_rightAdjunction_unit_mem (C) : FactorizedUnitMembershipInput C"
  productSuccessClaimed := false

theorem currentApiMap_found_count :
    currentFactorizedLocalizedAdjunctionApiMap.foundDeclarations.length = 8 := rfl

theorem currentApiMap_absent_count :
    currentFactorizedLocalizedAdjunctionApiMap.absentDeclarations.length = 4 := rfl

theorem currentApiMap_not_productSuccess :
    currentFactorizedLocalizedAdjunctionApiMap.productSuccessClaimed = false := rfl

def factorizedLocalizedAdjunctionFindings : List String :=
  ["the localized composite and factorized composite abbreviations compile",
    "verdierComparisonLocalizationIso transports factorized adjunction data to the localized composite",
    "the factorized right adjunction remains a named input",
    "the factorized left adjunction remains a named input",
    "unit membership for the factorized right adjunction remains a named input",
    "counit membership for the factorized left adjunction remains a named input",
    "the shortest next implementation target is FactorizedUnitMembershipInput C"]

theorem factorizedLocalizedAdjunctionFindings_count :
    factorizedLocalizedAdjunctionFindings.length = 7 := rfl

section Checks

#check FactorizedRightAdjunctionInput
#check FactorizedLeftAdjunctionInput
#check FactorizedUnitMembershipInput
#check FactorizedCounitMembershipInput
#check ComparisonFactorRightTransportInput.localizedAdjunction
#check ComparisonFactorRightTransportInput.localized_unit_mem
#check ComparisonFactorLeftTransportInput.localizedAdjunction
#check ComparisonFactorLeftTransportInput.localized_counit_mem
#check localized_right_transport_input_of_factorized_unit
#check localized_unit_mem_of_factorized_unit
#check localized_left_transport_input_of_factorized_counit
#check localized_counit_mem_of_factorized_counit
#check currentApiMap_not_productSuccess
#check factorizedLocalizedAdjunctionFindings_count

end Checks

end FactorizedLocalizedAdjunctionMembershipW257

end LeanLCAExactChallenge
