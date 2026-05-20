import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
W253 audit: W245-shaped localized comparison transport inputs.

This combines the generic adjunction transport pattern with the concrete
`BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso` isomorphism.
It does not construct the missing factorized adjunctions.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂ v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizedComparisonTransportInputW253

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

section W245Specialization

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

end W245Specialization

def localizedComparisonTransportInputFindings : List String :=
  ["generic right-adjunction transport packages localized unit membership",
    "generic left-adjunction transport packages localized counit membership",
    "the W245-shaped right input is factorized adjunction plus factorized unit membership",
    "the W245-shaped left input is factorized adjunction plus factorized counit membership",
    "the concrete factorized adjunctions and membership proofs are not constructed here"]

theorem localizedComparisonTransportInputFindings_count :
    localizedComparisonTransportInputFindings.length = 5 := rfl

section Checks

#check localizedComposite_factorizationIso
#check ComparisonFactorRightTransportInput
#check ComparisonFactorRightTransportInput.localizedAdjunction
#check ComparisonFactorRightTransportInput.localized_unit_mem
#check ComparisonFactorLeftTransportInput
#check ComparisonFactorLeftTransportInput.localizedAdjunction
#check ComparisonFactorLeftTransportInput.localized_counit_mem
#check localizedComparisonTransportInputFindings_count

end Checks

end LocalizedComparisonTransportInputW253

end LeanLCAExactChallenge
