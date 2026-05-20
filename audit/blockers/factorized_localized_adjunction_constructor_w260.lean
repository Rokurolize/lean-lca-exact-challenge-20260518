import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Worker W260: factorized localized adjunction constructor boundary.

W257 isolated four missing comparison-factor inputs.  This file keeps the
Verdier comparison route factored, flattens the nested right/unit and
left/counit inputs to their shortest checked local shapes, and proves the
transport consumers from those flattened inputs.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂ v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace FactorizedLocalizedAdjunctionConstructorW260

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

structure GenericRightUnitBoundary
    (W : MorphismProperty C) [W.RespectsIso]
    {F F' : C ⥤ D} (e : F ≅ F') : Type (max u₁ u₂ v₁ v₂) where
  rightAdjoint : D ⥤ C
  factorizedAdjunction : F' ⊣ rightAdjoint
  factorized_unit_mem : W.functorCategory C factorizedAdjunction.unit

def GenericRightUnitBoundary.localizedAdjunction
    (W : MorphismProperty C) [W.RespectsIso]
    {F F' : C ⥤ D} {e : F ≅ F'}
    (I : GenericRightUnitBoundary W e) :
    F ⊣ I.rightAdjoint :=
  I.factorizedAdjunction.ofNatIsoLeft e.symm

theorem GenericRightUnitBoundary.localized_unit_mem
    (W : MorphismProperty C) [W.RespectsIso]
    {F F' : C ⥤ D} {e : F ≅ F'}
    (I : GenericRightUnitBoundary W e) :
    W.functorCategory C (I.localizedAdjunction W).unit := by
  change W.functorCategory C (I.factorizedAdjunction.ofNatIsoLeft e.symm).unit
  rw [show (I.factorizedAdjunction.ofNatIsoLeft e.symm).unit =
      I.factorizedAdjunction.unit ≫
        (Functor.isoWhiskerRight e.symm I.rightAdjoint).hom by
    simp [Adjunction.ofNatIsoLeft, Functor.isoWhiskerRight_hom]]
  exact functorCategory_postcomp_iso_mem W I.factorizedAdjunction.unit
    (Functor.isoWhiskerRight e.symm I.rightAdjoint) I.factorized_unit_mem

structure GenericLeftCounitBoundary
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ C} (e : F ≅ F') : Type (max u₁ u₂ v₁ v₂) where
  leftAdjoint : C ⥤ D
  factorizedAdjunction : leftAdjoint ⊣ F'
  factorized_counit_mem : W.functorCategory D factorizedAdjunction.counit

def GenericLeftCounitBoundary.localizedAdjunction
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ C} {e : F ≅ F'}
    (I : GenericLeftCounitBoundary W e) :
    I.leftAdjoint ⊣ F :=
  I.factorizedAdjunction.ofNatIsoRight e.symm

theorem GenericLeftCounitBoundary.localized_counit_mem
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ C} {e : F ≅ F'}
    (I : GenericLeftCounitBoundary W e) :
    W.functorCategory D (I.localizedAdjunction W).counit := by
  change W.functorCategory D (I.factorizedAdjunction.ofNatIsoRight e.symm).counit
  rw [show (I.factorizedAdjunction.ofNatIsoRight e.symm).counit =
      (Functor.isoWhiskerRight e.symm I.leftAdjoint).symm.hom ≫
        I.factorizedAdjunction.counit by
    simp [Adjunction.ofNatIsoRight, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_symm]]
  exact functorCategory_precomp_iso_mem W
    (Functor.isoWhiskerRight e.symm I.leftAdjoint).symm
    I.factorizedAdjunction.counit I.factorized_counit_mem

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

/--
Shortest checked right/unit boundary: the nested `FactorizedRightAdjunctionInput`
is only packaging.  A constructor for this structure is the first missing theorem
needed to produce W257's `FactorizedUnitMembershipInput C`.
-/
abbrev FactorizedRightUnitBoundary
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) :=
  GenericRightUnitBoundary (boundedHomotopyInverseImageClass C)
    (localizedComposite_factorizationIso C)

def FactorizedRightUnitBoundary.toFactorizedRightAdjunctionInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedRightUnitBoundary C) :
    FactorizedRightAdjunctionInput C where
  rightAdjoint := I.rightAdjoint
  factorizedAdjunction := I.factorizedAdjunction

def FactorizedRightUnitBoundary.toFactorizedUnitMembershipInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedRightUnitBoundary C) :
    FactorizedUnitMembershipInput C where
  rightInput := I.toFactorizedRightAdjunctionInput
  factorized_unit_mem := I.factorized_unit_mem

def FactorizedRightUnitBoundary.localizedAdjunction
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedRightUnitBoundary C) :
    boundedHomotopyLocalizedComposite C ⊣ I.rightAdjoint :=
  GenericRightUnitBoundary.localizedAdjunction
    (boundedHomotopyInverseImageClass C) I

theorem FactorizedRightUnitBoundary.localized_unit_mem
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedRightUnitBoundary C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.unit :=
  GenericRightUnitBoundary.localized_unit_mem
    (boundedHomotopyInverseImageClass C) I

/--
Shortest checked left/counit boundary: the nested `FactorizedLeftAdjunctionInput`
is only packaging.  A constructor for this structure is the first missing theorem
needed to produce W257's `FactorizedCounitMembershipInput C`.
-/
abbrev FactorizedLeftCounitBoundary
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) :=
  GenericLeftCounitBoundary (boundedHomotopyInverseImageClass C)
    (localizedComposite_factorizationIso C)

def FactorizedLeftCounitBoundary.toFactorizedLeftAdjunctionInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedLeftCounitBoundary C) :
    FactorizedLeftAdjunctionInput C where
  leftAdjoint := I.leftAdjoint
  factorizedAdjunction := I.factorizedAdjunction

def FactorizedLeftCounitBoundary.toFactorizedCounitMembershipInput
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedLeftCounitBoundary C) :
    FactorizedCounitMembershipInput C where
  leftInput := I.toFactorizedLeftAdjunctionInput
  factorized_counit_mem := I.factorized_counit_mem

def FactorizedLeftCounitBoundary.localizedAdjunction
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedLeftCounitBoundary C) :
    I.leftAdjoint ⊣ boundedHomotopyLocalizedComposite C :=
  GenericLeftCounitBoundary.localizedAdjunction
    (boundedHomotopyInverseImageClass C) I

theorem FactorizedLeftCounitBoundary.localized_counit_mem
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : FactorizedLeftCounitBoundary C) :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) I.localizedAdjunction.counit :=
  GenericLeftCounitBoundary.localized_counit_mem
    (boundedHomotopyInverseImageClass C) I

end FactorizedRoute

structure ConstructorSearchState : Type where
  route : String
  seedHash : String
  factorizationIsoFound : Bool
  rightUnitBoundaryChecked : Bool
  leftCounitBoundaryChecked : Bool
  concreteFactorizedRightAdjunctionConstructed : Bool
  concreteFactorizedLeftAdjunctionConstructed : Bool
  concreteFactorizedUnitMembershipConstructed : Bool
  concreteFactorizedCounitMembershipConstructed : Bool
  shortestRightUnitConstructorStatement : String
  shortestLeftCounitConstructorStatement : String
  productSuccessClaimed : Bool

def currentConstructorSearchState : ConstructorSearchState where
  route := "factorized-localized-adjunction-constructor-v276-w260"
  seedHash := "b6acc85eb644229fcca8388e84f3c5b575817f6c8c828005a454e7bb11799dc0"
  factorizationIsoFound := true
  rightUnitBoundaryChecked := true
  leftCounitBoundaryChecked := true
  concreteFactorizedRightAdjunctionConstructed := false
  concreteFactorizedLeftAdjunctionConstructed := false
  concreteFactorizedUnitMembershipConstructed := false
  concreteFactorizedCounitMembershipConstructed := false
  shortestRightUnitConstructorStatement :=
    "def factorizedRightUnitBoundary (C) : FactorizedRightUnitBoundary C"
  shortestLeftCounitConstructorStatement :=
    "def factorizedLeftCounitBoundary (C) : FactorizedLeftCounitBoundary C"
  productSuccessClaimed := false

theorem currentConstructorSearchState_checked_boundaries :
    currentConstructorSearchState.rightUnitBoundaryChecked = true ∧
      currentConstructorSearchState.leftCounitBoundaryChecked = true := by
  exact ⟨rfl, rfl⟩

theorem currentConstructorSearchState_no_concrete_constructors :
    currentConstructorSearchState.concreteFactorizedRightAdjunctionConstructed = false ∧
      currentConstructorSearchState.concreteFactorizedLeftAdjunctionConstructed = false ∧
      currentConstructorSearchState.concreteFactorizedUnitMembershipConstructed = false ∧
      currentConstructorSearchState.concreteFactorizedCounitMembershipConstructed = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem currentConstructorSearchState_not_productSuccess :
    currentConstructorSearchState.productSuccessClaimed = false := rfl

def constructorBoundaryFindings : List String :=
  ["the Verdier comparison factorization isomorphism is enough to transport a factorized adjunction once membership is supplied",
    "the shortest right/unit checked boundary is rightAdjoint plus factorizedAdjunction plus factorized_unit_mem",
    "that right/unit boundary constructs FactorizedUnitMembershipInput C and a localized unit-membership consumer",
    "the shortest left/counit checked boundary is leftAdjoint plus factorizedAdjunction plus factorized_counit_mem",
    "that left/counit boundary constructs FactorizedCounitMembershipInput C and a localized counit-membership consumer",
    "no concrete local declaration was found that supplies either flattened boundary"]

theorem constructorBoundaryFindings_count :
    constructorBoundaryFindings.length = 6 := rfl

section Checks

#check FactorizedRightAdjunctionInput
#check FactorizedLeftAdjunctionInput
#check FactorizedUnitMembershipInput
#check FactorizedCounitMembershipInput
#check FactorizedRightUnitBoundary
#check FactorizedRightUnitBoundary.toFactorizedUnitMembershipInput
#check FactorizedRightUnitBoundary.localizedAdjunction
#check FactorizedRightUnitBoundary.localized_unit_mem
#check FactorizedLeftCounitBoundary
#check FactorizedLeftCounitBoundary.toFactorizedCounitMembershipInput
#check FactorizedLeftCounitBoundary.localizedAdjunction
#check FactorizedLeftCounitBoundary.localized_counit_mem
#check currentConstructorSearchState_checked_boundaries
#check currentConstructorSearchState_no_concrete_constructors
#check currentConstructorSearchState_not_productSuccess
#check constructorBoundaryFindings_count

end Checks

end FactorizedLocalizedAdjunctionConstructorW260

end LeanLCAExactChallenge
