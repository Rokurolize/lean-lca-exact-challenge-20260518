import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Worker W245: localized comparison-factor adjunction probe.

W240 identified the bounded homotopy/Verdier composite

`BoundedComplexCategory.homotopyQuotient C ⋙ ((exactAcyclicHomotopyIsoClosure C).trW).Q`

as the functor whose adjunction data would feed mathlib's
`Adjunction.hasLeftCalculusOfFractions` and `Adjunction.hasRightCalculusOfFractions`.
The available local comparison instead gives a factorization through
`(boundedHomotopyExactWeakEquivalence C).Q` and
`BoundedHomotopyDerivedCategory.verdierComparison C`.

This file narrows the obstruction: if an adjunction for the comparison-factor route is
already transported back to the localized composite, the W240 calculus conclusions follow
immediately. The comparison isomorphism alone remains too small: it supplies a commuting
functor isomorphism, not the transported `Adjunction`, nor the required unit/counit
membership in `MorphismProperty.functorCategory`.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizedComparisonFactorAdjunctionW245

/-- The localized composite targeted by the W233/W238/W240 adjunction route. -/
abbrev boundedHomotopyLocalizedComposite
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

/-- The inverse-image weak equivalences on bounded complexes. -/
abbrev boundedHomotopyInverseImageClass
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  ((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
    (BoundedComplexCategory.homotopyQuotient C)

/-- The localized composite inverts the inverse-image class. -/
theorem inverseImage_isInvertedBy_localizedComposite
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

/-- The comparison-factorized route exposed by the local Verdier comparison API. -/
abbrev factorizedLocalizedComposite
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  (boundedHomotopyExactWeakEquivalence C).Q ⋙
    BoundedHomotopyDerivedCategory.verdierComparison C

/-- The available comparison isomorphism: useful factorization, but not an adjunction. -/
def localizedComposite_factorizationIso
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedHomotopyLocalizedComposite C ≅ factorizedLocalizedComposite C :=
  BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso C

/--
Right-adjoint comparison-factor input. The `factorizedAdjunction` field records the smaller
universal property one might hope to get from the factorization. The extra
`localizedAdjunction` field is deliberately explicit: this is the transport back across
`localizedComposite_factorizationIso` that the current local declarations do not provide as a
ready-to-use bounded homotopy/Verdier input.
-/
structure ComparisonFactorRightAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    factorizedLocalizedComposite C ⊣ rightAdjoint
  localizedAdjunction :
    boundedHomotopyLocalizedComposite C ⊣ rightAdjoint
  unit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) localizedAdjunction.unit

/--
Left-adjoint comparison-factor input. As above, the factorized adjunction is not enough
without the transported localized adjunction and the counit membership proof.
-/
structure ComparisonFactorLeftAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftAdjoint :
    ExactAcyclicHomotopyVerdierCategory C ⥤ BoundedComplexCategory C
  factorizedAdjunction :
    leftAdjoint ⊣ factorizedLocalizedComposite C
  localizedAdjunction :
    leftAdjoint ⊣ boundedHomotopyLocalizedComposite C
  counit_mem :
    (boundedHomotopyInverseImageClass C).functorCategory
      (BoundedComplexCategory C) localizedAdjunction.counit

/--
A comparison-factor right adjunction gives W240's left-calculus conclusion exactly when it
also carries the transported localized adjunction and unit-membership input.
-/
theorem boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_comparisonFactorRight
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : ComparisonFactorRightAdjunctionInput C) :
    (boundedHomotopyInverseImageClass C).HasLeftCalculusOfFractions :=
  CategoryTheory.Adjunction.hasLeftCalculusOfFractions I.localizedAdjunction
    (boundedHomotopyInverseImageClass C)
    (inverseImage_isInvertedBy_localizedComposite
      (BoundedComplexCategory.homotopyQuotient C)
      ((exactAcyclicHomotopyIsoClosure C).trW))
    I.unit_mem

/--
A comparison-factor left adjunction gives W240/W250's right-calculus conclusion exactly when
it also carries the transported localized adjunction and counit-membership input.
-/
theorem boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_comparisonFactorLeft
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : ComparisonFactorLeftAdjunctionInput C) :
    (boundedHomotopyInverseImageClass C).HasRightCalculusOfFractions :=
  CategoryTheory.Adjunction.hasRightCalculusOfFractions I.localizedAdjunction
    (boundedHomotopyInverseImageClass C)
    (inverseImage_isInvertedBy_localizedComposite
      (BoundedComplexCategory.homotopyQuotient C)
      ((exactAcyclicHomotopyIsoClosure C).trW))
    I.counit_mem

/-- Since the target is definitionally this inverse image, the right input gives left calculus. -/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_comparisonFactorRight
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : ComparisonFactorRightAdjunctionInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_comparisonFactorRight C I

/-- Since the target is definitionally this inverse image, the left input gives right calculus. -/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_comparisonFactorLeft
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : ComparisonFactorLeftAdjunctionInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_comparisonFactorLeft C I

/-- Reproducible obstruction state for this comparison-factor probe. -/
structure LocalizedComparisonFactorAdjunctionState : Type where
  route : String
  seedHash : String
  factorizationIsoFound : Bool
  factorizedRightAdjunctionFound : Bool
  factorizedLeftAdjunctionFound : Bool
  transportedLocalizedAdjunctionFound : Bool
  unitMembershipFound : Bool
  counitMembershipFound : Bool
  functorCategoryDeclarationAvailable : Bool
  productSuccessClaimed : Bool

/-- Current W245 findings encoded as checked data. -/
def currentComparisonFactorAdjunctionState : LocalizedComparisonFactorAdjunctionState where
  route := "localized-comparison-factor-adjunction-v252"
  seedHash := "4c7630f249e680efabad83fa72caf22ccd64819b74354b0c27474a31e50e0dcb"
  factorizationIsoFound := true
  factorizedRightAdjunctionFound := false
  factorizedLeftAdjunctionFound := false
  transportedLocalizedAdjunctionFound := false
  unitMembershipFound := false
  counitMembershipFound := false
  functorCategoryDeclarationAvailable := true
  productSuccessClaimed := false

theorem currentComparisonFactorAdjunctionState_has_factorizationIso :
    currentComparisonFactorAdjunctionState.factorizationIsoFound = true := rfl

theorem currentComparisonFactorAdjunctionState_no_factorized_adjunction :
    currentComparisonFactorAdjunctionState.factorizedRightAdjunctionFound = false ∧
      currentComparisonFactorAdjunctionState.factorizedLeftAdjunctionFound = false := by
  exact ⟨rfl, rfl⟩

theorem currentComparisonFactorAdjunctionState_no_transport_or_membership :
    currentComparisonFactorAdjunctionState.transportedLocalizedAdjunctionFound = false ∧
      currentComparisonFactorAdjunctionState.unitMembershipFound = false ∧
      currentComparisonFactorAdjunctionState.counitMembershipFound = false := by
  exact ⟨rfl, rfl, rfl⟩

theorem currentComparisonFactorAdjunctionState_has_functorCategory_declaration :
    currentComparisonFactorAdjunctionState.functorCategoryDeclarationAvailable = true := rfl

theorem currentComparisonFactorAdjunctionState_not_productSuccess :
    currentComparisonFactorAdjunctionState.productSuccessClaimed = false := rfl

/-- Search findings as checked data rather than prose-only notes. -/
def localizedComparisonFactorAdjunctionFindings : List String :=
  ["BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso factors the searched localized composite through boundedHomotopyExactWeakEquivalence C",
    "a right adjunction for the transported comparison-factor route plus unit_mem yields HasLeftCalculusOfFractions for boundedHomotopyExactWeakEquivalence C",
    "a left adjunction for the transported comparison-factor route plus counit_mem yields HasRightCalculusOfFractions for boundedHomotopyExactWeakEquivalence C",
    "the local factorization isomorphism is not itself an Adjunction",
    "no local declaration was found that packages the transported localized Adjunction from the comparison factorization",
    "MorphismProperty.functorCategory is available, but no local declaration proves the needed unit or counit membership"]

theorem localizedComparisonFactorAdjunctionFindings_count :
    localizedComparisonFactorAdjunctionFindings.length = 6 := rfl

section Checks

#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions
#check CategoryTheory.Adjunction.hasRightCalculusOfFractions
#check Localization.inverts
#check MorphismProperty.functorCategory
#check BoundedComplexCategory.homotopyQuotient
#check boundedHomotopyExactWeakEquivalence
#check BoundedHomotopyDerivedCategory.verdierComparison
#check BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso
#check boundedHomotopyLocalizedComposite
#check boundedHomotopyInverseImageClass
#check inverseImage_isInvertedBy_localizedComposite
#check factorizedLocalizedComposite
#check localizedComposite_factorizationIso
#check ComparisonFactorRightAdjunctionInput
#check ComparisonFactorLeftAdjunctionInput
#check boundedHomotopyInverseImage_hasLeftCalculusOfFractions_of_comparisonFactorRight
#check boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_comparisonFactorLeft
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_comparisonFactorRight
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_comparisonFactorLeft
#check currentComparisonFactorAdjunctionState
#check currentComparisonFactorAdjunctionState_has_factorizationIso
#check currentComparisonFactorAdjunctionState_no_factorized_adjunction
#check currentComparisonFactorAdjunctionState_no_transport_or_membership
#check currentComparisonFactorAdjunctionState_has_functorCategory_declaration
#check currentComparisonFactorAdjunctionState_not_productSuccess
#check localizedComparisonFactorAdjunctionFindings
#check localizedComparisonFactorAdjunctionFindings_count

end Checks

end LocalizedComparisonFactorAdjunctionW245

end LeanLCAExactChallenge
