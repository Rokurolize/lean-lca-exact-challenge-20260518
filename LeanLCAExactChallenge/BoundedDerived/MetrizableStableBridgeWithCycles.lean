import LeanLCAExactChallenge.Derived.BoundedDerivedWithCycles
import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesHomotopy

/-!
# Corrected metrizable stable bridge for cycle-object acyclicity

This module gives the corrected `DboundedWithCycles` route its own stable package surface.
The fields are typed against `DboundedWithCycles MetrizableLCA` and the weak equivalences
are `boundedExactWeakEquivalenceWithCycles`.

The file intentionally keeps the remaining stable facts as explicit assumptions. It does
not use the legacy `Dbounded` semantic package as evidence for the corrected route.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace BoundedDerivedWithCycles
namespace Metrizable

/-- Bounded cochain complexes over default-universe metrizable LCA groups. -/
abbrev ComplexCategory : Type 1 :=
  BoundedComplexCategory MetrizableLCA.{0}

/-- The corrected ordinary bounded derived category for default-universe `MetrizableLCA`. -/
abbrev OrdinaryCategory : Type 1 :=
  DboundedWithCycles MetrizableLCA.{0}

/-- Corrected bounded weak equivalences for default-universe `MetrizableLCA`. -/
abbrev WeakEquivalence : MorphismProperty ComplexCategory :=
  boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}

/-- The corrected localization functor for default-universe `MetrizableLCA`. -/
abbrev localization : ComplexCategory ⥤ OrdinaryCategory :=
  DboundedWithCycles.localization MetrizableLCA.{0}

/-- The ordinary quasicategory nerve attached to the corrected metrizable localization. -/
abbrev infinityCategory : SSet.QCat :=
  BoundedDerivedOrdinaryQuasicategoryWithCycles MetrizableLCA.{0}

/-- Corrected weak equivalences are exactly the cycle-object acyclic mapping-cone maps. -/
theorem weakEquivalence_iff_exactAcyclicWithCyclesMappingCone
    {K L : ComplexCategory} (f : K ⟶ L) :
    WeakEquivalence f ↔
      exactAcyclicWithCycles MetrizableLCA
        (CochainComplex.mappingCone ((BoundedComplexCategory.ι MetrizableLCA).map f)) :=
  Iff.rfl

/--
Product-facing stable bounded-derived data for the corrected metrizable route.

The carrier and weak-equivalence class are recorded as fields so the package cannot be
mistaken for the legacy localization surface.
-/
structure StablePackage : Type 2 where
  quasicategoryCarrier :
    infinityCategory = BoundedDerivedOrdinaryQuasicategoryWithCycles MetrizableLCA.{0}
  weakEquivalenceClass :
    WeakEquivalence = boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}
  preadditive : Preadditive OrdinaryCategory
  finiteProductInstance : HasFiniteProducts OrdinaryCategory
  finiteBiproductInstance : HasFiniteBiproducts OrdinaryCategory
  finiteCoproductInstance : HasFiniteCoproducts OrdinaryCategory
  finiteLimitInstance : HasFiniteLimits OrdinaryCategory
  finiteColimitInstance : HasFiniteColimits OrdinaryCategory
  zeroObjectInstance : HasZeroObject OrdinaryCategory
  shiftAdditiveAll :
    letI : Preadditive OrdinaryCategory := preadditive
    ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive
  suspensionAdditive :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    (shiftFunctor OrdinaryCategory (1 : ℤ)).Additive
  pretriangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulatedStructure
    IsTriangulated OrdinaryCategory

/-- The explicit source-facing left-calculus assumption for the corrected weak equivalences. -/
structure LeftCalculusAssumption : Type 1 where
  leftCalculus : WeakEquivalence.HasLeftCalculusOfFractions

/-- The explicit source-facing right-calculus assumption for the corrected weak equivalences. -/
structure RightCalculusAssumption : Type 1 where
  rightCalculus : WeakEquivalence.HasRightCalculusOfFractions

/-- Build corrected left calculus from the homotopy Verdier route inputs. -/
def leftCalculusAssumptionOfHomotopyVerdier
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}) :
    LeftCalculusAssumption where
  leftCalculus :=
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint
      MetrizableLCA.{0} descent adjoint

/-- Build corrected right calculus from the homotopy Verdier route inputs. -/
def rightCalculusAssumptionOfHomotopyVerdier
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedLeftAdjointInput MetrizableLCA.{0}) :
    RightCalculusAssumption where
  rightCalculus :=
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint
      MetrizableLCA.{0} descent adjoint

/-- Build corrected preadditivity from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev preadditiveOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    Preadditive OrdinaryCategory :=
  DboundedWithCycles.preadditiveOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build a corrected zero object from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasZeroObjectOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasZeroObject OrdinaryCategory :=
  DboundedWithCycles.hasZeroObjectOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build corrected finite products from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteProductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteProducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteProductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build corrected finite coproducts from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteCoproductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteCoproducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteCoproductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0}
    input

/-- Build corrected finite biproducts from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteBiproductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    HasFiniteBiproducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteBiproductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0}
    input

/-- Build corrected shift additivity from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev shiftFunctorAdditiveOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0})
    (n : ℤ) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    (shiftFunctor OrdinaryCategory n).Additive :=
  DboundedWithCycles.shiftFunctor_additiveOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input n

/-- Build corrected pretriangulation from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev pretriangulatedOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    letI : HasZeroObject OrdinaryCategory :=
      hasZeroObjectOfBoundedVerdierLocalizationInput input
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      shiftFunctorAdditiveOfBoundedVerdierLocalizationInput input
    Pretriangulated OrdinaryCategory :=
  DboundedWithCycles.pretriangulatedOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input

/-- Build corrected triangulation from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev isTriangulatedOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    letI : HasZeroObject OrdinaryCategory :=
      hasZeroObjectOfBoundedVerdierLocalizationInput input
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      shiftFunctorAdditiveOfBoundedVerdierLocalizationInput input
    letI : Pretriangulated OrdinaryCategory :=
      pretriangulatedOfBoundedVerdierLocalizationInput input
    IsTriangulated OrdinaryCategory :=
  DboundedWithCycles.isTriangulatedOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input

/-- Semantic fields supplied by corrected left calculus and corrected finite-product closure. -/
structure LeftCalculusSemanticFields : Type 1 where
  leftCalculus : WeakEquivalence.HasLeftCalculusOfFractions
  preadditive : Preadditive OrdinaryCategory
  zeroObject : HasZeroObject OrdinaryCategory
  finiteProducts : HasFiniteProducts OrdinaryCategory
  finiteBiproducts : HasFiniteBiproducts OrdinaryCategory
  finiteCoproducts : HasFiniteCoproducts OrdinaryCategory
  shiftAdditiveAll :
    letI : Preadditive OrdinaryCategory := preadditive
    ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive
  suspensionAdditive :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    (shiftFunctor OrdinaryCategory (1 : ℤ)).Additive

/-- Build the corrected semantic fields that are available from left calculus. -/
def leftCalculusSemanticFields
    (assumption : LeftCalculusAssumption) : LeftCalculusSemanticFields where
  leftCalculus := assumption.leftCalculus
  preadditive := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  zeroObject := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasZeroObject
  finiteProducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteProducts
  finiteBiproducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteBiproducts
  finiteCoproducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteCoproducts
  shiftAdditiveAll := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    intro n
    exact DboundedWithCycles.shiftFunctor_additiveOfHasLeftCalculusOfFractions
      MetrizableLCA.{0} n
  suspensionAdditive := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.shiftFunctor_additiveOfHasLeftCalculusOfFractions
      MetrizableLCA.{0} 1

/-- Remaining stable fields for the corrected metrizable route after left calculus. -/
structure RemainingStableSemanticFields (available : LeftCalculusSemanticFields) :
    Type 1 where
  equalizers : HasEqualizers OrdinaryCategory
  coequalizers : HasCoequalizers OrdinaryCategory
  pretriangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulated
    IsTriangulated OrdinaryCategory

/-- Full corrected stable semantic input, split into derived and still-assumed fields. -/
structure StableSemanticInput : Type 1 where
  available : LeftCalculusSemanticFields
  remaining : RemainingStableSemanticFields available

/-- Assemble the full corrected stable semantic input from an explicit left-calculus field. -/
def stableSemanticInputOfLeftCalculus
    (assumption : LeftCalculusAssumption)
    (remaining : RemainingStableSemanticFields (leftCalculusSemanticFields assumption)) :
    StableSemanticInput where
  available := leftCalculusSemanticFields assumption
  remaining := remaining

/-- Transfer data that supplies the finite-shape part of the remaining corrected fields. -/
structure WalkingParallelPairTransferStableSemanticInputs
    (available : LeftCalculusSemanticFields) : Type 1 where
  transferInputs :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs
  pretriangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulated
    IsTriangulated OrdinaryCategory

/-- WPP finite-shape transfer supplies equalizers and coequalizers for the remaining fields. -/
def remainingStableSemanticFieldsOfWalkingParallelPairTransfer
    {available : LeftCalculusSemanticFields}
    (inputs : WalkingParallelPairTransferStableSemanticInputs available) :
    RemainingStableSemanticFields available where
  equalizers :=
    DboundedWithCycles.MetrizableLCA.hasEqualizersOfWalkingParallelPairTransfer
      inputs.transferInputs
  coequalizers :=
    DboundedWithCycles.MetrizableLCA.hasCoequalizersOfWalkingParallelPairTransfer
      inputs.transferInputs
  pretriangulated := inputs.pretriangulated
  triangulated := inputs.triangulated

/-- Build the corrected stable package from its checked semantic input surface. -/
def stablePackageOfSemanticInput (input : StableSemanticInput) : StablePackage where
  quasicategoryCarrier := rfl
  weakEquivalenceClass := rfl
  preadditive := input.available.preadditive
  finiteProductInstance := input.available.finiteProducts
  finiteBiproductInstance := input.available.finiteBiproducts
  finiteCoproductInstance := input.available.finiteCoproducts
  finiteLimitInstance := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := input.available.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfEqualizers
      input.remaining.equalizers
  finiteColimitInstance := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := input.available.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfCoequalizers
      input.remaining.coequalizers
  zeroObjectInstance := input.available.zeroObject
  shiftAdditiveAll := input.available.shiftAdditiveAll
  suspensionAdditive := input.available.suspensionAdditive
  pretriangulatedStructure := input.remaining.pretriangulated
  triangulatedStructure := input.remaining.triangulated

/-- Build the corrected stable package directly from left calculus plus remaining fields. -/
def stablePackageOfLeftCalculus
    (assumption : LeftCalculusAssumption)
    (remaining : RemainingStableSemanticFields (leftCalculusSemanticFields assumption)) :
    StablePackage :=
  stablePackageOfSemanticInput (stableSemanticInputOfLeftCalculus assumption remaining)

/-- Assemble the corrected stable input from the homotopy Verdier left-calculus route and WPP
finite-shape transfer. -/
def stableSemanticInputOfHomotopyVerdierWalkingParallelPairTransfer
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs : WalkingParallelPairTransferStableSemanticInputs
      (leftCalculusSemanticFields
        (leftCalculusAssumptionOfHomotopyVerdier descent adjoint))) :
    StableSemanticInput :=
  stableSemanticInputOfLeftCalculus (leftCalculusAssumptionOfHomotopyVerdier descent adjoint)
    (remainingStableSemanticFieldsOfWalkingParallelPairTransfer inputs)

/-- Build the corrected stable package from the homotopy Verdier left-calculus route and WPP
finite-shape transfer. -/
def stablePackageOfHomotopyVerdierWalkingParallelPairTransfer
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs : WalkingParallelPairTransferStableSemanticInputs
      (leftCalculusSemanticFields
        (leftCalculusAssumptionOfHomotopyVerdier descent adjoint))) :
    StablePackage :=
  stablePackageOfSemanticInput
    (stableSemanticInputOfHomotopyVerdierWalkingParallelPairTransfer descent adjoint inputs)

/-- Build the corrected stable package from the homotopy Verdier left-calculus route, WPP
finite-shape transfer, and bounded Verdier localized-equivalence input. -/
def stablePackageOfHomotopyVerdierWalkingParallelPairBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (transferInputs :
      DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs)
    (boundedInput :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    StablePackage where
  quasicategoryCarrier := rfl
  weakEquivalenceClass := rfl
  preadditive := preadditiveOfBoundedVerdierLocalizationInput boundedInput
  finiteProductInstance := hasFiniteProductsOfBoundedVerdierLocalizationInput boundedInput
  finiteBiproductInstance := hasFiniteBiproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteCoproductInstance := hasFiniteCoproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteLimitInstance := by
    let left := leftCalculusAssumptionOfHomotopyVerdier descent adjoint
    letI : WeakEquivalence.HasLeftCalculusOfFractions := left.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfWalkingParallelPairTransfer
      transferInputs
  finiteColimitInstance := by
    let left := leftCalculusAssumptionOfHomotopyVerdier descent adjoint
    letI : WeakEquivalence.HasLeftCalculusOfFractions := left.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfWalkingParallelPairTransfer
      transferInputs
  zeroObjectInstance := hasZeroObjectOfBoundedVerdierLocalizationInput boundedInput
  shiftAdditiveAll := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput
  suspensionAdditive := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput 1
  pretriangulatedStructure := pretriangulatedOfBoundedVerdierLocalizationInput boundedInput
  triangulatedStructure := isTriangulatedOfBoundedVerdierLocalizationInput boundedInput

/-- Route-specific inputs that remain before the corrected stable package is fully inhabited. -/
structure RouteSpecificInputs : Type 1 where
  boundedHomotopyClosed2 :
    (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂
  homotopyIsoClosureRealization :
    exactAcyclicWithCyclesHomotopyIsoClosureTrianglehIso13Realization MetrizableLCA.{0}
  descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0}
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized
  boundedHomotopyVerdierLocalization :
    letI : (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
      boundedHomotopyClosed2
    BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput
      MetrizableLCA.{0}

/-- Build the corrected stable package from the bundled route-specific inputs. -/
def stablePackageOfRouteSpecificInputs (inputs : RouteSpecificInputs) : StablePackage := by
  letI : (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    inputs.boundedHomotopyClosed2
  letI : (exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
      MetrizableLCA.{0} inputs.homotopyIsoClosureRealization
  let boundedInput :=
    BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy
      MetrizableLCA.{0} inputs.descent inputs.boundedHomotopyVerdierLocalization
  let transferInputs :=
    DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_normalized
      inputs.walkingParallelPairTransfer
  exact stablePackageOfHomotopyVerdierWalkingParallelPairBoundedVerdierLocalizationInput
    inputs.descent inputs.localizedRightAdjoint transferInputs boundedInput

/-- Names of route-specific inputs still to discharge for a fully inhabited corrected package. -/
def routeSpecificInputNames : List String :=
  ["(boundedHomotopyObject MetrizableLCA).IsTriangulatedClosed₂",
    "exactAcyclicWithCyclesHomotopyIsoClosureTrianglehIso13Realization MetrizableLCA",
    "ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA",
    "BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA",
    "DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized",
    "BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA"]

/-- Six route-specific inputs remain before the corrected package is fully inhabited. -/
theorem routeSpecificInputNames_count :
    routeSpecificInputNames.length = 6 :=
  rfl

/-- The corrected stable package carrier is the corrected ordinary quasicategory nerve. -/
theorem stablePackage_carrier (P : StablePackage) :
    P.quasicategoryCarrier = rfl :=
  rfl

/-- The corrected stable package records the corrected weak-equivalence class. -/
theorem stablePackage_weakEquivalenceClass (P : StablePackage) :
    P.weakEquivalenceClass = rfl :=
  rfl

/-- Names of semantic fields derived from corrected left calculus in this bridge. -/
def leftCalculusSemanticFieldNames : List String :=
  ["(boundedExactWeakEquivalenceWithCycles MetrizableLCA).HasLeftCalculusOfFractions",
    "Preadditive (DboundedWithCycles MetrizableLCA)",
    "HasZeroObject (DboundedWithCycles MetrizableLCA)",
    "HasFiniteProducts (DboundedWithCycles MetrizableLCA)",
    "HasFiniteBiproducts (DboundedWithCycles MetrizableLCA)",
    "HasFiniteCoproducts (DboundedWithCycles MetrizableLCA)",
    "forall n, (shiftFunctor (DboundedWithCycles MetrizableLCA) n).Additive",
    "(shiftFunctor (DboundedWithCycles MetrizableLCA) 1).Additive"]

/-- Corrected left calculus currently supplies eight named semantic fields. -/
theorem leftCalculusSemanticFieldNames_count :
    leftCalculusSemanticFieldNames.length = 8 :=
  rfl

/-- Remaining stable assumptions for the corrected route after the fields above. -/
def remainingStableSemanticFieldNames : List String :=
  ["HasEqualizers (DboundedWithCycles MetrizableLCA)",
    "HasCoequalizers (DboundedWithCycles MetrizableLCA)",
    "Pretriangulated (DboundedWithCycles MetrizableLCA)",
    "IsTriangulated (DboundedWithCycles MetrizableLCA)"]

/-- Four stable semantic fields remain explicit in this checked corrected bridge. -/
theorem remainingStableSemanticFieldNames_count :
    remainingStableSemanticFieldNames.length = 4 :=
  rfl

/-- Current corrected bridge state: the assumption surface is checked, not inhabited. -/
def currentMetrizableStableBridgeWithCyclesProductSuccessClaimed : Bool :=
  false

/-- The corrected bridge does not claim product success without the remaining inputs. -/
theorem currentMetrizableStableBridgeWithCycles_productSuccess :
    currentMetrizableStableBridgeWithCyclesProductSuccessClaimed = false :=
  rfl

end Metrizable
end BoundedDerivedWithCycles

end LeanLCAExactChallenge
