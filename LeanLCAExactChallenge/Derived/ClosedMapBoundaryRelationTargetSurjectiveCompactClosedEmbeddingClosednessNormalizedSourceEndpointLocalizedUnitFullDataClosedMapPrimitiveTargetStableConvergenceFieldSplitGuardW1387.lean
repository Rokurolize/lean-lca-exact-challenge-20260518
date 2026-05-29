import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapRawPrimitiveStableConvergenceFieldSplitGuardW1386
import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactPrimitiveFieldRoute

/-!
W1387 records definitional convergence for the closed-map W921-W924 primitive
target route chain, through mapped-cokernel, selected-difference,
target-surjectivity, and target-compactness primitive field surfaces.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W921 concrete leaves delegate to W920 after mapped-cokernel primitive bundling. -/
theorem w921ConcreteLeavesRunThroughW920W1387
    (leaves : MetrizableWppClosedMapMappedCokernelPrimitiveFieldLeavesW921) :
    concreteLeavesOfClosedMapMappedCokernelPrimitiveFieldsW921 leaves =
      concreteLeavesOfClosedMapRelationPrimitiveFieldsW920
        (w920LeavesOfMappedCokernelPrimitiveFieldsW921 leaves) :=
  rfl

/-- W921 route data delegates to W920 after mapped-cokernel primitive bundling. -/
theorem w921RouteDataProviderRunsThroughW920W1387
    (leaves : MetrizableWppClosedMapMappedCokernelPrimitiveFieldLeavesW921) :
    routeDataProviderOfClosedMapMappedCokernelPrimitiveFieldsW921 leaves =
      routeDataProviderOfClosedMapRelationPrimitiveFieldsW920
        (w920LeavesOfMappedCokernelPrimitiveFieldsW921 leaves) :=
  rfl

/-- W921 direct calculus delegates to W920 after mapped-cokernel primitive bundling. -/
theorem w921DirectCalculusRunsThroughW920W1387
    (leaves : MetrizableWppClosedMapMappedCokernelPrimitiveFieldLeavesW921) :
    directBoundedLeftCalculusOfClosedMapMappedCokernelPrimitiveFieldsW921
        leaves =
      directBoundedLeftCalculusOfClosedMapRelationPrimitiveFieldsW920
        (w920LeavesOfMappedCokernelPrimitiveFieldsW921 leaves) :=
  rfl

/-- W921 stable package delegates to W920 after mapped-cokernel primitive bundling. -/
theorem w921StablePackageRunsThroughW920W1387
    (leaves : MetrizableWppClosedMapMappedCokernelPrimitiveFieldLeavesW921) :
    boundedDerivedInfinityCategoryOfClosedMapMappedCokernelPrimitiveFieldsW921
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapRelationPrimitiveFieldsW920
        (w920LeavesOfMappedCokernelPrimitiveFieldsW921 leaves) :=
  rfl

/-- W922 concrete leaves delegate to W921 after selected-difference primitive bundling. -/
theorem w922ConcreteLeavesRunThroughW921W1387
    (leaves : MetrizableWppClosedMapSelectedDifferencePrimitiveFieldLeavesW922) :
    concreteLeavesOfClosedMapSelectedDifferencePrimitiveFieldsW922 leaves =
      concreteLeavesOfClosedMapMappedCokernelPrimitiveFieldsW921
        (w921LeavesOfSelectedDifferencePrimitiveFieldsW922 leaves) :=
  rfl

/-- W922 route data delegates to W921 after selected-difference primitive bundling. -/
theorem w922RouteDataProviderRunsThroughW921W1387
    (leaves : MetrizableWppClosedMapSelectedDifferencePrimitiveFieldLeavesW922) :
    routeDataProviderOfClosedMapSelectedDifferencePrimitiveFieldsW922 leaves =
      routeDataProviderOfClosedMapMappedCokernelPrimitiveFieldsW921
        (w921LeavesOfSelectedDifferencePrimitiveFieldsW922 leaves) :=
  rfl

/-- W922 direct calculus delegates to W921 after selected-difference primitive bundling. -/
theorem w922DirectCalculusRunsThroughW921W1387
    (leaves : MetrizableWppClosedMapSelectedDifferencePrimitiveFieldLeavesW922) :
    directBoundedLeftCalculusOfClosedMapSelectedDifferencePrimitiveFieldsW922
        leaves =
      directBoundedLeftCalculusOfClosedMapMappedCokernelPrimitiveFieldsW921
        (w921LeavesOfSelectedDifferencePrimitiveFieldsW922 leaves) :=
  rfl

/-- W922 stable package delegates to W921 after selected-difference primitive bundling. -/
theorem w922StablePackageRunsThroughW921W1387
    (leaves : MetrizableWppClosedMapSelectedDifferencePrimitiveFieldLeavesW922) :
    boundedDerivedInfinityCategoryOfClosedMapSelectedDifferencePrimitiveFieldsW922
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapMappedCokernelPrimitiveFieldsW921
        (w921LeavesOfSelectedDifferencePrimitiveFieldsW922 leaves) :=
  rfl

/-- W923 concrete leaves delegate to W922 after target-surjectivity primitive bundling. -/
theorem w923ConcreteLeavesRunThroughW922W1387
    (leaves : MetrizableWppClosedMapTargetSurjectivePrimitiveFieldLeavesW923) :
    concreteLeavesOfClosedMapTargetSurjectivePrimitiveFieldsW923 leaves =
      concreteLeavesOfClosedMapSelectedDifferencePrimitiveFieldsW922
        (w922LeavesOfTargetSurjectivePrimitiveFieldsW923 leaves) :=
  rfl

/-- W923 route data delegates to W922 after target-surjectivity primitive bundling. -/
theorem w923RouteDataProviderRunsThroughW922W1387
    (leaves : MetrizableWppClosedMapTargetSurjectivePrimitiveFieldLeavesW923) :
    routeDataProviderOfClosedMapTargetSurjectivePrimitiveFieldsW923 leaves =
      routeDataProviderOfClosedMapSelectedDifferencePrimitiveFieldsW922
        (w922LeavesOfTargetSurjectivePrimitiveFieldsW923 leaves) :=
  rfl

/-- W923 direct calculus delegates to W922 after target-surjectivity primitive bundling. -/
theorem w923DirectCalculusRunsThroughW922W1387
    (leaves : MetrizableWppClosedMapTargetSurjectivePrimitiveFieldLeavesW923) :
    directBoundedLeftCalculusOfClosedMapTargetSurjectivePrimitiveFieldsW923
        leaves =
      directBoundedLeftCalculusOfClosedMapSelectedDifferencePrimitiveFieldsW922
        (w922LeavesOfTargetSurjectivePrimitiveFieldsW923 leaves) :=
  rfl

/-- W923 stable package delegates to W922 after target-surjectivity primitive bundling. -/
theorem w923StablePackageRunsThroughW922W1387
    (leaves : MetrizableWppClosedMapTargetSurjectivePrimitiveFieldLeavesW923) :
    boundedDerivedInfinityCategoryOfClosedMapTargetSurjectivePrimitiveFieldsW923
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapSelectedDifferencePrimitiveFieldsW922
        (w922LeavesOfTargetSurjectivePrimitiveFieldsW923 leaves) :=
  rfl

/-- W924 concrete leaves delegate to W923 after target-compactness primitive bundling. -/
theorem w924ConcreteLeavesRunThroughW923W1387
    (leaves : MetrizableWppClosedMapTargetCompactPrimitiveFieldLeavesW924) :
    concreteLeavesOfClosedMapTargetCompactPrimitiveFieldsW924 leaves =
      concreteLeavesOfClosedMapTargetSurjectivePrimitiveFieldsW923
        (w923LeavesOfTargetCompactPrimitiveFieldsW924 leaves) :=
  rfl

/-- W924 route data delegates to W923 after target-compactness primitive bundling. -/
theorem w924RouteDataProviderRunsThroughW923W1387
    (leaves : MetrizableWppClosedMapTargetCompactPrimitiveFieldLeavesW924) :
    routeDataProviderOfClosedMapTargetCompactPrimitiveFieldsW924 leaves =
      routeDataProviderOfClosedMapTargetSurjectivePrimitiveFieldsW923
        (w923LeavesOfTargetCompactPrimitiveFieldsW924 leaves) :=
  rfl

/-- W924 direct calculus delegates to W923 after target-compactness primitive bundling. -/
theorem w924DirectCalculusRunsThroughW923W1387
    (leaves : MetrizableWppClosedMapTargetCompactPrimitiveFieldLeavesW924) :
    directBoundedLeftCalculusOfClosedMapTargetCompactPrimitiveFieldsW924
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetSurjectivePrimitiveFieldsW923
        (w923LeavesOfTargetCompactPrimitiveFieldsW924 leaves) :=
  rfl

/-- W924 stable package delegates to W923 after target-compactness primitive bundling. -/
theorem w924StablePackageRunsThroughW923W1387
    (leaves : MetrizableWppClosedMapTargetCompactPrimitiveFieldLeavesW924) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactPrimitiveFieldsW924
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetSurjectivePrimitiveFieldsW923
        (w923LeavesOfTargetCompactPrimitiveFieldsW924 leaves) :=
  rfl

/-- W1387 keeps W921-W924 input counts visible. -/
theorem w1387ClosedMapW921ToW924InputCounts :
    closedMapMappedCokernelPrimitiveFieldsInputNamesW921.length = 39 ∧
      closedMapSelectedDifferencePrimitiveFieldsInputNamesW922.length = 39 ∧
      closedMapTargetSurjectivePrimitiveFieldsInputNamesW923.length = 39 ∧
      closedMapTargetCompactPrimitiveFieldsInputNamesW924.length = 39 :=
  ⟨closedMapMappedCokernelPrimitiveFieldsInputNamesW921_count,
    closedMapSelectedDifferencePrimitiveFieldsInputNamesW922_count,
    closedMapTargetSurjectivePrimitiveFieldsInputNamesW923_count,
    closedMapTargetCompactPrimitiveFieldsInputNamesW924_count⟩

/-- Current W1387 nonterminal state. -/
structure ClosedMapPrimitiveTargetStableConvergenceStateW1387 :
    Type where
  seed : String
  declarations : List String
  mappedCokernelPrimitiveResult : String
  selectedDifferencePrimitiveResult : String
  targetSurjectivePrimitiveResult : String
  targetCompactPrimitiveResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1387 records W921-W924 convergence into the closed-map stable route. -/
def currentClosedMapPrimitiveTargetStableConvergenceStateW1387 :
    ClosedMapPrimitiveTargetStableConvergenceStateW1387 where
  seed := "w1387-closed-map-primitive-target-stable-convergence"
  declarations :=
    ["w921ConcreteLeavesRunThroughW920W1387",
      "w921RouteDataProviderRunsThroughW920W1387",
      "w921DirectCalculusRunsThroughW920W1387",
      "w921StablePackageRunsThroughW920W1387",
      "w922ConcreteLeavesRunThroughW921W1387",
      "w922RouteDataProviderRunsThroughW921W1387",
      "w922DirectCalculusRunsThroughW921W1387",
      "w922StablePackageRunsThroughW921W1387",
      "w923ConcreteLeavesRunThroughW922W1387",
      "w923RouteDataProviderRunsThroughW922W1387",
      "w923DirectCalculusRunsThroughW922W1387",
      "w923StablePackageRunsThroughW922W1387",
      "w924ConcreteLeavesRunThroughW923W1387",
      "w924RouteDataProviderRunsThroughW923W1387",
      "w924DirectCalculusRunsThroughW923W1387",
      "w924StablePackageRunsThroughW923W1387",
      "w1387ClosedMapW921ToW924InputCounts"]
  mappedCokernelPrimitiveResult :=
    "proved: W921 mapped-cokernel primitive field delegates into W920"
  selectedDifferencePrimitiveResult :=
    "proved: W922 selected-difference primitive fields delegate into W921"
  targetSurjectivePrimitiveResult :=
    "proved: W923 target-surjectivity primitive field delegates into W922"
  targetCompactPrimitiveResult :=
    "proved: W924 target-compactness primitive field delegates into W923"
  remainingInputs :=
    closedMapTargetCompactPrimitiveFieldsInputNamesW924
  productSuccessClaimed := false

theorem currentW1387ClosedMapPrimitiveTargetStableConvergence_productSuccess :
    currentClosedMapPrimitiveTargetStableConvergenceStateW1387.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
