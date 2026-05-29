import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapTargetNoUnivLocalizedUnitStableConvergenceFieldSplitGuardW1393
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1394 records definitional convergence for the W946-W949 boundary/relation,
target-closedness, normalized-source-triangulation, and endpoint-localized-unit
data chain.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W946 concrete leaves delegate to W945 after boundary/relation data bundling. -/
theorem w946ConcreteLeavesRunThroughW945W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves =
      concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
        (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
          leaves) :=
  rfl

/-- W946 route data delegates to W945 after boundary/relation data bundling. -/
theorem w946RouteDataProviderRunsThroughW945W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves =
      routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
        (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
          leaves) :=
  rfl

/-- W946 direct calculus delegates to W945 after boundary/relation data bundling. -/
theorem w946DirectCalculusRunsThroughW945W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
        (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
          leaves) :=
  rfl

/-- W946 stable package delegates to W945 after boundary/relation data bundling. -/
theorem w946StablePackageRunsThroughW945W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
        (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
          leaves) :=
  rfl

/-- W947 concrete leaves delegate to W946 after target-no-univ/closedness bundling. -/
theorem w947ConcreteLeavesRunThroughW946W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves =
      concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
          leaves) :=
  rfl

/-- W947 route data delegates to W946 after target-no-univ/closedness bundling. -/
theorem w947RouteDataProviderRunsThroughW946W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves =
      routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
          leaves) :=
  rfl

/-- W947 direct calculus delegates to W946 after target-no-univ/closedness bundling. -/
theorem w947DirectCalculusRunsThroughW946W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves =
      directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
          leaves) :=
  rfl

/-- W947 stable package delegates to W946 after target-no-univ/closedness bundling. -/
theorem w947StablePackageRunsThroughW946W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
          leaves) :=
  rfl

/-- W948 concrete leaves delegate to W947 after normalized-source-triangulation bundling. -/
theorem w948ConcreteLeavesRunThroughW947W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves =
      concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
          leaves) :=
  rfl

/-- W948 route data delegates to W947 after normalized-source-triangulation bundling. -/
theorem w948RouteDataProviderRunsThroughW947W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves =
      routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
          leaves) :=
  rfl

/-- W948 direct calculus delegates to W947 after normalized-source-triangulation bundling. -/
theorem w948DirectCalculusRunsThroughW947W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves =
      directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
          leaves) :=
  rfl

/-- W948 stable package delegates to W947 after normalized-source-triangulation bundling. -/
theorem w948StablePackageRunsThroughW947W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
          leaves) :=
  rfl

/-- W949 concrete leaves delegate to W948 after endpoint-localized-unit bundling. -/
theorem w949ConcreteLeavesRunThroughW948W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
        leaves =
      concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
          leaves) :=
  rfl

/-- W949 route data delegates to W948 after endpoint-localized-unit bundling. -/
theorem w949RouteDataProviderRunsThroughW948W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
        leaves =
      routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
          leaves) :=
  rfl

/-- W949 direct calculus delegates to W948 after endpoint-localized-unit bundling. -/
theorem w949DirectCalculusRunsThroughW948W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
        leaves =
      directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
          leaves) :=
  rfl

/-- W949 stable package delegates to W948 after endpoint-localized-unit bundling. -/
theorem w949StablePackageRunsThroughW948W1394
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
        (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
          leaves) :=
  rfl

/-- W1394 keeps W946-W949 input counts visible. -/
theorem w1394ClosedMapBoundaryRelationEndpointDataInputCounts :
    closedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW946.length =
        7 ∧
      closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947.length =
        6 ∧
      closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948.length =
        5 ∧
      closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949.length =
        4 :=
  ⟨closedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW946_count,
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947_count,
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948_count,
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949_count⟩

/-- Current W1394 nonterminal state. -/
structure ClosedMapBoundaryRelationEndpointDataStableConvergenceStateW1394 :
    Type where
  seed : String
  declarations : List String
  boundaryRelationResult : String
  targetClosednessResult : String
  normalizedSourceResult : String
  endpointLocalizedResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1394 records W946-W949 convergence into the closed-map stable route. -/
def currentClosedMapBoundaryRelationEndpointDataStableConvergenceStateW1394 :
    ClosedMapBoundaryRelationEndpointDataStableConvergenceStateW1394 where
  seed := "w1394-closed-map-boundary-relation-endpoint-data-stable-convergence"
  declarations :=
    ["w946ConcreteLeavesRunThroughW945W1394",
      "w946RouteDataProviderRunsThroughW945W1394",
      "w946DirectCalculusRunsThroughW945W1394",
      "w946StablePackageRunsThroughW945W1394",
      "w947ConcreteLeavesRunThroughW946W1394",
      "w947RouteDataProviderRunsThroughW946W1394",
      "w947DirectCalculusRunsThroughW946W1394",
      "w947StablePackageRunsThroughW946W1394",
      "w948ConcreteLeavesRunThroughW947W1394",
      "w948RouteDataProviderRunsThroughW947W1394",
      "w948DirectCalculusRunsThroughW947W1394",
      "w948StablePackageRunsThroughW947W1394",
      "w949ConcreteLeavesRunThroughW948W1394",
      "w949RouteDataProviderRunsThroughW948W1394",
      "w949DirectCalculusRunsThroughW948W1394",
      "w949StablePackageRunsThroughW948W1394",
      "w1394ClosedMapBoundaryRelationEndpointDataInputCounts"]
  boundaryRelationResult :=
    "proved: W946 boundary/relation data delegates into W945"
  targetClosednessResult :=
    "proved: W947 target-no-univ/closedness data delegates into W946"
  normalizedSourceResult :=
    "proved: W948 normalized-source-triangulation data delegates into W947"
  endpointLocalizedResult :=
    "proved: W949 endpoint-localized-unit data delegates into W948"
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949
  productSuccessClaimed := false

theorem currentW1394ClosedMapBoundaryRelationEndpointDataStableConvergence_productSuccess :
    currentClosedMapBoundaryRelationEndpointDataStableConvergenceStateW1394.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
