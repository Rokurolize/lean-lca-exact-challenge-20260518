import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBoundaryRelationDataStableConvergenceFieldSplitGuardW1413
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataNormalizedSourceTriangulationDataClosedEmbeddingClosednessFieldsEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W1414 records definitional convergence for the W972 target-no-univ-data
bridge: W972 projects the W944 provider into the split target primitives before
delegating into the W971 boundary/relation-data route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W972 constructs W971 leaves after unpacking W944 target no-univ data. -/
theorem w972W971LeavesRunThroughTargetNoUnivDataW1414
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves =
      w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves :=
  rfl

/-- W972 constructs W970 leaves by delegating through W971. -/
theorem w972W970LeavesRunThroughW971W1414
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    w970LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves =
      w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
        (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
          leaves) :=
  rfl

/-- W972 constructs W968 leaves by delegating through W971. -/
theorem w972W968LeavesRunThroughW971W1414
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    w968LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves =
      w968LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
        (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
          leaves) :=
  rfl

/-- W972 direct calculus delegates to W971 after unpacking W944. -/
theorem w972DirectCalculusRunsThroughW971W1414
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    directBoundedLeftCalculusOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves =
      directBoundedLeftCalculusOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
        (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
          leaves) :=
  rfl

/-- W972 stable package delegates to W971 after unpacking W944. -/
theorem w972StablePackageRunsThroughW971W1414
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    boundedDerivedInfinityCategoryOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
        leaves =
      boundedDerivedInfinityCategoryOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
        (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
          leaves) :=
  rfl

/-- W1414 keeps the W972 target-no-univ-data input count visible. -/
theorem w1414ClosedMapTargetNoUnivDataInputCount :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972.length =
      17 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972_count

/-- Current W1414 nonterminal state. -/
structure ClosedMapTargetNoUnivDataStableConvergenceStateW1414 :
    Type where
  seed : String
  declarations : List String
  targetNoUnivDataBridgeResult : String
  targetNoUnivDataUnpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1414 records W972 convergence into the closed-map stable route. -/
def currentClosedMapTargetNoUnivDataStableConvergenceStateW1414 :
    ClosedMapTargetNoUnivDataStableConvergenceStateW1414 where
  seed := "w1414-closed-map-target-no-univ-data-stable-convergence"
  declarations :=
    ["w972W971LeavesRunThroughTargetNoUnivDataW1414",
      "w972W970LeavesRunThroughW971W1414",
      "w972W968LeavesRunThroughW971W1414",
      "w972DirectCalculusRunsThroughW971W1414",
      "w972StablePackageRunsThroughW971W1414",
      "w1414ClosedMapTargetNoUnivDataInputCount"]
  targetNoUnivDataBridgeResult :=
    "proved: W972 target-no-univ-data leaves delegate into W971"
  targetNoUnivDataUnpackResult :=
    "proved: W972 replaces split target-difference and target-codomain\
      no-univ primitives by the W944 provider"
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972
  productSuccessClaimed := false

theorem currentW1414ClosedMapTargetNoUnivDataStableConvergence_productSuccess :
    currentClosedMapTargetNoUnivDataStableConvergenceStateW1414.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
