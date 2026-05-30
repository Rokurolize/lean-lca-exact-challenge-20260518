import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataNormalizedSourceTriangulationBoundaryUnpackGuardW1303

/-!
W1304 records the W947 target-no-univ/closedness provider boundary. Unpacking
W947 exposes W944 target no-univ data and W725 closedness-branch data; opening
the adjacent W946, W725, or W944 routes only expands to larger surfaces, so this
boundary does not close the remaining W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW947TargetNoUnivClosednessInnerInputNamesW1304 :
    List String :=
  ["W944 target no-univ data provider",
    "W725 selected-difference and mapped-cokernel closedness branch data"]

theorem canonicalW947TargetNoUnivClosednessInnerInputNamesW1304_count :
    canonicalW947TargetNoUnivClosednessInnerInputNamesW1304.length = 2 :=
  rfl

def canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304 :
    List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947

theorem canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304_count :
    canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304.length = 6 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947_count

def canonicalW946TargetNoUnivClosednessExpandedInputNamesW1304 :
    List String :=
  closedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW946

theorem canonicalW946TargetNoUnivClosednessExpandedInputNamesW1304_count :
    canonicalW946TargetNoUnivClosednessExpandedInputNamesW1304.length = 7 :=
  closedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW946_count

def canonicalW725ClosednessBranchRouteInputNamesW1304 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryClosednessBranchEndpointStrictTopologyDataNormalizedFixedTargetLocalizedRightAdjointSourceHomologicalTriangulationInputNamesW725

theorem canonicalW725ClosednessBranchRouteInputNamesW1304_count :
    canonicalW725ClosednessBranchRouteInputNamesW1304.length = 8 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryClosednessBranchEndpointStrictTopologyDataNormalizedFixedTargetLocalizedRightAdjointSourceHomologicalTriangulationInputNamesW725_count

def canonicalW944TargetNoUnivRouteInputNamesW1304 : List String :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944

theorem canonicalW944TargetNoUnivRouteInputNamesW1304_count :
    canonicalW944TargetNoUnivRouteInputNamesW1304.length = 10 :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944_count

theorem canonicalW947TargetNoUnivClosednessInnerUnpackExpandsCurrentSurfaceW1304 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW947TargetNoUnivClosednessInnerInputNamesW1304.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW947TargetNoUnivClosednessInnerInputNamesW1304_count]
  norm_num

theorem canonicalW947TargetNoUnivClosednessPrimitiveRouteExpandsCurrentSurfaceW1304 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304_count]
  norm_num

theorem canonicalW946TargetNoUnivClosednessExpandedRouteExpandsCurrentSurfaceW1304 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW946TargetNoUnivClosednessExpandedInputNamesW1304.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW946TargetNoUnivClosednessExpandedInputNamesW1304_count]
  norm_num

theorem canonicalW725ClosednessBranchRouteExpandsCurrentSurfaceW1304 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW725ClosednessBranchRouteInputNamesW1304.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW725ClosednessBranchRouteInputNamesW1304_count]
  norm_num

theorem canonicalW944TargetNoUnivRouteExpandsCurrentSurfaceW1304 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW944TargetNoUnivRouteInputNamesW1304.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW944TargetNoUnivRouteInputNamesW1304_count]
  norm_num

def repackTargetNoUnivClosednessDataW1304
    (targetNoUnivClosednessData :
      TargetNoUnivMembershipClosednessDataProviderW947) :
    TargetNoUnivMembershipClosednessDataProviderW947
    where
  targetNoUnivData :=
    targetNoUnivDataOfTargetNoUnivClosednessDataW947
      targetNoUnivClosednessData
  diagramAndMappedCokernelClosednessData :=
    diagramAndMappedCokernelClosednessDataOfTargetNoUnivClosednessDataW947
      targetNoUnivClosednessData

theorem repackTargetNoUnivClosednessDataW1304_eq
    (targetNoUnivClosednessData :
      TargetNoUnivMembershipClosednessDataProviderW947) :
    repackTargetNoUnivClosednessDataW1304
        targetNoUnivClosednessData =
      targetNoUnivClosednessData := by
  cases targetNoUnivClosednessData
  rfl

theorem w946LeavesTargetNoUnivOfW947LeavesW1304
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves).targetNoUnivData =
      targetNoUnivDataOfTargetNoUnivClosednessDataW947
        leaves.targetNoUnivClosednessData :=
  rfl

theorem w946LeavesClosednessOfW947LeavesW1304
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        leaves).diagramAndMappedCokernelClosednessData =
      diagramAndMappedCokernelClosednessDataOfTargetNoUnivClosednessDataW947
        leaves.targetNoUnivClosednessData :=
  rfl

structure MetrizableTargetNoUnivClosednessBoundaryUnpackGuardStateW1304 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  primitiveRouteSurfaceCount : Nat
  closednessBranchRouteSurfaceCount : Nat
  targetNoUnivRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetNoUnivClosednessBoundaryUnpackGuardStateW1304 :
    MetrizableTargetNoUnivClosednessBoundaryUnpackGuardStateW1304 where
  seed := "w1304-target-no-univ-closedness-boundary-unpack-guard"
  inspectedBoundary :=
    "W947 canonical projections to W944 target no-univ data and W725\
      closedness-branch data"
  innerSurfaceCount :=
    canonicalW947TargetNoUnivClosednessInnerInputNamesW1304.length
  primitiveRouteSurfaceCount :=
    canonicalW947TargetNoUnivClosednessPrimitiveInputNamesW1304.length
  closednessBranchRouteSurfaceCount :=
    canonicalW725ClosednessBranchRouteInputNamesW1304.length
  targetNoUnivRouteSurfaceCount :=
    canonicalW944TargetNoUnivRouteInputNamesW1304.length
  providerSearchResult :=
    "proved: canonical W947 target-no-univ/closedness unpacking exposes a\
      two-input provider boundary, while adjacent W946, W725, and W944 routes\
      expand to seven, eight, and ten inputs; repacking W947 projections is the\
      same provider, so this boundary does not close the remaining W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1304TargetNoUnivClosednessBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableTargetNoUnivClosednessBoundaryUnpackGuardStateW1304;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
