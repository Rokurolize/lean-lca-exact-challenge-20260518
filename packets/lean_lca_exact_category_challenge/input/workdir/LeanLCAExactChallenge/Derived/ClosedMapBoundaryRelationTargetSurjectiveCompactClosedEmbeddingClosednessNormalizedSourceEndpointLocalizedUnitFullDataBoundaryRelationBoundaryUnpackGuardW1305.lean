import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetNoUnivClosednessBoundaryUnpackGuardW1304

/-!
W1305 records the W730 boundary/relation provider boundary used by W946.
Unpacking W730 exposes W716 boundary data and W717 relation data; the older W730,
W716, and W717 routes all expand beyond the remaining W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW730BoundaryRelationInnerInputNamesW1305 : List String :=
  ["W716 WPP-limit boundary data provider",
    "W717 closed-natural-transformation relation data provider"]

theorem canonicalW730BoundaryRelationInnerInputNamesW1305_count :
    canonicalW730BoundaryRelationInnerInputNamesW1305.length = 2 :=
  rfl

def canonicalW730BoundaryRelationRouteInputNamesW1305 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryBoundaryRelationTargetClosednessNormalizedFixedTargetSourceEndpointInputNamesW730

theorem canonicalW730BoundaryRelationRouteInputNamesW1305_count :
    canonicalW730BoundaryRelationRouteInputNamesW1305.length = 3 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryBoundaryRelationTargetClosednessNormalizedFixedTargetSourceEndpointInputNamesW730_count

def canonicalW716BoundaryDataRouteInputNamesW1305 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryExplicitRelationFieldsTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW716

theorem canonicalW716BoundaryDataRouteInputNamesW1305_count :
    canonicalW716BoundaryDataRouteInputNamesW1305.length = 22 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryExplicitRelationFieldsTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW716_count

def canonicalW717RelationDataRouteInputNamesW1305 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW717

theorem canonicalW717RelationDataRouteInputNamesW1305_count :
    canonicalW717RelationDataRouteInputNamesW1305.length = 21 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW717_count

theorem canonicalW730BoundaryRelationInnerUnpackExpandsCurrentSurfaceW1305 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW730BoundaryRelationInnerInputNamesW1305.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW730BoundaryRelationInnerInputNamesW1305_count]
  norm_num

theorem canonicalW730BoundaryRelationRouteExpandsCurrentSurfaceW1305 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW730BoundaryRelationRouteInputNamesW1305.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW730BoundaryRelationRouteInputNamesW1305_count]
  norm_num

theorem canonicalW716BoundaryDataRouteExpandsCurrentSurfaceW1305 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW716BoundaryDataRouteInputNamesW1305.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW716BoundaryDataRouteInputNamesW1305_count]
  norm_num

theorem canonicalW717RelationDataRouteExpandsCurrentSurfaceW1305 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW717RelationDataRouteInputNamesW1305.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW717RelationDataRouteInputNamesW1305_count]
  norm_num

def repackBoundaryRelationDataW1305
    (boundaryRelationData : MetrizableWppBoundaryRelationDataProviderW730) :
    MetrizableWppBoundaryRelationDataProviderW730
    where
  boundaryData :=
    boundaryData_of_boundaryRelationDataW730 boundaryRelationData
  relationData :=
    relationData_of_boundaryRelationDataW730 boundaryRelationData

theorem repackBoundaryRelationDataW1305_eq
    (boundaryRelationData : MetrizableWppBoundaryRelationDataProviderW730) :
    repackBoundaryRelationDataW1305 boundaryRelationData =
      boundaryRelationData := by
  cases boundaryRelationData
  rfl

theorem w945LeavesBoundaryDataOfW946LeavesW1305
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves).boundaryData =
      boundaryData_of_boundaryRelationDataW730 leaves.boundaryRelationData :=
  rfl

theorem w945LeavesRelationDataOfW946LeavesW1305
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946) :
    (w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        leaves).relationData =
      relationData_of_boundaryRelationDataW730 leaves.boundaryRelationData :=
  rfl

structure MetrizableBoundaryRelationBoundaryUnpackGuardStateW1305 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  boundaryRelationRouteSurfaceCount : Nat
  boundaryDataRouteSurfaceCount : Nat
  relationDataRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBoundaryRelationBoundaryUnpackGuardStateW1305 :
    MetrizableBoundaryRelationBoundaryUnpackGuardStateW1305 where
  seed := "w1305-boundary-relation-boundary-unpack-guard"
  inspectedBoundary :=
    "W730 canonical projections to W716 boundary data and W717 relation data"
  innerSurfaceCount :=
    canonicalW730BoundaryRelationInnerInputNamesW1305.length
  boundaryRelationRouteSurfaceCount :=
    canonicalW730BoundaryRelationRouteInputNamesW1305.length
  boundaryDataRouteSurfaceCount :=
    canonicalW716BoundaryDataRouteInputNamesW1305.length
  relationDataRouteSurfaceCount :=
    canonicalW717RelationDataRouteInputNamesW1305.length
  providerSearchResult :=
    "proved: canonical W730 boundary/relation unpacking exposes a two-input\
      provider boundary, while W730, W716, and W717 routes expand to three,\
      twenty-two, and twenty-one inputs; repacking W730 projections is the same\
      provider, so this boundary does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1305BoundaryRelationBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableBoundaryRelationBoundaryUnpackGuardStateW1305;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
