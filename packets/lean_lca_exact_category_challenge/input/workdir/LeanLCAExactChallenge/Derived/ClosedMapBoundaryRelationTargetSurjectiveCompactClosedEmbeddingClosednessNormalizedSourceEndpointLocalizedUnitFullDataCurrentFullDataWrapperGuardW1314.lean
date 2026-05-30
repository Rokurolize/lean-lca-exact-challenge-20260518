import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSplitFullDataCycleGuardW1313
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitFullDataRoute

/-!
W1314 records the W977 current full-data wrapper. W977 is a one-input provider
surface that merely projects into the seven W976 leaves, so it keeps the
current one-input size rather than closing the W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW977CurrentFullDataInputNamesW1314 : List String :=
  closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977

theorem canonicalW977CurrentFullDataInputNamesW1314_count :
    canonicalW977CurrentFullDataInputNamesW1314.length = 1 :=
  closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977_count

def canonicalW976LeavesRouteInputNamesW1314 : List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976

theorem canonicalW976LeavesRouteInputNamesW1314_count :
    canonicalW976LeavesRouteInputNamesW1314.length = 7 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976_count

theorem canonicalW977CurrentFullDataKeepsCurrentSurfaceW1314 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      canonicalW977CurrentFullDataInputNamesW1314.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW977CurrentFullDataInputNamesW1314_count]

theorem canonicalW976LeavesRouteExpandsCurrentSurfaceW1314 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW976LeavesRouteInputNamesW1314.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW976LeavesRouteInputNamesW1314_count]
  norm_num

def repackCurrentFullDataW1314
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977
    where
  boundaryRelationData := boundaryRelationDataOfFullDataW977 fullData
  targetNoUnivData := targetNoUnivDataOfFullDataW977 fullData
  closedEmbeddingClosednessData := closedEmbeddingClosednessDataOfFullDataW977 fullData
  endpointKernelCokernelTopData :=
    endpointKernelCokernelTopDataOfFullDataW977 fullData
  localizedAdjunctionData := localizedAdjunctionDataOfFullDataW977 fullData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfFullDataW977 fullData
  unitKernelCokernelTopIsoData :=
    unitKernelCokernelTopIsoDataOfFullDataW977 fullData

theorem repackCurrentFullDataW1314_eq
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    repackCurrentFullDataW1314 fullData = fullData := by
  cases fullData
  rfl

theorem w976LeavesBoundaryRelationOfW977LeavesW1314
    (leaves : MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    (w976LeavesOfFullDataW977 leaves).boundaryRelationData =
      boundaryRelationDataOfFullDataW977 leaves.fullData :=
  rfl

theorem w976LeavesUnitDataOfW977LeavesW1314
    (leaves : MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    (w976LeavesOfFullDataW977 leaves).unitKernelCokernelTopIsoData =
      unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData :=
  rfl

structure MetrizableCurrentFullDataWrapperGuardStateW1314 : Type where
  seed : String
  inspectedBoundary : String
  wrapperSurfaceCount : Nat
  expandedRouteCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataWrapperGuardStateW1314 :
    MetrizableCurrentFullDataWrapperGuardStateW1314 where
  seed := "w1314-current-full-data-wrapper-guard"
  inspectedBoundary :=
    "W977 current full-data provider projecting into W730, W944, W973, W974,\
      W975, W948, and W976 leaves"
  wrapperSurfaceCount := canonicalW977CurrentFullDataInputNamesW1314.length
  expandedRouteCount := canonicalW976LeavesRouteInputNamesW1314.length
  providerSearchResult :=
    "proved: W977 keeps a one-input current full-data wrapper and expands to\
      the seven W976 leaves; repacking W977 projections is the same provider,\
      so this wrapper does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1314CurrentFullDataWrapperGuard_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataWrapperGuardStateW1314;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
