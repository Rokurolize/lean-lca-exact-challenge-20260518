import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetSurjectiveCompactKernelCokernelTopIsoFieldSplitGuardW1331
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W1332 supplements the existing W1308 W974 boundary guard by recording
additional field-split equalities from the endpoint kernel/cokernel-top
provider into the W973 leaves. The route still exposes W974's thirteen-input
component surface and therefore does not close the current one-input W987
obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332 :
    List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974

theorem canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332_count :
    canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332.length =
      13 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974_count

theorem canonicalW974EndpointKernelCokernelTopFieldSplitExpandsCurrentSurfaceW1332 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332_count]
  norm_num

theorem w974KeepsBoundaryRelationW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).boundaryRelationData =
      leaves.boundaryRelationData :=
  rfl

theorem w974KeepsTargetNoUnivW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).targetNoUnivData =
      leaves.targetNoUnivData :=
  rfl

theorem w974KeepsClosednessW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).closedEmbeddingClosednessData =
      leaves.closedEmbeddingClosednessData :=
  rfl

theorem w974KeepsNormalizedSourceW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).normalizedSourceTriangulationData =
      leaves.normalizedSourceTriangulationData :=
  rfl

theorem w974EndpointOpenMapOfLeavesW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).endpointOpenMap =
      endpointOpenMapOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData :=
  rfl

theorem w974EndpointCokernelTopOfLeavesW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).endpointCokernelTop =
      endpointCokernelTopOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData :=
  rfl

theorem w974KeepsLocalizedRightAdjointW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).boundedHomotopyLocalizedRightAdjoint =
      leaves.boundedHomotopyLocalizedRightAdjoint :=
  rfl

theorem w974KeepsUnitMappingConeIsoW1332
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).unitMappingConeIso =
      leaves.unitMappingConeIso :=
  rfl

structure MetrizableEndpointKernelCokernelTopFieldSplitGuardStateW1332 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointKernelCokernelTopFieldSplitGuardStateW1332 :
    MetrizableEndpointKernelCokernelTopFieldSplitGuardStateW1332 where
  seed := "w1332-endpoint-kernel-cokernel-top-field-split-guard"
  inspectedBoundary :=
    "W974 field split from endpoint kernel/cokernel-top data into W973 leaves"
  routeSurfaceCount :=
    canonicalW974EndpointKernelCokernelTopFieldSplitInputNamesW1332.length
  providerSearchResult :=
    "proved: W974 preserves boundary/relation, target no-univ, closedness,\
      normalized-source, endpoint open-map, endpoint cokernel-top, localized\
      right adjoint, and unit isomorphism fields while rebuilding W973, but\
      its route surface still has thirteen inputs and expands the current\
      one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1332EndpointKernelCokernelTopFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableEndpointKernelCokernelTopFieldSplitGuardStateW1332;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
