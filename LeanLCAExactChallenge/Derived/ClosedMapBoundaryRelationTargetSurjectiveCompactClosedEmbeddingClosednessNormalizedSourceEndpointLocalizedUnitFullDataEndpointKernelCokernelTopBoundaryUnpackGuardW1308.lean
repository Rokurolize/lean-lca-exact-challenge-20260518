import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedEmbeddingClosednessBoundaryUnpackGuardW1307
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W1308 records the W974 endpoint kernel/cokernel-top provider boundary.
Unpacking W974 exposes the four endpoint exactness witnesses, and the W974
route itself expands to a thirteen-input component surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308 :
    List String :=
  ["endpoint degreewise closed-embedding witnesses",
    "endpoint degreewise open-map witnesses",
    "endpoint degreewise cokernel-subgroup-top witnesses",
    "endpoint degreewise kernel-equality witnesses"]

theorem canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308_count :
    canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308.length = 4 :=
  rfl

def canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308 :
    List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974

theorem canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308_count :
    canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308.length = 13 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974_count

theorem canonicalW974EndpointKernelCokernelTopInnerUnpackExpandsCurrentSurfaceW1308 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308_count]
  norm_num

theorem canonicalW974EndpointKernelCokernelTopRouteExpandsCurrentSurfaceW1308 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308_count]
  norm_num

def repackEndpointKernelCokernelTopDataW1308
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    EndpointKernelCokernelTopDataProviderW974
    where
  endpointClosedEmbedding :=
    endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974 endpointData
  endpointOpenMap :=
    endpointOpenMapOfEndpointKernelCokernelTopDataW974 endpointData
  endpointCokernelTop :=
    endpointCokernelTopOfEndpointKernelCokernelTopDataW974 endpointData
  endpointKernelEquality :=
    endpointKernelEqualityOfEndpointKernelCokernelTopDataW974 endpointData

theorem repackEndpointKernelCokernelTopDataW1308_eq
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    repackEndpointKernelCokernelTopDataW1308 endpointData =
      endpointData := by
  cases endpointData
  rfl

theorem w973LeavesEndpointClosedEmbeddingOfW974LeavesW1308
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).endpointClosedEmbedding =
      endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData :=
  rfl

theorem w973LeavesEndpointKernelEqualityOfW974LeavesW1308
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        leaves).endpointKernelEquality =
      endpointKernelEqualityOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData :=
  rfl

structure MetrizableEndpointKernelCokernelTopBoundaryUnpackGuardStateW1308 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointKernelCokernelTopBoundaryUnpackGuardStateW1308 :
    MetrizableEndpointKernelCokernelTopBoundaryUnpackGuardStateW1308 where
  seed := "w1308-endpoint-kernel-cokernel-top-boundary-unpack-guard"
  inspectedBoundary :=
    "W974 canonical projections to endpoint closed-embedding, open-map,\
      cokernel-top, and kernel-equality witnesses"
  innerSurfaceCount :=
    canonicalW974EndpointKernelCokernelTopInnerInputNamesW1308.length
  routeSurfaceCount :=
    canonicalW974EndpointKernelCokernelTopRouteInputNamesW1308.length
  providerSearchResult :=
    "proved: canonical W974 endpoint kernel/cokernel-top unpacking exposes a\
      four-input provider boundary and a thirteen-input component route;\
      repacking W974 projections is the same provider, so this boundary does\
      not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1308EndpointKernelCokernelTopBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableEndpointKernelCokernelTopBoundaryUnpackGuardStateW1308;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
