import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataLocalizedAdjunctionBoundaryUnpackGuardW1309
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRoute

/-!
W1310 records the W976 dependent unit mapping-cone provider boundary.
Unpacking W976 exposes the model, four degreewise kernel/cokernel-top fields,
and the chosen isomorphism; the W976 route itself remains a seven-input surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW976UnitMappingConeInnerInputNamesW1310 :
    List String :=
  ["unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise cokernel-subgroup-top components",
    "unit mapping-cone degreewise kernel-equality components",
    "chosen unit mapping-cone isomorphism from the adjunction-unit mapping cone\
      to the chosen model"]

theorem canonicalW976UnitMappingConeInnerInputNamesW1310_count :
    canonicalW976UnitMappingConeInnerInputNamesW1310.length = 6 :=
  rfl

def canonicalW976UnitMappingConeRouteInputNamesW1310 :
    List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976

theorem canonicalW976UnitMappingConeRouteInputNamesW1310_count :
    canonicalW976UnitMappingConeRouteInputNamesW1310.length = 7 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976_count

theorem canonicalW976UnitMappingConeInnerUnpackExpandsCurrentSurfaceW1310 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW976UnitMappingConeInnerInputNamesW1310.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW976UnitMappingConeInnerInputNamesW1310_count]
  norm_num

theorem canonicalW976UnitMappingConeRouteExpandsCurrentSurfaceW1310 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW976UnitMappingConeRouteInputNamesW1310.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW976UnitMappingConeRouteInputNamesW1310_count]
  norm_num

def repackUnitMappingConeDataW1310
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      localizedAdjunctionData
    where
  unitMappingConeModel :=
    unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData
  unitMappingConeClosedEmbedding :=
    unitMappingConeClosedEmbeddingOfUnitKernelCokernelTopIsoDataW976 unitData
  unitMappingConeOpenMap :=
    unitMappingConeOpenMapOfUnitKernelCokernelTopIsoDataW976 unitData
  unitMappingConeCokernelTop :=
    unitMappingConeCokernelTopOfUnitKernelCokernelTopIsoDataW976 unitData
  unitMappingConeKernelEquality :=
    unitMappingConeKernelEqualityOfUnitKernelCokernelTopIsoDataW976 unitData
  unitMappingConeIso :=
    unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976 unitData

theorem repackUnitMappingConeDataW1310_eq
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    repackUnitMappingConeDataW1310 unitData =
      unitData := by
  cases unitData
  rfl

theorem w975LeavesUnitMappingConeModelOfW976LeavesW1310
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
        leaves).unitMappingConeModel =
      unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
        leaves.unitKernelCokernelTopIsoData :=
  rfl

theorem w975LeavesUnitMappingConeIsoOfW976LeavesW1310
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
        leaves).unitMappingConeIso =
      unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976
        leaves.unitKernelCokernelTopIsoData :=
  rfl

structure MetrizableUnitMappingConeBoundaryUnpackGuardStateW1310 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitMappingConeBoundaryUnpackGuardStateW1310 :
    MetrizableUnitMappingConeBoundaryUnpackGuardStateW1310 where
  seed := "w1310-unit-mapping-cone-boundary-unpack-guard"
  inspectedBoundary :=
    "W976 canonical projections to unit mapping-cone model, closed/open\
      components, cokernel-top, kernel-equality, and chosen isomorphism"
  innerSurfaceCount :=
    canonicalW976UnitMappingConeInnerInputNamesW1310.length
  routeSurfaceCount :=
    canonicalW976UnitMappingConeRouteInputNamesW1310.length
  providerSearchResult :=
    "proved: canonical W976 unit mapping-cone unpacking exposes a six-input\
      provider boundary and a seven-input route; repacking W976 projections is\
      the same dependent provider, so this boundary does not close the\
      remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1310UnitMappingConeBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableUnitMappingConeBoundaryUnpackGuardStateW1310;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
