import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987FieldDataConstructionGuardW1450

set_option autoImplicit false

namespace LeanLCAExactChallenge

namespace Dbounded

#check W987FieldDataConstructionInputW1450
#check MetrizableWppLimitBoundaryDataW716
#check ClosedNatTransOrdinaryRelationDataProviderW717
#check TargetNoUnivClosedEmbeddingClosednessDataProviderW984
#check NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
#check fullDataOfW987FieldDataW1450

noncomputable def attemptedW1450BoundaryData :
    MetrizableWppLimitBoundaryDataW716 := by
  refine
    { rightOpenBoundary := ?rightOpenBoundary
      sourcePiZeroBoundary := ?sourcePiZeroBoundary }

noncomputable def attemptedW1450RelationData :
    ClosedNatTransOrdinaryRelationDataProviderW717 := by
  refine
    { relationPullbackProvider := ?relationPullbackProvider
      targetRelationLiftsProvider := ?targetRelationLiftsProvider }

noncomputable def attemptedW1450TargetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 := by
  refine
    { targetNoUnivData := ?targetNoUnivData
      closedEmbeddingClosednessData := ?closedEmbeddingClosednessData }

noncomputable def attemptedW1450NormalizedSourceEndpointData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 := by
  refine
    { normalizedSourceTriangulationData := ?normalizedSourceTriangulationData
      endpointLocalizedUnitData := ?endpointLocalizedUnitData }

noncomputable def attemptedW1450FieldData :
    W987FieldDataConstructionInputW1450 := by
  refine
    { boundaryData := ?boundaryData
      relationData := ?relationData
      targetClosedEmbeddingClosednessData := ?targetClosedEmbeddingClosednessData
      normalizedSourceEndpointLocalizedUnitData :=
        ?normalizedSourceEndpointLocalizedUnitData }

noncomputable def attemptedW1450FullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 := by
  exact fullDataOfW987FieldDataW1450 attemptedW1450FieldData

end Dbounded

end LeanLCAExactChallenge
