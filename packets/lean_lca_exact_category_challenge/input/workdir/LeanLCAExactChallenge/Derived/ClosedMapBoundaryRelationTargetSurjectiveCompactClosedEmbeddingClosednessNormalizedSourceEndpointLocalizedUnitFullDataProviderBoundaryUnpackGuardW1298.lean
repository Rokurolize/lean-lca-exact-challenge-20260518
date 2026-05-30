import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCandidateGuardConsolidationW1297

/-!
W1298 records the canonical W987 provider boundary: unpacking W987 exposes the
W730 boundary/relation provider and the W986 branch-specific provider, and
repacking those projections is judgmentally the same W987 provider.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalFullDataUnpackedInputNamesW1298 : List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986

theorem canonicalFullDataUnpackedInputNamesW1298_count :
    canonicalFullDataUnpackedInputNamesW1298.length = 2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count

theorem canonicalFullDataUnpackExpandsCurrentSurfaceW1298 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalFullDataUnpackedInputNamesW1298.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalFullDataUnpackedInputNamesW1298_count]
  norm_num

def repackFullDataOfFullDataW1298
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
    where
  boundaryRelationData := boundaryRelationDataOfFullDataW987 fullData
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
      fullData

theorem repackFullDataOfFullDataW1298_eq
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    repackFullDataOfFullDataW1298 fullData = fullData := by
  cases fullData
  rfl

theorem w986FullDataBoundaryRelationOfFullDataW1298
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (w986FullDataOfFullDataW987 fullData).boundaryRelationData =
      boundaryRelationDataOfFullDataW987 fullData :=
  rfl

theorem w986FullDataTargetDataOfFullDataW1298
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (w986FullDataOfFullDataW987 fullData).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        fullData :=
  rfl

structure MetrizableProviderBoundaryUnpackGuardStateW1298 : Type where
  seed : String
  inspectedBoundary : String
  unpackedSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableProviderBoundaryUnpackGuardStateW1298 :
    MetrizableProviderBoundaryUnpackGuardStateW1298 where
  seed := "w1298-provider-boundary-unpack-guard"
  inspectedBoundary :=
    "W987 canonical projections to W730 boundary/relation and W986 target/\
      normalized endpoint provider"
  unpackedSurfaceCount := canonicalFullDataUnpackedInputNamesW1298.length
  providerSearchResult :=
    "proved: canonical W987 unpacking exposes the W986 two-input surface and\
      repacking the projections is the same W987 provider, so this boundary\
      does not close the remaining one-input obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1298ProviderBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableProviderBoundaryUnpackGuardStateW1298;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
