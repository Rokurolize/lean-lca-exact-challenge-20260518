import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderBoundaryUnpackGuardW1298

/-!
W1299 records the next canonical boundary inside the W986 provider exposed by
W1298. Unpacking W986 exposes W984 target/closedness data and W950 normalized
source/endpoint-localized data; with W730 this is the W985 three-input surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW986InnerUnpackedInputNamesW1299 : List String :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985

theorem canonicalW986InnerUnpackedInputNamesW1299_count :
    canonicalW986InnerUnpackedInputNamesW1299.length = 3 :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count

theorem canonicalW986InnerUnpackExpandsW986SurfaceW1299 :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986.length <
      canonicalW986InnerUnpackedInputNamesW1299.length := by
  rw [targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count,
    canonicalW986InnerUnpackedInputNamesW1299_count]
  norm_num

theorem canonicalW986InnerUnpackExpandsCurrentSurfaceW1299 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW986InnerUnpackedInputNamesW1299.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW986InnerUnpackedInputNamesW1299_count]
  norm_num

def repackTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW1299
    (targetNormalizedEndpointData :
      TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
      targetNormalizedEndpointData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
      targetNormalizedEndpointData

theorem repackTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW1299_eq
    (targetNormalizedEndpointData :
      TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    repackTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW1299
        targetNormalizedEndpointData =
      targetNormalizedEndpointData := by
  cases targetNormalizedEndpointData
  rfl

theorem w985FullDataTargetDataOfW986FullDataW1299
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        fullData).targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        fullData.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w985FullDataNormalizedEndpointDataOfW986FullDataW1299
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
        fullData).normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        fullData.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
  rfl

structure MetrizableInnerProviderBoundaryUnpackGuardStateW1299 : Type where
  seed : String
  inspectedBoundary : String
  unpackedSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableInnerProviderBoundaryUnpackGuardStateW1299 :
    MetrizableInnerProviderBoundaryUnpackGuardStateW1299 where
  seed := "w1299-inner-provider-boundary-unpack-guard"
  inspectedBoundary :=
    "W986 canonical projections to W984 target/closedness data and W950\
      normalized-source/endpoint-localized data"
  unpackedSurfaceCount := canonicalW986InnerUnpackedInputNamesW1299.length
  providerSearchResult :=
    "proved: canonical W986 unpacking exposes the W985 three-input surface and\
      repacking the W986 inner projections is the same provider, so this\
      boundary does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1299InnerProviderBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableInnerProviderBoundaryUnpackGuardStateW1299;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
