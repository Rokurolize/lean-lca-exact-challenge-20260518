import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataUnitStrictExactIsoToLocalizedUnitChoiceGuardW1316
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceRoute

/-!
W1317 records the W988 localized-unit-choice route. W988 constructs the W987
full-data provider from the W982 localized-unit-choice surface, which is still
a six-input expansion of the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW988LocalizedUnitChoiceInputNamesW1317 : List String :=
  localizedUnitChoiceInputNamesW988

theorem canonicalW988LocalizedUnitChoiceInputNamesW1317_count :
    canonicalW988LocalizedUnitChoiceInputNamesW1317.length = 6 :=
  localizedUnitChoiceInputNamesW988_count

theorem canonicalW988LocalizedUnitChoiceRouteExpandsCurrentSurfaceW1317 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW988LocalizedUnitChoiceInputNamesW1317.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW988LocalizedUnitChoiceInputNamesW1317_count]
  norm_num

theorem w988BuildsTargetClosedEmbeddingClosednessDataW1317
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988
        localizedUnitChoiceData).targetNoUnivData =
      localizedUnitChoiceData.targetNoUnivData :=
  rfl

theorem w988BuildsEndpointLocalizedUnitDataW1317
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (endpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        localizedUnitChoiceData).localizedUnitData =
      localizedUnitChoiceData.localizedUnitData :=
  rfl

theorem w988FullDataKeepsBoundaryRelationW1317
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (fullDataOfLocalizedUnitChoiceW988
        localizedUnitChoiceData).boundaryRelationData =
      localizedUnitChoiceData.boundaryRelationData :=
  rfl

theorem w988FullDataBuildsInnerProviderW1317
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData).targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        localizedUnitChoiceData :=
  rfl

structure MetrizableLocalizedUnitChoiceToFullDataGuardStateW1317 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToFullDataGuardStateW1317 :
    MetrizableLocalizedUnitChoiceToFullDataGuardStateW1317 where
  seed := "w1317-localized-unit-choice-to-full-data-guard"
  inspectedBoundary :=
    "W988 construction of W987 full data from W982 localized-unit-choice data"
  routeSurfaceCount := canonicalW988LocalizedUnitChoiceInputNamesW1317.length
  providerSearchResult :=
    "proved: W988 constructs W987 by packaging W982 localized-unit-choice\
      fields into W984, W949, W950, and W986 data, but the route surface has\
      six inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1317LocalizedUnitChoiceToFullDataGuard_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToFullDataGuardStateW1317;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
