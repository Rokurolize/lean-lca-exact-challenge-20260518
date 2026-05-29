import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataNormalizedSourceEndpointGuardW1326
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceRoute

/-!
W1327 supplements the existing W1317 W988 guard by recording the remaining
field-split equalities in the localized-unit-choice to full-data route. The
route still exposes W982's six inputs and therefore does not close the current
one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327 :
    List String :=
  localizedUnitChoiceInputNamesW988

theorem canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327_count :
    canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327.length = 6 :=
  localizedUnitChoiceInputNamesW988_count

theorem canonicalW988LocalizedUnitChoiceFieldSplitExpandsCurrentSurfaceW1327 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327_count]
  norm_num

theorem w988TargetClosedEmbeddingClosednessKeepsClosednessW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988
        data).closedEmbeddingClosednessData =
      data.closedEmbeddingClosednessData :=
  rfl

theorem w988EndpointLocalizedUnitKeepsEndpointStrictExactW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (endpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        data).endpointStrictExact =
      data.endpointStrictExact :=
  rfl

theorem w988NormalizedEndpointKeepsNormalizedSourceW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        data).normalizedSourceTriangulationData =
      data.normalizedSourceTriangulationData :=
  rfl

theorem w988NormalizedEndpointUsesEndpointLocalizedUnitW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        data).endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfLocalizedUnitChoiceW988 data :=
  rfl

theorem w988InnerProviderUsesTargetClosedEmbeddingClosednessW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        data).targetClosedEmbeddingClosednessData =
      targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988 data :=
  rfl

theorem w988InnerProviderUsesNormalizedEndpointW1327
    (data :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
        data).normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988 data :=
  rfl

structure MetrizableLocalizedUnitChoiceFieldSplitGuardStateW1327 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceFieldSplitGuardStateW1327 :
    MetrizableLocalizedUnitChoiceFieldSplitGuardStateW1327 where
  seed := "w1327-localized-unit-choice-field-split-guard"
  inspectedBoundary :=
    "W988 field split from W982 localized-unit-choice data into W984, W949,\
      W950, and W986"
  routeSurfaceCount :=
    canonicalW988LocalizedUnitChoiceFieldSplitInputNamesW1327.length
  providerSearchResult :=
    "proved: W988 preserves the closedness, endpoint strict exactness,\
      normalized-source, endpoint-localized, target/closedness, and\
      normalized-endpoint fields while constructing W986, but its route surface\
      still has six inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1327LocalizedUnitChoiceFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceFieldSplitGuardStateW1327;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
