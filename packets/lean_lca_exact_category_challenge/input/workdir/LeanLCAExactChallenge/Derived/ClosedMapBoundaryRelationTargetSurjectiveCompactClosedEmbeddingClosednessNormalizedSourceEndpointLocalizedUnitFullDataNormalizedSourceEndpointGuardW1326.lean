import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetCompactTargetProviderGuardW1325
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W1326 records the W994 normalized-source/endpoint route. W994 consumes the
four-input W730/W715/W973/W950 surface and uses W950 to provide W993's endpoint
strict exactness, localized-unit data, and normalized-source triangulation.
This still expands the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW994NormalizedSourceEndpointInputNamesW1326 :
    List String :=
  targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994

theorem canonicalW994NormalizedSourceEndpointInputNamesW1326_count :
    canonicalW994NormalizedSourceEndpointInputNamesW1326.length = 4 :=
  targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994_count

theorem canonicalW994NormalizedSourceEndpointExpandsCurrentSurfaceW1326 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW994NormalizedSourceEndpointInputNamesW1326.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW994NormalizedSourceEndpointInputNamesW1326_count]
  norm_num

theorem w994ProjectsEndpointLocalizedUnitDataW1326
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data =
      endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        data.normalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w994LocalizedUnitChoiceEndpointStrictExactW1326
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
      data).endpointStrictExact =
      endpointStrictExactOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
          data) :=
  rfl

theorem w994LocalizedUnitChoiceLocalizedUnitDataW1326
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
      data).localizedUnitData =
      localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
          data) :=
  rfl

theorem w994LocalizedUnitChoiceNormalizedSourceDataW1326
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
      data).normalizedSourceTriangulationData =
      normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        data.normalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w994FullDataRunsThroughW993W1326
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994) :
    fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994 data =
      fullDataOfTargetSurjectiveCompactLocalizedUnitChoiceW993
        (localizedUnitChoiceDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
          data) :=
  rfl

structure MetrizableNormalizedSourceEndpointGuardStateW1326 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointGuardStateW1326 :
    MetrizableNormalizedSourceEndpointGuardStateW1326 where
  seed := "w1326-normalized-source-endpoint-guard"
  inspectedBoundary :=
    "W994 construction of W993 data from W730, W715, W973, and W950"
  routeSurfaceCount :=
    canonicalW994NormalizedSourceEndpointInputNamesW1326.length
  providerSearchResult :=
    "proved: W994 projects W950 into endpoint strict exactness, localized-unit\
      data, and normalized-source triangulation for W993, but its route surface\
      has four inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1326NormalizedSourceEndpointGuard_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointGuardStateW1326;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
