import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetClosednessBoundaryUnpackGuardW1300

/-!
W1301 records the W983 endpoint-localized-unit full-data boundary reached from
W1300. Unpacking W983 exposes the existing five-input surface, and unpacking
its W949 endpoint-localized-unit provider exposes the earlier four-input
primitive route. Both surfaces are larger than the current one-input W987
obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301 : List String :=
  endpointLocalizedUnitChoiceFullDataInputNamesW983

theorem canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301_count :
    canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301.length = 5 :=
  endpointLocalizedUnitChoiceFullDataInputNamesW983_count

def canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301 : List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949

theorem canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301_count :
    canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301.length = 4 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949_count

theorem canonicalW983EndpointLocalizedUnitUnpackExpandsW984FullDataSurfaceW1301 :
    canonicalW984FullDataUnpackedInputNamesW1300.length <
      canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301.length := by
  rw [canonicalW984FullDataUnpackedInputNamesW1300_count,
    canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301_count]
  norm_num

theorem canonicalW983EndpointLocalizedUnitUnpackExpandsCurrentSurfaceW1301 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301_count]
  norm_num

theorem canonicalW949EndpointLocalizedUnitPrimitiveRouteExpandsCurrentSurfaceW1301 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301_count]
  norm_num

def repackEndpointLocalizedUnitDataW1301
    (endpointLocalizedUnitData :
      EndpointStrictExactLocalizedUnitDataProviderW949) :
    EndpointStrictExactLocalizedUnitDataProviderW949
    where
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      endpointLocalizedUnitData
  localizedUnitData :=
    localizedUnitDataOfEndpointLocalizedUnitDataW949
      endpointLocalizedUnitData

theorem repackEndpointLocalizedUnitDataW1301_eq
    (endpointLocalizedUnitData :
      EndpointStrictExactLocalizedUnitDataProviderW949) :
    repackEndpointLocalizedUnitDataW1301 endpointLocalizedUnitData =
      endpointLocalizedUnitData := by
  cases endpointLocalizedUnitData
  rfl

theorem w982FullDataEndpointStrictExactOfW983FullDataW1301
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData).endpointStrictExact =
      endpointStrictExactOfEndpointLocalizedUnitDataW949
        fullData.endpointLocalizedUnitData :=
  rfl

theorem w982FullDataLocalizedUnitDataOfW983FullDataW1301
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983) :
    (fullDataOfEndpointLocalizedUnitChoiceW983 fullData).localizedUnitData =
      localizedUnitDataOfEndpointLocalizedUnitDataW949
        fullData.endpointLocalizedUnitData :=
  rfl

structure MetrizableEndpointLocalizedUnitBoundaryUnpackGuardStateW1301 : Type where
  seed : String
  inspectedBoundary : String
  unpackedSurfaceCount : Nat
  primitiveRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitBoundaryUnpackGuardStateW1301 :
    MetrizableEndpointLocalizedUnitBoundaryUnpackGuardStateW1301 where
  seed := "w1301-endpoint-localized-unit-boundary-unpack-guard"
  inspectedBoundary :=
    "W983 canonical projections to endpoint strict-exact witnesses and W945\
      localized-unit data through W949 endpoint-localized-unit data"
  unpackedSurfaceCount :=
    canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301.length
  primitiveRouteSurfaceCount :=
    canonicalW949EndpointLocalizedUnitPrimitiveInputNamesW1301.length
  providerSearchResult :=
    "proved: canonical W983 endpoint-localized-unit unpacking exposes a\
      five-input full-data surface, and the W949 primitive route exposes a\
      four-input surface; repacking the W949 projections is the same provider,\
      so this boundary does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1301EndpointLocalizedUnitBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitBoundaryUnpackGuardStateW1301;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
