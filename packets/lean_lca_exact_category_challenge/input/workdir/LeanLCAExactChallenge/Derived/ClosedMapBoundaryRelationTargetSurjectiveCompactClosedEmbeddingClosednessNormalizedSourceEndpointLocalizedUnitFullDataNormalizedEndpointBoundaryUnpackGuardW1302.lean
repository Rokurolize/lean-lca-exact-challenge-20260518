import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointLocalizedUnitBoundaryUnpackGuardW1301

/-!
W1302 records the W950 normalized-source/endpoint-localized provider boundary
behind the W985 surface. Unpacking W950 exposes W948 normalized-source
triangulation data and W949 endpoint-localized-unit data; the primitive W950
route is still a three-input surface, so it does not close the remaining W987
obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW985NormalizedEndpointUnpackedInputNamesW1302 : List String :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985

theorem canonicalW985NormalizedEndpointUnpackedInputNamesW1302_count :
    canonicalW985NormalizedEndpointUnpackedInputNamesW1302.length = 3 :=
  normalizedSourceEndpointLocalizedUnitChoiceInputNamesW985_count

def canonicalW950NormalizedEndpointPrimitiveInputNamesW1302 : List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950

theorem canonicalW950NormalizedEndpointPrimitiveInputNamesW1302_count :
    canonicalW950NormalizedEndpointPrimitiveInputNamesW1302.length = 3 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950_count

def canonicalW950NormalizedEndpointInnerInputNamesW1302 : List String :=
  ["W948 normalized-source-triangulation data provider",
    "W949 endpoint-localized-unit data provider"]

theorem canonicalW950NormalizedEndpointInnerInputNamesW1302_count :
    canonicalW950NormalizedEndpointInnerInputNamesW1302.length = 2 :=
  rfl

theorem canonicalW985NormalizedEndpointUnpackExpandsCurrentSurfaceW1302 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW985NormalizedEndpointUnpackedInputNamesW1302.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW985NormalizedEndpointUnpackedInputNamesW1302_count]
  norm_num

theorem canonicalW950NormalizedEndpointPrimitiveRouteExpandsCurrentSurfaceW1302 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW950NormalizedEndpointPrimitiveInputNamesW1302.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW950NormalizedEndpointPrimitiveInputNamesW1302_count]
  norm_num

theorem canonicalW950NormalizedEndpointInnerUnpackExpandsCurrentSurfaceW1302 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW950NormalizedEndpointInnerInputNamesW1302.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW950NormalizedEndpointInnerInputNamesW1302_count]
  norm_num

def repackNormalizedSourceEndpointLocalizedUnitDataW1302
    (normalizedSourceEndpointLocalizedUnitData :
      NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
    where
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      normalizedSourceEndpointLocalizedUnitData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      normalizedSourceEndpointLocalizedUnitData

theorem repackNormalizedSourceEndpointLocalizedUnitDataW1302_eq
    (normalizedSourceEndpointLocalizedUnitData :
      NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950) :
    repackNormalizedSourceEndpointLocalizedUnitDataW1302
        normalizedSourceEndpointLocalizedUnitData =
      normalizedSourceEndpointLocalizedUnitData := by
  cases normalizedSourceEndpointLocalizedUnitData
  rfl

theorem w984FullDataEndpointLocalizedUnitOfW985FullDataW1302
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData).endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        fullData.normalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w984FullDataNormalizedSourceTriangulationOfW985FullDataW1302
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985 fullData).normalizedSourceTriangulationData =
      normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        fullData.normalizedSourceEndpointLocalizedUnitData :=
  rfl

structure MetrizableNormalizedEndpointBoundaryUnpackGuardStateW1302 : Type where
  seed : String
  inspectedBoundary : String
  unpackedSurfaceCount : Nat
  innerSurfaceCount : Nat
  primitiveRouteSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedEndpointBoundaryUnpackGuardStateW1302 :
    MetrizableNormalizedEndpointBoundaryUnpackGuardStateW1302 where
  seed := "w1302-normalized-endpoint-boundary-unpack-guard"
  inspectedBoundary :=
    "W950 canonical projections to W948 normalized-source-triangulation data\
      and W949 endpoint-localized-unit data"
  unpackedSurfaceCount :=
    canonicalW985NormalizedEndpointUnpackedInputNamesW1302.length
  innerSurfaceCount :=
    canonicalW950NormalizedEndpointInnerInputNamesW1302.length
  primitiveRouteSurfaceCount :=
    canonicalW950NormalizedEndpointPrimitiveInputNamesW1302.length
  providerSearchResult :=
    "proved: canonical W950 normalized-source/endpoint-localized unpacking\
      exposes a two-input provider boundary and a three-input primitive route;\
      repacking the W950 projections is the same provider, so this boundary\
      does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1302NormalizedEndpointBoundaryUnpackGuard_productSuccess :
    (let state :=
        currentMetrizableNormalizedEndpointBoundaryUnpackGuardStateW1302;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
