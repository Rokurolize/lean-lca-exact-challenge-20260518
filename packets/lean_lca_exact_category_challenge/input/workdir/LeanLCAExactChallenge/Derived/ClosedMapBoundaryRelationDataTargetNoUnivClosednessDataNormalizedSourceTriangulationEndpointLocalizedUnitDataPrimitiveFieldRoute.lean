import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W950 feeds the W949 endpoint-localized-unit route while replacing the W948
normalized-source-triangulation provider and W949 endpoint-localized-unit
provider leaves by one normalized-source/endpoint-localized-unit provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484

namespace Dbounded

/--
W950 normalized-source/endpoint-localized-unit provider: package the current
W948 normalized-source-triangulation data with W949 endpoint-localized-unit
data.
-/
structure NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :
    Type 2 where
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  endpointLocalizedUnitData :
    EndpointStrictExactLocalizedUnitDataProviderW949

/-- W950 projects W948 normalized-source-triangulation data. -/
def normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    (normalizedSourceEndpointLocalizedUnitData :
      NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceEndpointLocalizedUnitData.normalizedSourceTriangulationData

/-- W950 projects W949 endpoint-localized-unit data. -/
def endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    (normalizedSourceEndpointLocalizedUnitData :
      NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  normalizedSourceEndpointLocalizedUnitData.endpointLocalizedUnitData

/--
W950 preserves W949's boundary/relation and target-no-univ/closedness fields,
while bundling normalized-source-triangulation and endpoint-localized-unit
data.
-/
structure MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessData :
    TargetNoUnivMembershipClosednessDataProviderW947
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/- W950 projects W949 leaves by unpacking normalized-source/endpoint data. -/
def w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivClosednessData := leaves.targetNoUnivClosednessData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      leaves.normalizedSourceEndpointLocalizedUnitData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      leaves.normalizedSourceEndpointLocalizedUnitData

/-- W950 W733 concrete leaves after projecting W949 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950
      leaves)

/-- W950 W732 route data after projecting W949 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950
      leaves)

/--
W950 exposes W949's route with normalized-source-triangulation data and
endpoint-localized-unit data consolidated into one provider.
-/
def closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W947 target-no-univ/closedness data provider: W944 target no-univ data\
      and W725 selected-difference and mapped-cokernel closedness branch data",
    "W950 normalized-source/endpoint-localized-unit data provider: W948\
      normalized-source-triangulation data and W949 endpoint-localized-unit\
      data"]

theorem closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950_count :
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950.length =
      3 :=
  rfl

/-- Current checked W950 state. -/
structure MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsRouteStateW950 :
    Type where
  seed : String
  declarations : List String
  normalizedEndpointDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsRouteStateW950 :
    MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsRouteStateW950
    where
  seed :=
    "w950-closed-map-boundary-relation-data-target-no-univ-closedness-data-\
      normalized-source-triangulation-endpoint-localized-unit-data-\
      primitive-field-route"
  declarations :=
    ["NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950",
      "normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950",
      "endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950",
      "MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950",
      "w949LeavesOfNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataFieldsW950",
      "concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950",
      "routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950_count"]
  normalizedEndpointDataResult :=
    "proved: W950 projects one normalized-source/endpoint-localized-unit\
      provider into W948 normalized-source-triangulation data and W949\
      endpoint-localized-unit data for the W949 route"
  exactAtResult :=
    "proved: closed-map boundary-relation-data target-no-univ-closedness-data\
      normalized-source-triangulation-endpoint-localized-unit-data route\
      feeds the W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/\
      W936/W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W948 normalized-source-triangulation data and W949 endpoint-localized\
      unit data replaced by W950 normalized-source/endpoint-localized-unit\
      data provider",
      "W730 boundary/relation data and W947 target-no-univ/closedness data\
      remain explicit"]
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950
  productSuccessClaimed := false

theorem currentW950ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsRouteStateW950;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
