import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W952 feeds the W951 target/closedness/normalized-source/endpoint-localized
route while replacing the remaining W730 boundary/relation provider and W951
target/closedness/normalized-source/endpoint-localized provider leaves by one
current full-provider.
-/

set_option autoImplicit false
set_option linter.style.longLine false

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
W952 full current provider: package the remaining W730 boundary/relation data
with W951 target/closedness/normalized-source/endpoint-localized data.
-/
structure BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951

/-- W952 projects W730 boundary/relation data. -/
def boundaryRelationDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952
    (boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData.boundaryRelationData

/-- W952 projects W951 target/closedness/normalized-source/endpoint-localized data. -/
def targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952
    (boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952) :
    TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951 :=
  boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData.targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData

/--
W952 exposes W951's two remaining fields as one current full-provider field.
-/
structure MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :
    Type 2 where
  boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
    BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952

/- W952 projects W951 leaves by unpacking the current full-provider. -/
def w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (leaves :
      MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951
    where
  boundaryRelationData :=
    boundaryRelationDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952
      leaves.boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952
      leaves.boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W952 W733 concrete leaves after projecting W951 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (leaves :
      MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
      leaves)

/-- W952 W732 route data after projecting W951 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (leaves :
      MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (leaves :
      MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (leaves :
      MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
      leaves)

/--
W952 exposes W951's route with all remaining current closed-map data
consolidated into one provider.
-/
def closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952 :
    List String :=
  ["W952 boundary-relation/target-no-univ-closedness/normalized-source-\
      endpoint-localized-unit data provider: W730 boundary/relation data and\
      W951 target-no-univ-closedness/normalized-source-endpoint-localized-unit\
      data"]

theorem closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952_count :
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952.length =
      1 :=
  rfl

/-- Current checked W952 state. -/
structure MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW952 :
    Type where
  seed : String
  declarations : List String
  fullProviderResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW952 :
    MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW952
    where
  seed :=
    "w952-closed-map-boundary-relation-target-no-univ-closedness-\
      normalized-source-triangulation-endpoint-localized-unit-data-\
      primitive-field-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952",
      "boundaryRelationDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952",
      "targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW952",
      "MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952",
      "w951LeavesOfBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952",
      "concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952",
      "routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952_count"]
  fullProviderResult :=
    "proved: W952 projects one current full-provider into W730 boundary/\
      relation data and W951 target-no-univ-closedness/normalized-source-\
      endpoint-localized-unit data for the W951 route"
  exactAtResult :=
    "proved: closed-map boundary-relation target-no-univ-closedness\
      normalized-source-endpoint-localized-unit-data route feeds the W951/\
      W950/W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/W935/\
      W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W730 boundary/relation data and W951 target-no-univ-closedness/\
      normalized-source-endpoint-localized-unit data replaced by W952\
      current full-provider"]
  remainingInputs :=
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952
  productSuccessClaimed := false

theorem currentW952ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW952;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
