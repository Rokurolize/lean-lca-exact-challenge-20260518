import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W951 feeds the W950 normalized-source/endpoint-localized-unit route while
replacing the W947 target-no-univ/closedness provider and the W950
normalized-source/endpoint-localized-unit provider leaves by one combined
provider.
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
W951 target/closedness/normalized-source/endpoint-localized provider: package
the current W947 target-no-univ/closedness data with W950
normalized-source/endpoint-localized-unit data.
-/
structure TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951 :
    Type 2 where
  targetNoUnivClosednessData :
    TargetNoUnivMembershipClosednessDataProviderW947
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W951 projects W947 target-no-univ/closedness data. -/
def targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951
    (targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
      TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951) :
    TargetNoUnivMembershipClosednessDataProviderW947 :=
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData.targetNoUnivClosednessData

/-- W951 projects W950 normalized-source/endpoint-localized-unit data. -/
def normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951
    (targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
      TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData.normalizedSourceEndpointLocalizedUnitData

/--
W951 preserves W950's boundary/relation field while bundling
target-no-univ/closedness and normalized-source/endpoint-localized-unit data.
-/
structure MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951

/- W951 projects W950 leaves by unpacking target/closedness and normalized-source/endpoint data. -/
def w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldLeavesW950
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivClosednessData :=
    targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951
      leaves.targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951
      leaves.targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W951 W733 concrete leaves after projecting W950 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951
      leaves)

/-- W951 W732 route data after projecting W950 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsW950
    (w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951
      leaves)

/--
W951 exposes W950's route with target-no-univ/closedness data and
normalized-source/endpoint-localized-unit data consolidated into one provider.
-/
def closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W951 target-no-univ-closedness/normalized-source-endpoint-localized-unit\
      data provider: W947 target-no-univ/closedness data and W950\
      normalized-source/endpoint-localized-unit data"]

theorem closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951_count :
    closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951.length =
      2 :=
  rfl

/-- Current checked W951 state. -/
structure MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW951 :
    Type where
  seed : String
  declarations : List String
  targetNormalizedEndpointDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW951 :
    MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW951
    where
  seed :=
    "w951-closed-map-boundary-relation-data-target-no-univ-closedness-\
      normalized-source-triangulation-endpoint-localized-unit-data-\
      primitive-field-route"
  declarations :=
    ["TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951",
      "targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951",
      "normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataW951",
      "MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW951",
      "w950LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataBoundaryRelationDataFieldsW951",
      "concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951",
      "routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW951",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951_count"]
  targetNormalizedEndpointDataResult :=
    "proved: W951 projects one target-no-univ-closedness/normalized-source-\
      endpoint-localized-unit provider into W947 target-no-univ/closedness\
      data and W950 normalized-source/endpoint-localized-unit data for the\
      W950 route"
  exactAtResult :=
    "proved: closed-map boundary-relation-data target-no-univ-closedness\
      normalized-source-endpoint-localized-unit-data route feeds the W950/\
      W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/W935/W934/\
      W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W947 target-no-univ/closedness data and W950 normalized-source/endpoint-\
      localized-unit data replaced by W951 target-no-univ-closedness/\
      normalized-source-endpoint-localized-unit data provider",
      "W730 boundary/relation data remains explicit"]
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW951
  productSuccessClaimed := false

theorem currentW951ClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsRouteStateW951;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
