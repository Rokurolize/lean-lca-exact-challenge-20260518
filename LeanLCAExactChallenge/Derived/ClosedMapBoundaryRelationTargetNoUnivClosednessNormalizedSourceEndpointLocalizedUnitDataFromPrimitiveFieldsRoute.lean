import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W953 constructs the W952 current full-provider from the existing W945
primitive-field leaf surface. This opens the W952 provider into its current
boundary/relation, target-no-univ/closedness, normalized-source, and
endpoint-localized-unit components without claiming that those primitive
fields have been instantiated.
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

/-- W953 constructs W730 boundary/relation data from the W945 primitive leaves. -/
def boundaryRelationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppBoundaryRelationDataProviderW730
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData

/-- W953 constructs W947 target-no-univ/closedness data from the W945 primitive leaves. -/
def targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    TargetNoUnivMembershipClosednessDataProviderW947
    where
  targetNoUnivData := leaves.targetNoUnivData
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData

/-- W953 constructs W948 normalized-source data from the W945 primitive leaves. -/
def normalizedSourceTriangulationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
    where
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData

/-- W953 constructs W949 endpoint-localized-unit data from the W945 primitive leaves. -/
def endpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    EndpointStrictExactLocalizedUnitDataProviderW949
    where
  endpointStrictExact := leaves.endpointStrictExact
  localizedUnitData := leaves.localizedUnitData

/-- W953 constructs W950 normalized-source/endpoint-localized data from W945 primitive leaves. -/
def normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
    where
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves

/-- W953 constructs W951 target/closedness/normalized-source/endpoint-localized data. -/
def targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951
    where
  targetNoUnivClosednessData :=
    targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves

/-- W953 constructs the W952 full current provider from W945 primitive leaves. -/
def boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952
    where
  boundaryRelationData :=
    boundaryRelationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves
  targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953
      leaves

/-- W953 feeds W952 by constructing the single W952 provider from W945 primitive leaves. -/
def w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952
    where
  boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitData :=
    boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953
      leaves

/-- W953 W733 concrete leaves after constructing W952 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves)

/-- W953 W732 route data after constructing W952 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsW952
    (w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
      leaves)

/--
W953 records the primitive leaves that construct W952's single current provider.
-/
def closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953 :
    List String :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945

theorem closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953_count :
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953.length =
      8 :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945_count

/-- Current checked W953 state. -/
structure MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsRouteStateW953 :
    Type where
  seed : String
  declarations : List String
  providerConstructionResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsRouteStateW953 :
    MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsRouteStateW953
    where
  seed :=
    "w953-closed-map-boundary-relation-target-no-univ-closedness-normalized-\
      source-endpoint-localized-unit-provider-from-primitive-fields-route"
  declarations :=
    ["boundaryRelationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "targetNoUnivClosednessDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "normalizedSourceTriangulationDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "endpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "normalizedSourceEndpointLocalizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "targetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953",
      "boundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataOfPrimitiveFieldsW953",
      "w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953_count"]
  providerConstructionResult :=
    "proved: W953 constructs the W952 full current provider from the W945\
      primitive-field leaf surface"
  exactAtResult :=
    "proved: the W953 primitive-field constructor feeds the W952/W951/W950/\
      W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/W935/W934/\
      W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W952 full current provider replaced by an explicit constructor from\
      W945 primitive leaves",
      "W733 old concrete leaves were inspected but do not directly construct\
      W952 because W945 localized-unit data is stronger than W721 localized\
      right-adjoint data"]
  remainingInputs :=
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsInputNamesW953
  productSuccessClaimed := false

theorem currentW953ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsRouteStateW953;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
