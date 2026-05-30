import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFromPrimitiveFieldsRoute

/-!
W954 feeds the W953 W945-primitive-leaf constructor while replacing the W945
localized-unit data provider by the raw W944 right-adjoint, adjunction, and
W939 unit strict-exact component fields.
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
W954 constructs W945 localized-unit data from the raw W944 right adjoint,
adjunction, and W939 unit component witness fields.
-/
def localizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945
    where
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W954 builds the W945 primitive-leaf surface consumed by W953. -/
def w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetNoUnivData := leaves.targetNoUnivData
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  localizedUnitData :=
    localizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves

/-- W954 constructs W952 leaves through W953 after building W945 localized-unit data. -/
def w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves)

/-- W954 W733 concrete leaves after constructing W953/W952 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves)

/-- W954 W732 route data after constructing W953/W952 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitPrimitiveFieldsW953
    (w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
      leaves)

/--
W954 records the W944 unit-component primitive surface feeding W953.
-/
def closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954 :
    List String :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944

theorem closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954_count :
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954.length =
      10 :=
  closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW944_count

/-- Current checked W954 state. -/
structure MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW954 :
    Type where
  seed : String
  declarations : List String
  localizedUnitConstructionResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW954 :
    MetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW954
    where
  seed :=
    "w954-closed-map-boundary-relation-target-no-univ-closedness-normalized-\
      source-endpoint-unit-components-primitive-fields-route"
  declarations :=
    ["localizedUnitDataOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954",
      "closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954_count"]
  localizedUnitConstructionResult :=
    "proved: W954 constructs W945 localized-unit data from the W944 raw\
      right adjoint, localized adjunction, and W939 unit component witness"
  exactAtResult :=
    "proved: the W954 unit-component surface feeds the W953/W952/W951/W950/\
      W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/W935/W934/\
      W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W945 localized-unit data replaced by right adjoint, localized\
      adjunction, and W939 unit strict-exact component witness",
      "W716 boundary data, W717 relation data, W944 target no-univ data, W725\
      closedness data, W719 normalized fixed-target data, W722 source data,\
      and endpoint strict-exact witnesses remain explicit"]
  remainingInputs :=
    closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW954
  productSuccessClaimed := false

theorem currentW954ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW954;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
