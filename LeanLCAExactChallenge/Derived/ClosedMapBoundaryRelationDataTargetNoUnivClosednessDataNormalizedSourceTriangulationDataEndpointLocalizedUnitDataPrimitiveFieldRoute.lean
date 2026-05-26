import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute

/-!
W949 feeds the W948 normalized-source-triangulation route while replacing the
separate endpoint strict-exact witness and W945 localized-unit data leaves by
one endpoint-localized-unit provider.
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
W949 endpoint/localized-unit provider: package the current endpoint strict
short-exact witness with the W945 localized-unit data provider.
-/
structure EndpointStrictExactLocalizedUnitDataProviderW949 : Type 2 where
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/-- W949 projects endpoint strict short-exact witnesses. -/
def endpointStrictExactOfEndpointLocalizedUnitDataW949
    (endpointLocalizedUnitData :
      EndpointStrictExactLocalizedUnitDataProviderW949) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointLocalizedUnitData.endpointStrictExact

/-- W949 projects the W945 localized-unit data provider. -/
def localizedUnitDataOfEndpointLocalizedUnitDataW949
    (endpointLocalizedUnitData :
      EndpointStrictExactLocalizedUnitDataProviderW949) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  endpointLocalizedUnitData.localizedUnitData

/--
W949 preserves W948's boundary/relation, target-no-univ/closedness, and
normalized-source-triangulation fields, while bundling endpoint strict-exact
and localized-unit data.
-/
structure MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessData :
    TargetNoUnivMembershipClosednessDataProviderW947
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  endpointLocalizedUnitData :
    EndpointStrictExactLocalizedUnitDataProviderW949

/- W949 projects W948 leaves by unpacking endpoint/localized-unit data. -/
def w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivClosednessData := leaves.targetNoUnivClosednessData
  normalizedSourceTriangulationData := leaves.normalizedSourceTriangulationData
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      leaves.endpointLocalizedUnitData
  localizedUnitData :=
    localizedUnitDataOfEndpointLocalizedUnitDataW949
      leaves.endpointLocalizedUnitData

/-- W949 W733 concrete leaves after projecting W948 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
      leaves)

/-- W949 W732 route data after projecting W948 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949
      leaves)

/--
W949 exposes W948's route with endpoint strict-exact witnesses and localized
unit data consolidated into one provider.
-/
def closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W947 target-no-univ/closedness data provider: W944 target no-univ data\
      and W725 selected-difference and mapped-cokernel closedness branch data",
    "W948 normalized-source-triangulation data provider: W719 normalized\
      fixed-target data and W722 source-side triangulation data",
    "W949 endpoint-localized-unit data provider: endpoint strict short-exact\
      witnesses and W945 localized-unit data"]

theorem closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949_count :
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949.length =
      4 :=
  rfl

/-- Current checked W949 state. -/
structure MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsRouteStateW949 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedUnitDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsRouteStateW949 :
    MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsRouteStateW949
    where
  seed :=
    "w949-closed-map-boundary-relation-data-target-no-univ-closedness-data-\
      normalized-source-triangulation-data-endpoint-localized-unit-data-\
      primitive-field-route"
  declarations :=
    ["EndpointStrictExactLocalizedUnitDataProviderW949",
      "endpointStrictExactOfEndpointLocalizedUnitDataW949",
      "localizedUnitDataOfEndpointLocalizedUnitDataW949",
      "MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldLeavesW949",
      "w948LeavesOfEndpointLocalizedUnitDataBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataFieldsW949",
      "concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949",
      "routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsW949",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949_count"]
  endpointLocalizedUnitDataResult :=
    "proved: W949 projects one endpoint-localized-unit provider into endpoint\
      strict short-exact witnesses and W945 localized-unit data for the W948\
      route"
  exactAtResult :=
    "proved: closed-map boundary-relation-data target-no-univ-closedness-data\
      normalized-source-triangulation-data endpoint-localized-unit-data route\
      feeds the W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/\
      W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["endpoint strict-exact witnesses and W945 localized-unit data replaced by\
      W949 endpoint-localized-unit data provider",
      "W730 boundary/relation data, W947 target-no-univ/closedness data, and\
      W948 normalized-source-triangulation data remain explicit"]
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949
  productSuccessClaimed := false

theorem currentW949ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsRouteStateW949;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
