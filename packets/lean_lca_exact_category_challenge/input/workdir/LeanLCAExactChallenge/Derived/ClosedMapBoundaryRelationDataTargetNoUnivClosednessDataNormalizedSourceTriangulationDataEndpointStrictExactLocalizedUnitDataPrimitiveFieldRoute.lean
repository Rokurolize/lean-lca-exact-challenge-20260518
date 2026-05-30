import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute

/-!
W948 feeds the W947 target-no-univ/closedness route while replacing the
separate W719 normalized fixed-target data and W722 source-triangulation data
leaves by one normalized-source-triangulation provider.
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
W948 normalized/source-triangulation provider: package W719 normalized
fixed-target data with W722 source-side triangulation data.
-/
structure NormalizedFixedTargetSourceTriangulationDataProviderW948 : Type 2 where
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722

/-- W948 projects W719 normalized fixed-target data. -/
def normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
    (normalizedSourceData :
      NormalizedFixedTargetSourceTriangulationDataProviderW948) :
    MetrizableWppNormalizedFixedTargetDataProviderW719 :=
  normalizedSourceData.normalizedFixedTargetData

/-- W948 projects W722 source-triangulation data. -/
def sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
    (normalizedSourceData :
      NormalizedFixedTargetSourceTriangulationDataProviderW948) :
    MetrizableWppSourceTriangulationDataProviderW722 :=
  normalizedSourceData.sourceTriangulationData

/--
W948 preserves W947's boundary/relation, target-no-univ/closedness, endpoint
strict-exact, and localized-unit fields, while bundling normalized fixed-target
and source-triangulation data.
-/
structure MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessData :
    TargetNoUnivMembershipClosednessDataProviderW947
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/- W948 projects W947 leaves by unpacking normalized/source-triangulation data. -/
def w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivClosednessData := leaves.targetNoUnivClosednessData
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
      leaves.normalizedSourceTriangulationData
  sourceTriangulationData :=
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
      leaves.normalizedSourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  localizedUnitData := leaves.localizedUnitData

/-- W948 W733 concrete leaves after projecting W947 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
      leaves)

/-- W948 W732 route data after projecting W947 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948
      leaves)

/--
W948 exposes W947's route with normalized fixed-target data and source-side
triangulation data consolidated into one provider.
-/
def closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W947 target-no-univ/closedness data provider: W944 target no-univ data\
      and W725 selected-difference and mapped-cokernel closedness branch data",
    "W948 normalized-source-triangulation data provider: W719 normalized\
      fixed-target data and W722 source-side triangulation data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "W945 localized-unit data provider: right adjoint, adjunction, and unit\
      mapping-cone strict-exact component witness"]

theorem closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948_count :
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948.length =
      5 :=
  rfl

/-- Current checked W948 state. -/
structure MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsRouteStateW948 :
    Type where
  seed : String
  declarations : List String
  normalizedSourceDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsRouteStateW948 :
    MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsRouteStateW948
    where
  seed :=
    "w948-closed-map-boundary-relation-data-target-no-univ-closedness-data-\
      normalized-source-triangulation-data-endpoint-strict-exact-localized-\
      unit-data-primitive-field-route"
  declarations :=
    ["NormalizedFixedTargetSourceTriangulationDataProviderW948",
      "normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948",
      "sourceTriangulationDataOfNormalizedSourceTriangulationDataW948",
      "MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldLeavesW948",
      "w947LeavesOfNormalizedSourceTriangulationDataBoundaryRelationDataTargetNoUnivClosednessDataEndpointStrictExactLocalizedUnitDataFieldsW948",
      "concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948",
      "routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsW948",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948_count"]
  normalizedSourceDataResult :=
    "proved: W948 projects one normalized-source-triangulation provider into\
      W719 normalized fixed-target data and W722 source-triangulation data\
      for the W947 route"
  exactAtResult :=
    "proved: closed-map boundary-relation-data target-no-univ-closedness-data\
      normalized-source-triangulation-data endpoint-strict-exact\
      localized-unit-data route feeds the W947/W946/W945/W944/W943/W942/\
      W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W719 normalized fixed-target data and W722 source-triangulation data\
      replaced by W948 normalized-source-triangulation data provider",
      "W730 boundary/relation data, W947 target-no-univ/closedness data,\
      endpoint strict-exact witnesses, and W945 localized-unit data remain\
      explicit"]
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsInputNamesW948
  productSuccessClaimed := false

theorem currentW948ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataFieldsRouteStateW948;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
