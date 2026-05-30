import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute

/-!
W947 feeds the W946 closed-map boundary/relation route while replacing the
separate W944 target no-univ data and W725 closedness data leaves by one
target-no-univ/closedness provider, mirroring the older W729 target/closedness
shape without reintroducing W715 target compactness.
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
W947 target-no-univ/closedness provider: package the W944 target no-univ data
with the W725 matched selected-difference and mapped-cokernel closedness branch.
-/
structure TargetNoUnivMembershipClosednessDataProviderW947 : Type 2 where
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725

/-- W947 projects W944 target no-univ data. -/
def targetNoUnivDataOfTargetNoUnivClosednessDataW947
    (targetClosednessData :
      TargetNoUnivMembershipClosednessDataProviderW947) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetClosednessData.targetNoUnivData

/-- W947 projects W725 diagram and mapped-cokernel closedness data. -/
def diagramAndMappedCokernelClosednessDataOfTargetNoUnivClosednessDataW947
    (targetClosednessData :
      TargetNoUnivMembershipClosednessDataProviderW947) :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725 :=
  targetClosednessData.diagramAndMappedCokernelClosednessData

/--
W947 preserves W946's boundary/relation, normalized fixed-target,
source-triangulation, endpoint strict-exact, and localized-unit fields, while
bundling the target no-univ and closedness leaves.
-/
structure MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivClosednessData :
    TargetNoUnivMembershipClosednessDataProviderW947
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/- W947 projects W946 leaves by unpacking the target-no-univ/closedness data. -/
def w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfTargetNoUnivClosednessDataW947
      leaves.targetNoUnivClosednessData
  diagramAndMappedCokernelClosednessData :=
    diagramAndMappedCokernelClosednessDataOfTargetNoUnivClosednessDataW947
      leaves.targetNoUnivClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  localizedUnitData := leaves.localizedUnitData

/-- W947 W733 concrete leaves after projecting W946 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
      leaves)

/-- W947 W732 route data after projecting W946 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    (leaves :
      MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
    (w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
      leaves)

/--
W947 exposes W946's route with target no-univ data and matched closedness data
consolidated into one provider.
-/
def closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W947 target-no-univ/closedness data provider: W944 target no-univ data\
      and W725 selected-difference and mapped-cokernel closedness branch data",
    "W719 normalized fixed-target data provider: normalized strict-representative\
      lift blueprint, target fixed-target uniqueness, and localization-model\
      fixed-target uniqueness",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "W945 localized-unit data provider: right adjoint, adjunction, and unit\
      mapping-cone strict-exact component witness"]

theorem closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947_count :
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947.length =
      6 :=
  rfl

/-- Current checked W947 state. -/
structure MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW947 :
    Type where
  seed : String
  declarations : List String
  targetClosednessDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW947 :
    MetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW947
    where
  seed :=
    "w947-closed-map-boundary-relation-data-target-no-univ-closedness-data-\
      normalized-fixed-target-data-source-triangulation-endpoint-strict-exact-\
      localized-unit-data-primitive-field-route"
  declarations :=
    ["TargetNoUnivMembershipClosednessDataProviderW947",
      "targetNoUnivDataOfTargetNoUnivClosednessDataW947",
      "diagramAndMappedCokernelClosednessDataOfTargetNoUnivClosednessDataW947",
      "MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947",
      "w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947",
      "concreteLeavesOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947",
      "routeDataProviderOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947",
      "closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947_count"]
  targetClosednessDataResult :=
    "proved: W947 projects one target-no-univ/closedness provider into W944\
      target no-univ data and W725 closedness data for the W946 route"
  exactAtResult :=
    "proved: closed-map boundary-relation-data target-no-univ-closedness-data\
      normalized-fixed-target-data source-triangulation endpoint-strict-exact\
      localized-unit-data route feeds the W946/W945/W944/W943/W942/W941/W940/\
      W937/W936/W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W944 target no-univ data and W725 closedness data replaced by W947\
      target-no-univ/closedness data provider",
      "W730 boundary/relation data, W719 normalized fixed-target data, W722\
      source-triangulation data, endpoint strict-exact witnesses, and W945\
      localized-unit data remain explicit"]
  remainingInputs :=
    closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947
  productSuccessClaimed := false

theorem currentW947ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW947;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
