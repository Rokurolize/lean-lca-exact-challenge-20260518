import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute

/-!
W958 feeds the W957 relation-field route while replacing the bundled W719
normalized fixed-target provider by its three raw constructor fields:
normalized strict-representative lift blueprint, target fixed-target uniqueness,
and localization-model fixed-target uniqueness.
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
W958 preserves the W957 field surface while splitting W719 normalized
fixed-target data into its normalized-lift and fixed-target uniqueness fields.
-/
structure MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactNoUnivMembershipProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/-- W958 builds W719 normalized fixed-target data from the three raw fields. -/
def normalizedFixedTargetDataOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppNormalizedFixedTargetDataProviderW719
    where
  normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq := leaves.localizationModelFixedTargetUniq

/-- W958 builds the W957 leaves consumed by the relation-field route. -/
def w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW957
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    leaves.targetCodomainCompactNoUnivMembershipProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W958 constructs W956 leaves through W957 after building W719 data. -/
def w956LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW956 :=
  w956LeavesOfRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 constructs W955 leaves through W957/W956. -/
def w955LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :=
  w955LeavesOfRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 constructs W954 leaves through W957/W956/W955. -/
def w954LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :=
  w954LeavesOfRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 constructs W953 primitive leaves through W957/W956/W955/W954. -/
def w953PrimitiveLeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 constructs W952 leaves through W957/W956/W955/W954/W953. -/
def w952LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 W733 concrete leaves after constructing W957 leaves. -/
def concreteLeavesOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/-- W958 W732 route data after constructing W957 leaves. -/
def routeDataProviderOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW957
    (w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
      leaves)

/--
W958 records the W957 field surface with W719 normalized fixed-target data split
into the normalized lift blueprint and two fixed-target uniqueness obligations.
-/
def closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary proposition",
    "raw source-difference cokernel-pi-zero WPP-limit boundary proposition",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "W725 selected-difference and mapped-cokernel closedness branch: closed map\
      or closed embedding data",
    "normalized strict-representative lift blueprint for WPP diagrams and maps",
    "target fixed-target uniqueness for the WPP objectwise localization functor",
    "localization-model fixed-target uniqueness for the WPP objectwise\
      localization functor",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict components\
      (closed inclusion, open map, surjectivity, algebraic exactness) plus\
      isomorphism"]

theorem closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958_count :
    closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958.length =
      15 :=
  rfl

/-- Current checked W958 state. -/
structure MetrizableClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW958 :
    Type where
  seed : String
  declarations : List String
  normalizedSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW958 :
    MetrizableClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW958
    where
  seed :=
    "w958-closed-map-raw-boundary-relation-fields-normalized-fixed-target-\
      fields-split-target-no-univ-closedness-normalized-source-endpoint-unit-\
      components-primitive-fields-route"
  declarations :=
    ["MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958",
      "normalizedFixedTargetDataOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w956LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w955LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w954LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w953PrimitiveLeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "w952LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "concreteLeavesOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "routeDataProviderOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "directBoundedLeftCalculusOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "boundedDerivedInfinityCategoryOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958",
      "closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958",
      "closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958_count"]
  normalizedSplitResult :=
    "proved: W958 constructs W719 normalized fixed-target data from raw\
      normalized-lift blueprint, target fixed-target uniqueness, and\
      localization-model fixed-target uniqueness fields"
  exactAtResult :=
    "proved: the W958 raw-boundary relation-field normalized-field surface\
      feeds the W957/W956/W955/W954/W953/W952/W951/W950/W949/W948/W947/W946/\
      W945/W944/W943/W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/W930\
      stable ExactAt route"
  refinedInputs :=
    ["W719 normalized fixed-target data replaced by raw normalized-lift\
      blueprint, target fixed-target uniqueness, and localization-model\
      fixed-target uniqueness fields",
      "W725 closedness data, W722 source data, endpoint strict-exact\
      witnesses, split target primitives, raw W716 boundary propositions, raw\
      W717 relation providers, and raw right-adjoint/adjunction/W939 unit\
      component fields remain explicit"]
  remainingInputs :=
    closedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW958
  productSuccessClaimed := false

theorem currentW958ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW958;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
