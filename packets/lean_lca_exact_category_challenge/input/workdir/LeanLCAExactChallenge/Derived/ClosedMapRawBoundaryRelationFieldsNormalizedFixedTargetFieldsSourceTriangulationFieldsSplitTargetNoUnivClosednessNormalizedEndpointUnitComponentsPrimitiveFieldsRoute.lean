import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute

/-!
W959 feeds the W958 normalized-field route while replacing the bundled W722
source-triangulation provider by its three raw constructor fields:
source pretriangulated, source triangulated, and source-side triangle completion.
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
W959 preserves the W958 field surface while splitting W722 source-triangulation
data into source pretriangulated, triangulated, and triangle-completion fields.
-/
structure MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959 :
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
  sourcePretriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
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

/-- W959 builds W722 source-triangulation data from the three raw fields. -/
def sourceTriangulationDataOfFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppSourceTriangulationDataProviderW722
    where
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion

/-- W959 builds the W958 leaves consumed by the normalized-field route. -/
def w958LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958
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
  normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourceTriangulationData := sourceTriangulationDataOfFieldsW959 leaves
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W959 constructs W957 leaves through W958 after building W722 data. -/
def w957LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW957 :=
  w957LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 constructs W956 leaves through W958/W957. -/
def w956LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW956 :=
  w956LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 constructs W955 leaves through W958/W957/W956. -/
def w955LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :=
  w955LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 constructs W954 leaves through W958/W957/W956/W955. -/
def w954LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :=
  w954LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 constructs W953 primitive leaves through W958/W957/W956/W955/W954. -/
def w953PrimitiveLeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 constructs W952 leaves through W958/W957/W956/W955/W954/W953. -/
def w952LeavesOfSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 W733 concrete leaves after constructing W958 leaves. -/
def concreteLeavesOfClosedMapSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/-- W959 W732 route data after constructing W958 leaves. -/
def routeDataProviderOfClosedMapSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

theorem directBoundedLeftCalculusOfClosedMapSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

noncomputable def boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationFieldsW959
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW958
    (w958LeavesOfSourceTriangulationFieldsW959 leaves)

/--
W959 records the W958 field surface with W722 source-triangulation data split
into source pretriangulated, source triangulated, and triangle-completion data.
-/
def closedMapSourceTriangulationFieldsInputNamesW959 :
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
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict components\
      (closed inclusion, open map, surjectivity, algebraic exactness) plus\
      isomorphism"]

theorem closedMapSourceTriangulationFieldsInputNamesW959_count :
    closedMapSourceTriangulationFieldsInputNamesW959.length = 17 :=
  rfl

/-- Current checked W959 state. -/
structure MetrizableClosedMapSourceTriangulationFieldsRouteStateW959 :
    Type where
  seed : String
  declarations : List String
  sourceSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapSourceTriangulationFieldsRouteStateW959 :
    MetrizableClosedMapSourceTriangulationFieldsRouteStateW959
    where
  seed :=
    "w959-closed-map-raw-boundary-relation-fields-normalized-fixed-target-\
      source-triangulation-fields-split-target-no-univ-closedness-normalized-\
      endpoint-unit-components-primitive-fields-route"
  declarations :=
    ["MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959",
      "sourceTriangulationDataOfFieldsW959",
      "w958LeavesOfSourceTriangulationFieldsW959",
      "w957LeavesOfSourceTriangulationFieldsW959",
      "w956LeavesOfSourceTriangulationFieldsW959",
      "w955LeavesOfSourceTriangulationFieldsW959",
      "w954LeavesOfSourceTriangulationFieldsW959",
      "w953PrimitiveLeavesOfSourceTriangulationFieldsW959",
      "w952LeavesOfSourceTriangulationFieldsW959",
      "concreteLeavesOfClosedMapSourceTriangulationFieldsW959",
      "routeDataProviderOfClosedMapSourceTriangulationFieldsW959",
      "directBoundedLeftCalculusOfClosedMapSourceTriangulationFieldsW959",
      "boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationFieldsW959",
      "closedMapSourceTriangulationFieldsInputNamesW959",
      "closedMapSourceTriangulationFieldsInputNamesW959_count"]
  sourceSplitResult :=
    "proved: W959 constructs W722 source-triangulation data from raw\
      source-pretriangulated, source-triangulated, and source-side\
      triangle-completion fields"
  exactAtResult :=
    "proved: the W959 source-triangulation field surface feeds the W958/W957/\
      W956/W955/W954/W953/W952/W951/W950/W949/W948/W947/W946/W945/W944/W943/\
      W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable ExactAt\
      route"
  refinedInputs :=
    ["W722 source-triangulation data replaced by raw source pretriangulated,\
      source triangulated, and source-side triangle-completion fields",
      "W725 closedness data, endpoint strict-exact witnesses, split target\
      primitives, raw W716 boundary propositions, raw W717 relation providers,\
      raw W719 normalized fixed-target fields, and raw right-adjoint/adjunction/\
      W939 unit component fields remain explicit"]
  remainingInputs := closedMapSourceTriangulationFieldsInputNamesW959
  productSuccessClaimed := false

theorem currentW959ClosedMapSourceTriangulationFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapSourceTriangulationFieldsRouteStateW959;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
