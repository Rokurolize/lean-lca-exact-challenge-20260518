import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute

/-!
W960 feeds the W959 source-triangulation-field route while replacing the bundled
W725 closedness branch provider by the two raw fields of its closed-map
constructor: selected-difference closed-map components and the mapped explicit
cokernel closed-map provider.
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
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W960 preserves the W959 field surface while splitting W725 closedness data
along the closed-map constructor branch.
-/
structure MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960 :
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
  globalClosedMapComponents :
    SelectedDifferenceClosedMapDiagramComponentProviderW718
  mappedCokernelClosedMapProvider :
    MappedExplicitCokernelClosedMapProviderW519
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

/-- W960 builds the W725 closed-map branch from its two raw fields. -/
def diagramAndMappedCokernelClosednessDataOfClosedMapFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725 :=
  .closedMap leaves.globalClosedMapComponents
    leaves.mappedCokernelClosedMapProvider

/-- W960 builds the W959 leaves consumed by the source-triangulation-field route. -/
def w959LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959
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
    diagramAndMappedCokernelClosednessDataOfClosedMapFieldsW960 leaves
  normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W960 constructs W958 leaves through W959. -/
def w958LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958 :=
  w958LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W957 leaves through W959/W958. -/
def w957LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW957 :=
  w957LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W956 leaves through W959/W958/W957. -/
def w956LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW956 :=
  w956LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W955 leaves through W959/W958/W957/W956. -/
def w955LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :=
  w955LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W954 leaves through W959/W958/W957/W956/W955. -/
def w954LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :=
  w954LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W953 primitive leaves through W959/W958/W957/W956/W955/W954. -/
def w953PrimitiveLeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 constructs W952 leaves through W959/W958/W957/W956/W955/W954/W953. -/
def w952LeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 W733 concrete leaves after constructing W959 leaves. -/
def concreteLeavesOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/-- W960 W732 route data after constructing W959 leaves. -/
def routeDataProviderOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

theorem directBoundedLeftCalculusOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

noncomputable def boundedDerivedInfinityCategoryOfClosedMapClosednessFieldsW960
    (leaves :
      MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationFieldsW959
    (w959LeavesOfClosedMapClosednessFieldsW960 leaves)

/--
W960 records the W959 field surface with W725 closedness data split along the
closed-map branch constructor.
-/
def closedMapClosednessFieldsInputNamesW960 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary proposition",
    "raw source-difference cokernel-pi-zero WPP-limit boundary proposition",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "W718 selected-difference closed-map diagram component provider",
    "W519 mapped explicit cokernel closed-map provider",
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

theorem closedMapClosednessFieldsInputNamesW960_count :
    closedMapClosednessFieldsInputNamesW960.length = 18 :=
  rfl

/-- Current checked W960 state. -/
structure MetrizableClosedMapClosednessFieldsRouteStateW960 :
    Type where
  seed : String
  declarations : List String
  closednessSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapClosednessFieldsRouteStateW960 :
    MetrizableClosedMapClosednessFieldsRouteStateW960
    where
  seed :=
    "w960-closed-map-raw-boundary-relation-fields-normalized-fixed-target-\
      source-triangulation-fields-closed-map-closedness-fields-split-target-\
      no-univ-closedness-normalized-endpoint-unit-components-primitive-fields-\
      route"
  declarations :=
    ["MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedMapClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW960",
      "diagramAndMappedCokernelClosednessDataOfClosedMapFieldsW960",
      "w959LeavesOfClosedMapClosednessFieldsW960",
      "w958LeavesOfClosedMapClosednessFieldsW960",
      "w957LeavesOfClosedMapClosednessFieldsW960",
      "w956LeavesOfClosedMapClosednessFieldsW960",
      "w955LeavesOfClosedMapClosednessFieldsW960",
      "w954LeavesOfClosedMapClosednessFieldsW960",
      "w953PrimitiveLeavesOfClosedMapClosednessFieldsW960",
      "w952LeavesOfClosedMapClosednessFieldsW960",
      "concreteLeavesOfClosedMapClosednessFieldsW960",
      "routeDataProviderOfClosedMapClosednessFieldsW960",
      "directBoundedLeftCalculusOfClosedMapClosednessFieldsW960",
      "boundedDerivedInfinityCategoryOfClosedMapClosednessFieldsW960",
      "closedMapClosednessFieldsInputNamesW960",
      "closedMapClosednessFieldsInputNamesW960_count"]
  closednessSplitResult :=
    "proved: W960 constructs the W725 closed-map branch from raw\
      selected-difference closed-map diagram components and the mapped explicit\
      cokernel closed-map provider"
  exactAtResult :=
    "proved: the W960 closed-map closedness field surface feeds the W959/W958/\
      W957/W956/W955/W954/W953/W952/W951/W950/W949/W948/W947/W946/W945/W944/\
      W943/W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable\
      ExactAt route"
  refinedInputs :=
    ["W725 closedness branch replaced on the closed-map path by W718\
      selected-difference closed-map components and W519 mapped explicit\
      cokernel closed-map provider",
      "the W725 closed-embedding constructor remains a separate branch, and\
      endpoint strict-exact witnesses, split target primitives, raw W716\
      boundary propositions, raw W717 relation providers, raw W719 normalized\
      fixed-target fields, raw W722 source-triangulation fields, and raw\
      right-adjoint/adjunction/W939 unit component fields remain explicit"]
  remainingInputs := closedMapClosednessFieldsInputNamesW960
  productSuccessClaimed := false

theorem currentW960ClosedMapClosednessFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapClosednessFieldsRouteStateW960;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
