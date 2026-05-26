import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFromUnitComponentsPrimitiveFieldsRoute

/-!
W955 feeds the W954 unit-component route while replacing the bundled W944
target no-univ provider by the two target primitives already exposed by W943:
target-difference surjectivity and target-codomain compact no-univ membership.
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
W955 preserves the W954 field surface while splitting W944 target no-univ data
into target-difference surjectivity and target-codomain compact no-univ
membership primitives.
-/
structure MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactNoUnivMembershipProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
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

/-- W955 builds W944 target no-univ data from the two split target primitives. -/
def targetNoUnivDataOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  fun Y =>
    ⟨leaves.targetDifferenceSurjectiveForTargetProvider Y,
      leaves.targetCodomainCompactNoUnivMembershipProvider Y⟩

/-- W955 builds the W944 leaves consumed by W954. -/
def w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetNoUnivData :=
    targetNoUnivDataOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    leaves.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/-- W955 constructs W953 primitive leaves through W954 after building W944 leaves. -/
def w953PrimitiveLeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

/-- W955 constructs W952 leaves through W954/W953. -/
def w952LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

/-- W955 W733 concrete leaves after constructing W954 leaves. -/
def concreteLeavesOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

/-- W955 W732 route data after constructing W954 leaves. -/
def routeDataProviderOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
    (leaves :
      MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW954
    (w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955
      leaves)

/--
W955 records the W954 field surface with W944 target no-univ data split back
into the two target primitives used by W943.
-/
def closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955 :
    List String :=
  closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943

theorem closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955_count :
    closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955.length =
      11 :=
  closedMapTargetCompactClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsInputNamesW943_count

/-- Current checked W955 state. -/
structure MetrizableClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW955 :
    Type where
  seed : String
  declarations : List String
  targetSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW955 :
    MetrizableClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW955
    where
  seed :=
    "w955-closed-map-boundary-relation-split-target-no-univ-closedness-\
      normalized-source-endpoint-unit-components-primitive-fields-route"
  declarations :=
    ["MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955",
      "targetNoUnivDataOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "w954LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "w953PrimitiveLeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "w952LeavesOfSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "concreteLeavesOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "routeDataProviderOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "directBoundedLeftCalculusOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsW955",
      "closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955",
      "closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955_count"]
  targetSplitResult :=
    "proved: W955 constructs W944 target no-univ data from split\
      target-difference surjectivity and target compact no-univ membership\
      primitives"
  exactAtResult :=
    "proved: the W955 split-target surface feeds the W954/W953/W952/W951/\
      W950/W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/\
      W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["W944 target no-univ data replaced by split target-difference surjectivity\
      and target-codomain compact no-univ membership primitives",
      "W716 boundary data, W717 relation data, W725 closedness data, W719\
      normalized fixed-target data, W722 source data, endpoint strict-exact\
      witnesses, and raw right-adjoint/adjunction/W939 unit component fields\
      remain explicit"]
  remainingInputs :=
    closedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsInputNamesW955
  productSuccessClaimed := false

theorem currentW955ClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldsRouteStateW955;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
