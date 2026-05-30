import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointHomologyFreeComparisonStableConvergenceFieldSplitGuardW1382
import LeanLCAExactChallenge.Derived.ClosedMapRelationDataBoundaryDataSourceTriangulationEndpointFactsLocalizedRightAdjointComparisonStableExactAtRoute

/-!
W1383 records the definitional convergence of the closed-map W900-W903
comparison stable ExactAt chain, bundling endpoint facts, source triangulation,
boundary data, and relation data into the W899 endpoint-homology-free route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W900 endpoint closed-embedding facts are projected from the W856 provider. -/
theorem w900EndpointClosedEmbeddingRunsThroughEndpointFactsW1383
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    endpointClosedEmbeddingOfEndpointFactsW900 endpointFacts =
      endpointFacts.endpointClosedEmbedding :=
  rfl

/-- W900 endpoint open-map facts are projected from the W856 provider. -/
theorem w900EndpointOpenMapRunsThroughEndpointFactsW1383
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    endpointOpenMapOfEndpointFactsW900 endpointFacts =
      endpointFacts.endpointOpenMap :=
  rfl

/-- W900 endpoint epi facts are projected from the W856 provider. -/
theorem w900EndpointEpiRunsThroughEndpointFactsW1383
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    endpointEpiOfExactAtOfEndpointFactsW900 endpointFacts =
      endpointFacts.endpointEpiOfExactAt :=
  rfl

/-- W900 localized right-adjoint data is projected from the W721 provider. -/
theorem w900LocalizedRightAdjointRunsThroughW721W1383
    (localizedData : MetrizableWppLocalizedRightAdjointDataProviderW721) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedRightAdjointW900
        localizedData =
      boundedHomotopyLocalizedRightAdjoint_of_localizedRightAdjointDataW721
        localizedData :=
  rfl

/-- W900 concrete leaves delegate to W899 after endpoint/localized-adjoint bundling. -/
theorem w900ConcreteLeavesRunThroughW899W1383
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    concreteLeavesOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900 leaves =
      concreteLeavesOfClosedMapEndpointHomologyFreeComparisonW899
        (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
          leaves) :=
  rfl

/-- W900 route data delegates to W899 after endpoint/localized-adjoint bundling. -/
theorem w900RouteDataProviderRunsThroughW899W1383
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    routeDataProviderOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
        leaves =
      routeDataProviderOfClosedMapEndpointHomologyFreeComparisonW899
        (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
          leaves) :=
  rfl

/-- W900 direct calculus delegates to W899 after endpoint/localized-adjoint bundling. -/
theorem w900DirectCalculusRunsThroughW899W1383
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    directBoundedLeftCalculusOfClosedMapEndpointLocalizedAdjointW900 leaves =
      directBoundedLeftCalculusOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
        (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
          leaves) :=
  rfl

/-- W900 stable package delegates to W899 after endpoint/localized-adjoint bundling. -/
theorem w900StablePackageRunsThroughW899W1383
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    boundedDerivedInfinityCategoryOfClosedMapEndpointLocalizedAdjointW900 leaves =
      boundedDerivedInfinityCategoryOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
        (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
          leaves) :=
  rfl

/-- W901 source pretriangulation is projected from the W722 provider. -/
theorem w901SourcePretriangulatedRunsThroughW722W1383
    (sourceData : MetrizableWppSourceTriangulationDataProviderW722) :
    sourcePretriangulatedOfSourceTriangulationW901 sourceData =
      sourcePretriangulated_of_sourceTriangulationDataW722 sourceData :=
  rfl

/-- W901 source triangulation is projected from the W722 provider. -/
theorem w901SourceTriangulatedRunsThroughW722W1383
    (sourceData : MetrizableWppSourceTriangulationDataProviderW722) :
    sourceTriangulatedOfSourceTriangulationW901 sourceData =
      sourceTriangulated_of_sourceTriangulationDataW722 sourceData :=
  rfl

/-- W901 concrete leaves delegate to W900 after source-triangulation bundling. -/
theorem w901ConcreteLeavesRunThroughW900W1383
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    concreteLeavesOfClosedMapSourceTriangulationEndpointFactsW901 leaves =
      concreteLeavesOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
        (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901
          leaves) :=
  rfl

/-- W901 route data delegates to W900 after source-triangulation bundling. -/
theorem w901RouteDataProviderRunsThroughW900W1383
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    routeDataProviderOfClosedMapSourceTriangulationEndpointFactsW901 leaves =
      routeDataProviderOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
        (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901
          leaves) :=
  rfl

/-- W901 direct calculus delegates to W900 after source-triangulation bundling. -/
theorem w901DirectCalculusRunsThroughW900W1383
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    directBoundedLeftCalculusOfClosedMapSourceTriangulationEndpointFactsW901
        leaves =
      directBoundedLeftCalculusOfClosedMapEndpointLocalizedAdjointW900
        (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901
          leaves) :=
  rfl

/-- W901 stable package delegates to W900 after source-triangulation bundling. -/
theorem w901StablePackageRunsThroughW900W1383
    (leaves : MetrizableWppClosedMapSourceTriangulationEndpointFactsLeavesW901) :
    boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationEndpointFactsW901
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapEndpointLocalizedAdjointW900
        (closedMapEndpointLocalizedAdjointLeavesOfSourceTriangulationW901
          leaves) :=
  rfl

/-- W902 right-open boundary is projected from W716 data. -/
theorem w902RightOpenBoundaryRunsThroughW716W1383
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    rightOpenBoundaryOfBoundaryDataW902 boundaryData =
      rightOpenBoundary_of_boundaryDataW716 boundaryData :=
  rfl

/-- W902 source-pi-zero boundary is projected from W716 data. -/
theorem w902SourcePiZeroBoundaryRunsThroughW716W1383
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    sourcePiZeroBoundaryOfBoundaryDataW902 boundaryData =
      sourcePiZeroBoundary_of_boundaryDataW716 boundaryData :=
  rfl

/-- W902 concrete leaves delegate to W901 after boundary-data bundling. -/
theorem w902ConcreteLeavesRunThroughW901W1383
    (leaves :
      MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    concreteLeavesOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        leaves =
      concreteLeavesOfClosedMapSourceTriangulationEndpointFactsW901
        (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902
          leaves) :=
  rfl

/-- W902 route data delegates to W901 after boundary-data bundling. -/
theorem w902RouteDataProviderRunsThroughW901W1383
    (leaves :
      MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    routeDataProviderOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        leaves =
      routeDataProviderOfClosedMapSourceTriangulationEndpointFactsW901
        (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902
          leaves) :=
  rfl

/-- W902 direct calculus delegates to W901 after boundary-data bundling. -/
theorem w902DirectCalculusRunsThroughW901W1383
    (leaves :
      MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    directBoundedLeftCalculusOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        leaves =
      directBoundedLeftCalculusOfClosedMapSourceTriangulationEndpointFactsW901
        (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902
          leaves) :=
  rfl

/-- W902 stable package delegates to W901 after boundary-data bundling. -/
theorem w902StablePackageRunsThroughW901W1383
    (leaves :
      MetrizableWppClosedMapBoundaryDataSourceTriangulationEndpointFactsLeavesW902) :
    boundedDerivedInfinityCategoryOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationEndpointFactsW901
        (closedMapSourceTriangulationEndpointFactsLeavesOfBoundaryDataW902
          leaves) :=
  rfl

/-- W903 relation-pullback data is projected from W717 data. -/
theorem w903RelationPullbackRunsThroughW717W1383
    (relationData : ClosedNatTransOrdinaryRelationDataProviderW717) :
    relationPullbackProviderOfRelationDataW903 relationData =
      relationPullbackProvider_of_relationDataW717 relationData :=
  rfl

/-- W903 target-relation-lift data is projected from W717 data. -/
theorem w903TargetRelationLiftsRunsThroughW717W1383
    (relationData : ClosedNatTransOrdinaryRelationDataProviderW717) :
    targetRelationLiftsProviderOfRelationDataW903 relationData =
      targetRelationLiftsProvider_of_relationDataW717 relationData :=
  rfl

/-- W903 concrete leaves delegate to W902 after relation-data bundling. -/
theorem w903ConcreteLeavesRunThroughW902W1383
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    concreteLeavesOfClosedMapRelationDataBoundaryEndpointFactsW903 leaves =
      concreteLeavesOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves) :=
  rfl

/-- W903 route data delegates to W902 after relation-data bundling. -/
theorem w903RouteDataProviderRunsThroughW902W1383
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    routeDataProviderOfClosedMapRelationDataBoundaryEndpointFactsW903 leaves =
      routeDataProviderOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves) :=
  rfl

/-- W903 direct calculus delegates to W902 after relation-data bundling. -/
theorem w903DirectCalculusRunsThroughW902W1383
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    directBoundedLeftCalculusOfClosedMapRelationDataBoundaryEndpointFactsW903
        leaves =
      directBoundedLeftCalculusOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves) :=
  rfl

/-- W903 stable package delegates to W902 after relation-data bundling. -/
theorem w903StablePackageRunsThroughW902W1383
    (leaves :
      MetrizableWppClosedMapRelationDataBoundaryEndpointFactsLeavesW903) :
    boundedDerivedInfinityCategoryOfClosedMapRelationDataBoundaryEndpointFactsW903
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapBoundaryDataSourceTriangulationEndpointFactsW902
        (closedMapBoundaryEndpointFactsLeavesOfRelationDataW903 leaves) :=
  rfl

/-- W1383 keeps the W900 endpoint/localized-adjoint count visible. -/
theorem w1383ClosedMapEndpointLocalizedAdjointInputCountMatchesW900 :
    closedMapEndpointLocalizedAdjointInputNamesW900.length = 33 :=
  closedMapEndpointLocalizedAdjointInputNamesW900_count

/-- W1383 keeps the W901 source-triangulation count visible. -/
theorem w1383ClosedMapSourceTriangulationEndpointFactsInputCountMatchesW901 :
    closedMapSourceTriangulationEndpointFactsInputNamesW901.length = 31 :=
  closedMapSourceTriangulationEndpointFactsInputNamesW901_count

/-- W1383 keeps the W902 boundary-data count visible. -/
theorem
    w1383ClosedMapBoundaryDataSourceTriangulationEndpointFactsInputCountMatchesW902 :
    closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902.length =
      30 :=
  closedMapBoundaryDataSourceTriangulationEndpointFactsInputNamesW902_count

/-- W1383 keeps the W903 relation-data count visible. -/
theorem w1383ClosedMapRelationDataBoundaryEndpointFactsInputCountMatchesW903 :
    closedMapRelationDataBoundaryEndpointFactsInputNamesW903.length = 29 :=
  closedMapRelationDataBoundaryEndpointFactsInputNamesW903_count

/-- Current W1383 nonterminal state. -/
structure BundledClosedMapEndpointRelationStableConvergenceStateW1383 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedAdjointResult : String
  sourceTriangulationResult : String
  boundaryDataResult : String
  relationDataResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1383 records W900-W903 convergence into the closed-map stable ExactAt chain. -/
def currentBundledClosedMapEndpointRelationStableConvergenceStateW1383 :
    BundledClosedMapEndpointRelationStableConvergenceStateW1383 where
  seed := "w1383-bundled-closed-map-endpoint-relation-stable-convergence"
  declarations :=
    ["w900EndpointClosedEmbeddingRunsThroughEndpointFactsW1383",
      "w900EndpointOpenMapRunsThroughEndpointFactsW1383",
      "w900EndpointEpiRunsThroughEndpointFactsW1383",
      "w900LocalizedRightAdjointRunsThroughW721W1383",
      "w900ConcreteLeavesRunThroughW899W1383",
      "w900RouteDataProviderRunsThroughW899W1383",
      "w900DirectCalculusRunsThroughW899W1383",
      "w900StablePackageRunsThroughW899W1383",
      "w901SourcePretriangulatedRunsThroughW722W1383",
      "w901SourceTriangulatedRunsThroughW722W1383",
      "w901ConcreteLeavesRunThroughW900W1383",
      "w901RouteDataProviderRunsThroughW900W1383",
      "w901DirectCalculusRunsThroughW900W1383",
      "w901StablePackageRunsThroughW900W1383",
      "w902RightOpenBoundaryRunsThroughW716W1383",
      "w902SourcePiZeroBoundaryRunsThroughW716W1383",
      "w902ConcreteLeavesRunThroughW901W1383",
      "w902RouteDataProviderRunsThroughW901W1383",
      "w902DirectCalculusRunsThroughW901W1383",
      "w902StablePackageRunsThroughW901W1383",
      "w903RelationPullbackRunsThroughW717W1383",
      "w903TargetRelationLiftsRunsThroughW717W1383",
      "w903ConcreteLeavesRunThroughW902W1383",
      "w903RouteDataProviderRunsThroughW902W1383",
      "w903DirectCalculusRunsThroughW902W1383",
      "w903StablePackageRunsThroughW902W1383",
      "w1383ClosedMapEndpointLocalizedAdjointInputCountMatchesW900",
      "w1383ClosedMapSourceTriangulationEndpointFactsInputCountMatchesW901",
      "w1383ClosedMapBoundaryDataSourceTriangulationEndpointFactsInputCountMatchesW902",
      "w1383ClosedMapRelationDataBoundaryEndpointFactsInputCountMatchesW903"]
  endpointLocalizedAdjointResult :=
    "proved: W900 bundles W856 endpoint facts and W721 localized-right-adjoint \
      data into the W899 endpoint-homology-free closed-map route"
  sourceTriangulationResult :=
    "proved: W901 bundles W722 source triangulation data into the W900 route"
  boundaryDataResult :=
    "proved: W902 bundles W716 boundary data into the W901 route"
  relationDataResult :=
    "proved: W903 bundles W717 relation data into the W902 route"
  remainingInputs :=
    closedMapRelationDataBoundaryEndpointFactsInputNamesW903
  productSuccessClaimed := false

theorem currentW1383BundledClosedMapEndpointRelationStableConvergence_productSuccess :
    currentBundledClosedMapEndpointRelationStableConvergenceStateW1383.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
