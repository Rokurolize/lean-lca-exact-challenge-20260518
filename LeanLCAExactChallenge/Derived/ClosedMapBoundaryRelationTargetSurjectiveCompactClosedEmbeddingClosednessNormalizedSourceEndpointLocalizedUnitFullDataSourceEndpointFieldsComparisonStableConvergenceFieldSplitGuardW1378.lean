import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataComparisonConcreteLeavesStableConvergenceFieldSplitGuardW1377
import LeanLCAExactChallenge.Derived.EndpointStrictTopologyFieldsComparisonStableExactAtRoute

/-!
W1378 records the definitional convergence of the W883/W884/W885/W886
comparison stable ExactAt route from W733 concrete leaves down to explicit
source-triangulation and endpoint strict-topology fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W883 W733 concrete leaves reuse the W877 W732 route-data constructor. -/
theorem w883RouteDataProviderRunsThroughW877W1378
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    routeDataProviderOfConcreteLeavesForW883 leaves =
      routeDataProviderOfConcreteLeavesW877 leaves :=
  rfl

/-- W883 direct calculus delegates to W882 after W733 route-data construction. -/
theorem w883DirectCalculusRunsThroughW882W1378
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
        leaves =
      directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfConcreteLeavesForW883 leaves) :=
  rfl

/-- W883 stable package delegates to W882 after W733 route-data construction. -/
theorem w883StablePackageRunsThroughW882W1378
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
        leaves =
      boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfConcreteLeavesForW883 leaves) :=
  rfl

/-- W884 source-homological data is supplied from W855 comparison bijectivity. -/
theorem w884SourceHomologicalDataRunsThroughW855W1378
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    sourceHomologicalTriangulationDataOfSourceTriangulationW884 leaves =
      sourceHomologicalTriangulationDataOfComparisonBijectivityW855
        leaves.sourceTriangulationData :=
  rfl

/-- W884 route data delegates to W883 after source-triangulation leaf assembly. -/
theorem w884RouteDataProviderRunsThroughW883W1378
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    routeDataProviderOfSourceTriangulationComparisonW884 leaves =
      routeDataProviderOfConcreteLeavesForW883
        (concreteLeavesOfSourceTriangulationComparisonW884 leaves) :=
  rfl

/-- W884 direct calculus delegates to W883 after source-triangulation leaf assembly. -/
theorem w884DirectCalculusRunsThroughW883W1378
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
        leaves =
      directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
        (concreteLeavesOfSourceTriangulationComparisonW884 leaves) :=
  rfl

/-- W884 stable package delegates to W883 after source-triangulation leaf assembly. -/
theorem w884StablePackageRunsThroughW883W1378
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
        leaves =
      boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
        (concreteLeavesOfSourceTriangulationComparisonW884 leaves) :=
  rfl

/-- W885 source-triangulation provider is assembled from its three explicit fields. -/
theorem w885SourceTriangulationDataRunsThroughFieldsW1378
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    sourceTriangulationDataOfFieldsW885 leaves =
      { sourcePretriangulated := leaves.sourcePretriangulated
        sourceTriangulated := leaves.sourceTriangulated
        triangleCompletion := leaves.triangleCompletion } :=
  rfl

/-- W885 concrete leaves delegate to W884 after explicit source-field assembly. -/
theorem w885ConcreteLeavesRunThroughW884W1378
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    concreteLeavesOfSourceTriangulationFieldsComparisonW885 leaves =
      concreteLeavesOfSourceTriangulationComparisonW884
        (sourceTriangulationLeavesOfFieldsW885 leaves) :=
  rfl

/-- W885 route data delegates to W884 after explicit source-field assembly. -/
theorem w885RouteDataProviderRunsThroughW884W1378
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    routeDataProviderOfSourceTriangulationFieldsComparisonW885 leaves =
      routeDataProviderOfSourceTriangulationComparisonW884
        (sourceTriangulationLeavesOfFieldsW885 leaves) :=
  rfl

/-- W885 direct calculus delegates to W884 after explicit source-field assembly. -/
theorem w885DirectCalculusRunsThroughW884W1378
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
        leaves =
      directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
        (sourceTriangulationLeavesOfFieldsW885 leaves) :=
  rfl

/-- W885 stable package delegates to W884 after explicit source-field assembly. -/
theorem w885StablePackageRunsThroughW884W1378
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
        leaves =
      boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
        (sourceTriangulationLeavesOfFieldsW885 leaves) :=
  rfl

/-- W886 endpoint strict-topology provider is assembled from its four explicit fields. -/
theorem w886EndpointStrictTopologyDataRunsThroughFieldsW1378
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    endpointStrictTopologyDataOfFieldsW886 leaves =
      { endpointForgetPreservesHomology := leaves.endpointForgetPreservesHomology
        endpointClosedEmbedding := leaves.endpointClosedEmbedding
        endpointOpenMap := leaves.endpointOpenMap
        endpointEpiOfExactAt := leaves.endpointEpiOfExactAt } :=
  rfl

/-- W886 concrete leaves delegate to W885 after explicit endpoint-field assembly. -/
theorem w886ConcreteLeavesRunThroughW885W1378
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    concreteLeavesOfEndpointFieldsComparisonW886 leaves =
      concreteLeavesOfSourceTriangulationFieldsComparisonW885
        (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves) :=
  rfl

/-- W886 route data delegates to W885 after explicit endpoint-field assembly. -/
theorem w886RouteDataProviderRunsThroughW885W1378
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    routeDataProviderOfEndpointFieldsComparisonW886 leaves =
      routeDataProviderOfSourceTriangulationFieldsComparisonW885
        (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves) :=
  rfl

/-- W886 direct calculus delegates to W885 after explicit endpoint-field assembly. -/
theorem w886DirectCalculusRunsThroughW885W1378
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
        leaves =
      directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
        (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves) :=
  rfl

/-- W886 stable package delegates to W885 after explicit endpoint-field assembly. -/
theorem w886StablePackageRunsThroughW885W1378
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
        leaves =
      boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
        (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves) :=
  rfl

/-- W1378 keeps the W883 concrete-leaves count visible. -/
theorem w1378ConcreteLeavesComparisonStableExactAtInputCountMatchesW883 :
    concreteLeavesComparisonStableExactAtInputNamesW883.length = 8 :=
  concreteLeavesComparisonStableExactAtInputNamesW883_count

/-- W1378 keeps the W884 source-triangulation leaf count visible. -/
theorem w1378SourceTriangulationComparisonStableExactAtInputCountMatchesW884 :
    sourceTriangulationComparisonStableExactAtInputNamesW884.length = 8 :=
  sourceTriangulationComparisonStableExactAtInputNamesW884_count

/-- W1378 keeps the W885 explicit source-field count visible. -/
theorem w1378SourceTriangulationFieldsComparisonStableExactAtInputCountMatchesW885 :
    sourceTriangulationFieldsComparisonStableExactAtInputNamesW885.length = 10 :=
  sourceTriangulationFieldsComparisonStableExactAtInputNamesW885_count

/-- W1378 keeps the W886 explicit endpoint-field count visible. -/
theorem w1378EndpointFieldsComparisonStableExactAtInputCountMatchesW886 :
    endpointFieldsComparisonStableExactAtInputNamesW886.length = 13 :=
  endpointFieldsComparisonStableExactAtInputNamesW886_count

/-- Current W1378 nonterminal state. -/
structure SourceEndpointFieldsComparisonStableConvergenceStateW1378 : Type where
  seed : String
  declarations : List String
  concreteLeavesResult : String
  sourceTriangulationResult : String
  sourceFieldsResult : String
  endpointFieldsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1378 records W883-W886 convergence into the comparison stable ExactAt route. -/
def currentSourceEndpointFieldsComparisonStableConvergenceStateW1378 :
    SourceEndpointFieldsComparisonStableConvergenceStateW1378 where
  seed := "w1378-source-endpoint-fields-comparison-stable-convergence"
  declarations :=
    ["w883RouteDataProviderRunsThroughW877W1378",
      "w883DirectCalculusRunsThroughW882W1378",
      "w883StablePackageRunsThroughW882W1378",
      "w884SourceHomologicalDataRunsThroughW855W1378",
      "w884RouteDataProviderRunsThroughW883W1378",
      "w884DirectCalculusRunsThroughW883W1378",
      "w884StablePackageRunsThroughW883W1378",
      "w885SourceTriangulationDataRunsThroughFieldsW1378",
      "w885ConcreteLeavesRunThroughW884W1378",
      "w885RouteDataProviderRunsThroughW884W1378",
      "w885DirectCalculusRunsThroughW884W1378",
      "w885StablePackageRunsThroughW884W1378",
      "w886EndpointStrictTopologyDataRunsThroughFieldsW1378",
      "w886ConcreteLeavesRunThroughW885W1378",
      "w886RouteDataProviderRunsThroughW885W1378",
      "w886DirectCalculusRunsThroughW885W1378",
      "w886StablePackageRunsThroughW885W1378",
      "w1378ConcreteLeavesComparisonStableExactAtInputCountMatchesW883",
      "w1378SourceTriangulationComparisonStableExactAtInputCountMatchesW884",
      "w1378SourceTriangulationFieldsComparisonStableExactAtInputCountMatchesW885",
      "w1378EndpointFieldsComparisonStableExactAtInputCountMatchesW886"]
  concreteLeavesResult :=
    "proved: W883 reuses W877 W733-to-W732 construction and delegates to W882"
  sourceTriangulationResult :=
    "proved: W884 supplies the W733 source-homological leaf through W855 and \
      delegates to W883"
  sourceFieldsResult :=
    "proved: W885 assembles W722 source-triangulation data from explicit fields \
      and delegates to W884"
  endpointFieldsResult :=
    "proved: W886 assembles W720 endpoint strict-topology data from explicit \
      fields and delegates to W885"
  remainingInputs :=
    endpointFieldsComparisonStableExactAtInputNamesW886
  productSuccessClaimed := false

theorem currentW1378SourceEndpointFieldsComparisonStableConvergence_productSuccess :
    currentSourceEndpointFieldsComparisonStableConvergenceStateW1378.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
