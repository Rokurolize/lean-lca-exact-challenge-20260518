import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeLocalizedRightAdjointConvergenceGuardW1515
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSourceEndpointFieldsComparisonStableConvergenceFieldSplitGuardW1378

/-!
W1516 composes the W1515 W987 endpoint strict-topology route with the existing
W1378 source/endpoint convergence guard. W1515 reaches W886; W1378 records the
W886-to-W885, W885-to-W884, W884-to-W883, and W883-to-W882/W877 delegations.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

/-- W1516 reuses the W1515 localized-right-adjoint convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputW1515

/-- W1516 names the W886 endpoint strict-topology leaves reached by W1515. -/
def endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppEndpointStrictTopologyFieldLeavesW886 :=
  endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    input

/-- W1516 projects W1515's W886 leaves to W885 source-triangulation field leaves. -/
def sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppSourceTriangulationFieldComparisonLeavesW885 :=
  sourceTriangulationFieldLeavesOfEndpointFieldsW886
    (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 projects W1515 through W885 to W884 source-triangulation leaves. -/
def sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppSourceTriangulationComparisonLeavesW884 :=
  sourceTriangulationLeavesOfFieldsW885
    (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 exposes the W884 concrete leaves obtained from the W1515 endpoint route. -/
def concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfSourceTriangulationComparisonW884
    (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 exposes the same concrete leaves as W1515. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    input

/-- W1516 exposes the same route data as W1515. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    input

/-- W1516 exposes the same direct bounded left calculus package as W1515. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    input

/-- W1516 exposes the same bounded derived infinity-category package as W1515. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceW1515
    input

/-- W1516 specializes W1378's W886 endpoint strict-topology assembly to W1515 leaves. -/
theorem w1516EndpointStrictTopologyDataRunsThroughW886W1378
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    endpointStrictTopologyDataOfFieldsW886
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) =
      { endpointForgetPreservesHomology :=
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).endpointForgetPreservesHomology
        endpointClosedEmbedding :=
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).endpointClosedEmbedding
        endpointOpenMap :=
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).endpointOpenMap
        endpointEpiOfExactAt :=
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).endpointEpiOfExactAt } :=
  w886EndpointStrictTopologyDataRunsThroughFieldsW1378
    (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 specializes W1378's W885 source-triangulation assembly to W1515 leaves. -/
theorem w1516SourceTriangulationDataRunsThroughW885W1378
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    sourceTriangulationDataOfFieldsW885
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) =
      { sourcePretriangulated :=
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).sourcePretriangulated
        sourceTriangulated :=
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).sourceTriangulated
        triangleCompletion :=
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input).triangleCompletion } :=
  w885SourceTriangulationDataRunsThroughFieldsW1378
    (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 specializes W1378's W884 source-homological construction to W1515 leaves. -/
theorem w1516SourceHomologicalDataRunsThroughW855W1378
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    sourceHomologicalTriangulationDataOfSourceTriangulationW884
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) =
      sourceHomologicalTriangulationDataOfComparisonBijectivityW855
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input).sourceTriangulationData :=
  w884SourceHomologicalDataRunsThroughW855W1378
    (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1516 composes W1515's W886 route with W1378's W886-to-W885 step. -/
theorem w1516ConcreteLeavesRunThroughW886W885
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      concreteLeavesOfSourceTriangulationFieldsComparisonW885
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        concreteLeavesOfEndpointFieldsComparisonW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1515ConcreteLeavesRunThroughW887W886 input
    _ =
        concreteLeavesOfSourceTriangulationFieldsComparisonW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w886ConcreteLeavesRunThroughW885W1378
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

/-- W1516 further composes through W885 to W884. -/
theorem w1516ConcreteLeavesRunThroughW885W884
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      concreteLeavesOfSourceTriangulationComparisonW884
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        concreteLeavesOfSourceTriangulationFieldsComparisonW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516ConcreteLeavesRunThroughW886W885 input
    _ =
        concreteLeavesOfSourceTriangulationComparisonW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w885ConcreteLeavesRunThroughW884W1378
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516RouteDataProviderRunsThroughW886W885
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      routeDataProviderOfSourceTriangulationFieldsComparisonW885
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        routeDataProviderOfEndpointFieldsComparisonW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1515RouteDataProviderRunsThroughW887W886 input
    _ =
        routeDataProviderOfSourceTriangulationFieldsComparisonW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w886RouteDataProviderRunsThroughW885W1378
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516RouteDataProviderRunsThroughW885W884
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      routeDataProviderOfSourceTriangulationComparisonW884
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        routeDataProviderOfSourceTriangulationFieldsComparisonW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516RouteDataProviderRunsThroughW886W885 input
    _ =
        routeDataProviderOfSourceTriangulationComparisonW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w885RouteDataProviderRunsThroughW884W1378
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516RouteDataProviderRunsThroughW884W883
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      routeDataProviderOfConcreteLeavesForW883
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        routeDataProviderOfSourceTriangulationComparisonW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516RouteDataProviderRunsThroughW885W884 input
    _ =
        routeDataProviderOfConcreteLeavesForW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w884RouteDataProviderRunsThroughW883W1378
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516RouteDataProviderRunsThroughW883W877
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      routeDataProviderOfConcreteLeavesW877
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        routeDataProviderOfConcreteLeavesForW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516RouteDataProviderRunsThroughW884W883 input
    _ =
        routeDataProviderOfConcreteLeavesW877
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w883RouteDataProviderRunsThroughW877W1378
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516DirectCalculusRunsThroughW886W885
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1515DirectCalculusRunsThroughW887W886 input
    _ =
        directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w886DirectCalculusRunsThroughW885W1378
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516DirectCalculusRunsThroughW885W884
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516DirectCalculusRunsThroughW886W885 input
    _ =
        directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w885DirectCalculusRunsThroughW884W1378
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516DirectCalculusRunsThroughW884W883
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516DirectCalculusRunsThroughW885W884 input
    _ =
        directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w884DirectCalculusRunsThroughW883W1378
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516DirectCalculusRunsThroughW883W882
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfConcreteLeavesForW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input)) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516DirectCalculusRunsThroughW884W883 input
    _ =
        directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
          (routeDataProviderOfConcreteLeavesForW883
            (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
              input)) :=
      w883DirectCalculusRunsThroughW882W1378
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516StablePackageRunsThroughW886W885
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
          (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1515StablePackageRunsThroughW887W886 input
    _ =
        boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w886StablePackageRunsThroughW885W1378
        (endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516StablePackageRunsThroughW885W884
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
          (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516StablePackageRunsThroughW886W885 input
    _ =
        boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w885StablePackageRunsThroughW884W1378
        (sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516StablePackageRunsThroughW884W883
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
          (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516StablePackageRunsThroughW885W884 input
    _ =
        boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w884StablePackageRunsThroughW883W1378
        (sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

theorem w1516StablePackageRunsThroughW883W882
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfConcreteLeavesForW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input)) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
        boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
          (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
            input) :=
      w1516StablePackageRunsThroughW884W883 input
    _ =
        boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
          (routeDataProviderOfConcreteLeavesForW883
            (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
              input)) :=
      w883StablePackageRunsThroughW882W1378
        (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
          input)

/-- W1516 keeps the W1515 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3LocalizedRightAdjointConvergenceInputNamesW1515_count

/-- Current W1516 nonterminal source/endpoint convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceStateW1516 :
    Type where
  seed : String
  declarations : List String
  endpointFieldsResult : String
  sourceFieldsResult : String
  sourceTriangulationResult : String
  concreteLeavesRouteResult : String
  remainingInputs : List String
  w886RemainingInputs : List String
  w885RemainingInputs : List String
  w884RemainingInputs : List String
  w883RemainingInputs : List String
  w882RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1516 records the W1515-to-W1378 source/endpoint convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceStateW1516 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceStateW1516 where
  seed :=
    "w1516-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-source-endpoint-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516",
      "endpointStrictTopologyFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516",
      "sourceTriangulationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516",
      "sourceTriangulationLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516",
      "w1516EndpointStrictTopologyDataRunsThroughW886W1378",
      "w1516SourceTriangulationDataRunsThroughW885W1378",
      "w1516SourceHomologicalDataRunsThroughW855W1378",
      "w1516ConcreteLeavesRunThroughW886W885",
      "w1516ConcreteLeavesRunThroughW885W884",
      "w1516RouteDataProviderRunsThroughW886W885",
      "w1516RouteDataProviderRunsThroughW885W884",
      "w1516RouteDataProviderRunsThroughW884W883",
      "w1516RouteDataProviderRunsThroughW883W877",
      "w1516DirectCalculusRunsThroughW886W885",
      "w1516DirectCalculusRunsThroughW885W884",
      "w1516DirectCalculusRunsThroughW884W883",
      "w1516DirectCalculusRunsThroughW883W882",
      "w1516StablePackageRunsThroughW886W885",
      "w1516StablePackageRunsThroughW885W884",
      "w1516StablePackageRunsThroughW884W883",
      "w1516StablePackageRunsThroughW883W882",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516_count"]
  endpointFieldsResult :=
    "proved: W1515's W886 endpoint strict-topology route specializes W1378's\
      W886-to-W885 convergence"
  sourceFieldsResult :=
    "proved: W1516 further composes through W885 explicit source fields"
  sourceTriangulationResult :=
    "proved: W1516 further composes through W884 source triangulation and W855\
      source homology construction"
  concreteLeavesRouteResult :=
    "proved: W1516 route data, direct calculus, and stable package run through\
      W883 and W882 while concrete leaves run through W884"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516
  w886RemainingInputs :=
    endpointFieldsComparisonStableExactAtInputNamesW886
  w885RemainingInputs :=
    sourceTriangulationFieldsComparisonStableExactAtInputNamesW885
  w884RemainingInputs :=
    sourceTriangulationComparisonStableExactAtInputNamesW884
  w883RemainingInputs :=
    concreteLeavesComparisonStableExactAtInputNamesW883
  w882RemainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882
  productSuccessClaimed := false

theorem currentW1516W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceStateW1516.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
