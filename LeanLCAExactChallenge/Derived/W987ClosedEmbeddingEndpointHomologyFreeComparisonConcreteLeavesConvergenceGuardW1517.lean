import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeSourceEndpointConvergenceGuardW1516
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataComparisonConcreteLeavesStableConvergenceFieldSplitGuardW1377

/-!
W1517 specializes the W1516 W987 source/endpoint convergence surface to the
existing W1377 comparison concrete-leaves route. W1516 already reaches the W882
W732 route-data surface; W1517 records the W882-to-W881, W881-to-W880, and
W880-to-W879 delegations, plus the W879 branch delegations to W878.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1517 reuses the W1516 source/endpoint convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputW1516

/-- W1517 exposes the W732 route data already reached by W1516 through W883. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfConcreteLeavesForW883
    (concreteLeavesOfSourceTriangulationOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
      input)

/-- W1517's W732 route data is the W1516 source/endpoint route data. -/
theorem w1517RouteDataProviderMatchesW1516W732
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
        input =
      routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input :=
  w1516RouteDataProviderRunsThroughW884W883 input

/-- W1517 projects the W732 route data to the W874 endpoint-localized provider. -/
def endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874 :=
  endpointLocalizedRouteDataProviderOfW732ForW882
    (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)

/-- W1517 projects endpoint-localized data to the W853 homology-free provider. -/
def homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeRouteDataProviderOfEndpointLocalizedW881
    (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)

/-- W1517 exposes the direct bounded left calculus proof from W1516. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    input

/-- W1517 exposes the bounded derived infinity-category package from W1516. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceW1516
    input

/-- W1517 specializes W1377's W882-to-W875 endpoint-localized projection. -/
theorem w1517EndpointLocalizedProviderRunsThroughW875W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      routeDataProviderOfW732W875
        (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) :=
  w882EndpointLocalizedProviderRunsThroughW875W1377
    (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)

/-- W1517 specializes W1377's W881-to-W856 homology-free projection. -/
theorem w1517HomologyFreeProviderRunsThroughW856W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
        (endpointFactsRouteDataProviderOfEndpointLocalizedW874
          (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input)) :=
  w881HomologyFreeProviderRunsThroughW856W1377
    (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)

/-- W1517 direct calculus reaches W882 by the W1516 W883-to-W882 theorem. -/
theorem w1517DirectCalculusRunsThroughW882W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) :=
  w1516DirectCalculusRunsThroughW883W882 input

/-- W1517 stable package reaches W882 by the W1516 W883-to-W882 theorem. -/
theorem w1517StablePackageRunsThroughW882W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
        (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) :=
  w1516StablePackageRunsThroughW883W882 input

/-- W1517 direct calculus delegates from W882 to W881. -/
theorem w1517DirectCalculusRunsThroughW881W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
          (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517DirectCalculusRunsThroughW882W1377 input
    _ =
        directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
          (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w882DirectCalculusRunsThroughW881W1377
        (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 stable package delegates from W882 to W881. -/
theorem w1517StablePackageRunsThroughW881W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
          (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517StablePackageRunsThroughW882W1377 input
    _ =
        boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
          (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w882StablePackageRunsThroughW881W1377
        (routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 direct calculus delegates from W881 to W880. -/
theorem w1517DirectCalculusRunsThroughW880W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
          (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517DirectCalculusRunsThroughW881W1377 input
    _ =
        directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
          (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w881DirectCalculusRunsThroughW880W1377
        (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 stable package delegates from W881 to W880. -/
theorem w1517StablePackageRunsThroughW880W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
          (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517StablePackageRunsThroughW881W1377 input
    _ =
        boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
          (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w881StablePackageRunsThroughW880W1377
        (endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 direct calculus delegates from W880 to the W879 branch match. -/
theorem w1517DirectCalculusRunsThroughW879W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      match (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input).diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
            (closedMapExactInputsOfHomologyFreeRouteDataW853
              (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                input)
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
              (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                input)
              globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
          (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517DirectCalculusRunsThroughW880W1377 input
    _ =
        match (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input).diagramAndMappedCokernelClosednessData with
        | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
            directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
              (closedMapExactInputsOfHomologyFreeRouteDataW853
                (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                  input)
                globalClosedMapComponents mappedCokernelClosedMapProvider)
        | .closedEmbedding globalClosedEmbeddingComponents
            mappedCokernelClosedEmbeddingProvider =>
            directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
              (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
                (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                  input)
                globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
      w880DirectCalculusRunsThroughW879W1377
        (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 stable package delegates from W880 to the W879 branch match. -/
theorem w1517StablePackageRunsThroughW879W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
      match (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input).diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
            (closedMapExactInputsOfHomologyFreeRouteDataW853
              (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                input)
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
              (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                input)
              globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
        input =
        boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
          (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input) :=
      w1517StablePackageRunsThroughW880W1377 input
    _ =
        match (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input).diagramAndMappedCokernelClosednessData with
        | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
            boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
              (closedMapExactInputsOfHomologyFreeRouteDataW853
                (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                  input)
                globalClosedMapComponents mappedCokernelClosedMapProvider)
        | .closedEmbedding globalClosedEmbeddingComponents
            mappedCokernelClosedEmbeddingProvider =>
            boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
              (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
                (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
                  input)
                globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
      w880StablePackageRunsThroughW879W1377
        (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input)

/-- W1517 names the closed-map W735 exact input branch assembled from W853. -/
def closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedMapExactInputsOfHomologyFreeRouteDataW853
    (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)
    globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1517 names the closed-embedding W735 exact input branch assembled from W853. -/
def closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
    (homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input)
    globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1517 closed-map branch specializes W1377's W879-to-W851 selected-cochain step. -/
theorem w1517ClosedMapSelectedCochainDataRunsThroughW851W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapSelectedCochainDataOfComparisonW879
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedMapSelectedCochainDirectSourceDataOfComparisonW851
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w879ClosedMapSelectedCochainDataRunsThroughW851W1377
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1517 closed-embedding branch specializes W1377's W879-to-W851 selected-cochain step. -/
theorem w1517ClosedEmbeddingSelectedCochainDataRunsThroughW851W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingSelectedCochainDataOfComparisonW879
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w879ClosedEmbeddingSelectedCochainDataRunsThroughW851W1377
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1517 closed-map branch specializes W1377's W879-to-W878 direct-calculus step. -/
theorem w1517ClosedMapDirectCalculusRunsThroughW878W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        (closedMapSelectedCochainDataOfComparisonW879
          (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input globalClosedMapComponents mappedCokernelClosedMapProvider)) :=
  w879ClosedMapDirectCalculusRunsThroughW878W1377
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1517 closed-embedding branch specializes W1377's W879-to-W878 direct-calculus step. -/
theorem w1517ClosedEmbeddingDirectCalculusRunsThroughW878W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        (closedEmbeddingSelectedCochainDataOfComparisonW879
          (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)) :=
  w879ClosedEmbeddingDirectCalculusRunsThroughW878W1377
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1517 closed-map branch specializes W1377's W879-to-W878 stable-package step. -/
theorem w1517ClosedMapStablePackageRunsThroughW878W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        (closedMapSelectedCochainDataOfComparisonW879
          (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input globalClosedMapComponents mappedCokernelClosedMapProvider)) :=
  w879ClosedMapStablePackageRunsThroughW878W1377
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1517 closed-embedding branch specializes W1377's W879-to-W878 stable-package step. -/
theorem w1517ClosedEmbeddingStablePackageRunsThroughW878W1377
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        (closedEmbeddingSelectedCochainDataOfComparisonW879
          (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
            input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)) :=
  w879ClosedEmbeddingStablePackageRunsThroughW878W1377
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1517 keeps the W1516 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceEndpointConvergenceInputNamesW1516_count

/-- Current W1517 nonterminal comparison concrete-leaves convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceStateW1517 :
    Type where
  seed : String
  declarations : List String
  routeDataResult : String
  endpointLocalizedResult : String
  homologyFreeResult : String
  comparisonBranchResult : String
  selectedCochainBranchResult : String
  remainingInputs : List String
  w882RemainingInputs : List String
  w881RemainingInputs : List String
  w880RemainingInputs : List String
  w879RemainingInputs : List String
  w878RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1517 records the W1516-to-W1377 comparison concrete-leaves convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceStateW1517 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceStateW1517 where
  seed :=
    "w1517-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-comparison-concrete-leaves-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputW1517",
      "routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "w1517RouteDataProviderMatchesW1516W732",
      "endpointLocalizedRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "homologyFreeRouteDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "w1517EndpointLocalizedProviderRunsThroughW875W1377",
      "w1517HomologyFreeProviderRunsThroughW856W1377",
      "w1517DirectCalculusRunsThroughW882W1377",
      "w1517StablePackageRunsThroughW882W1377",
      "w1517DirectCalculusRunsThroughW881W1377",
      "w1517StablePackageRunsThroughW881W1377",
      "w1517DirectCalculusRunsThroughW880W1377",
      "w1517StablePackageRunsThroughW880W1377",
      "w1517DirectCalculusRunsThroughW879W1377",
      "w1517StablePackageRunsThroughW879W1377",
      "closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517",
      "w1517ClosedMapSelectedCochainDataRunsThroughW851W1377",
      "w1517ClosedEmbeddingSelectedCochainDataRunsThroughW851W1377",
      "w1517ClosedMapDirectCalculusRunsThroughW878W1377",
      "w1517ClosedEmbeddingDirectCalculusRunsThroughW878W1377",
      "w1517ClosedMapStablePackageRunsThroughW878W1377",
      "w1517ClosedEmbeddingStablePackageRunsThroughW878W1377",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517_count"]
  routeDataResult :=
    "proved: W1517 uses the W732 route data that W1516 reaches through W883"
  endpointLocalizedResult :=
    "proved: W1517 specializes W1377's W882-to-W875 endpoint-localized projection"
  homologyFreeResult :=
    "proved: W1517 specializes W1377's W881-to-W856 homology-free projection"
  comparisonBranchResult :=
    "proved: W1517 direct calculus and stable package run through W882, W881, \
      W880, and the W879 closedness branch match"
  selectedCochainBranchResult :=
    "proved: W1517 closed-map and closed-embedding branches specialize W1377's \
      W879-to-W878 selected-cochain delegations"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceInputNamesW1517
  w882RemainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882
  w881RemainingInputs :=
    endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881
  w880RemainingInputs :=
    homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880
  w879RemainingInputs :=
    comparisonConcreteLeavesStableExactAtInputNamesW879
  w878RemainingInputs :=
    selectedCochainConcreteLeavesStableExactAtInputNamesW878
  productSuccessClaimed := false

theorem currentW1517W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceStateW1517.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
