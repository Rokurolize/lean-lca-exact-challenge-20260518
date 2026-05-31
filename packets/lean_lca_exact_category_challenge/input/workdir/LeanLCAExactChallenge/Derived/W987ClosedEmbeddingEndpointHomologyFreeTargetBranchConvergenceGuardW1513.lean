import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeConvergenceGuardW1512
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetClosednessBranchComparisonStableConvergenceFieldSplitGuardW1381

/-!
W1513 composes the W1512 W987 closed-embedding endpoint-homology-free surface
with the existing W1381 target-closedness branch convergence guard. W1512
already routes W898 back to W897; W1381 records the W897 closed-embedding branch
delegation to W895 and the W895 target-field delegation to W894.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

/-- W1513 reuses the W1512 endpoint-homology-free convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingEndpointHomologyFreeConvergenceInputW1512

/-- W1513 names the W897 closed-embedding leaves reached by W1512. -/
def closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    MetrizableWppClosedEmbeddingClosednessFieldLeavesW897 :=
  closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceW1512
    input

/-- W1513 names the W895 target-field leaves projected from W1512's W897 leaves. -/
def targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    MetrizableWppTargetSurjectiveCompactFieldLeavesW895 :=
  targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
      input)

/-- W1513 names the W894 relation-field leaves projected from W1512 through W895. -/
def relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    MetrizableWppRelationFieldLeavesW894 :=
  relationFieldLeavesOfTargetSurjectiveCompactFieldsW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
      input)

/-- W1513 exposes the same concrete leaves as W1512. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceW1512
    input

/-- W1513 exposes the same route data as W1512. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceW1512
    input

/-- W1513 exposes the same direct bounded left calculus package as W1512. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceW1512
    input

/-- W1513 exposes the same bounded derived infinity-category package as W1512. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceW1512
    input

/-- W1513 confirms W1512's W897 leaves are the W1511/W1510 closedness leaves. -/
theorem w1513ClosedEmbeddingClosednessFieldLeavesRunThroughW1511W1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      closedEmbeddingClosednessFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingEndpointHomologyFreeComparisonW1511
        input :=
  w1511ClosedEmbeddingClosednessFieldLeavesMatchW1510 input

/-- W1513 specializes W1381's W897 branch assembly to W1512 leaves. -/
theorem w1513ClosedEmbeddingClosednessDataRunsThroughW897W1381
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    diagramAndMappedCokernelClosednessDataOfClosedEmbeddingFieldsW897
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input).globalClosedEmbeddingComponents
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input).mappedCokernelClosedEmbeddingProvider =
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725.closedEmbedding
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input).globalClosedEmbeddingComponents
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input).mappedCokernelClosedEmbeddingProvider :=
  w897ClosedEmbeddingClosednessDataRunsThroughFieldsW1381
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
      input).globalClosedEmbeddingComponents
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
      input).mappedCokernelClosedEmbeddingProvider

/-- W1513 composes W1512's W898-to-W897 concrete leaves with W1381's W897-to-W895 step. -/
theorem w1513ConcreteLeavesRunThroughW897W895
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        concreteLeavesOfClosedEmbeddingClosednessFieldsComparisonW897
          (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1512ConcreteLeavesRunThroughW898W897Convergence input
    _ =
        concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w897ConcreteLeavesRunThroughW895W1381
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 composes W1512's route data with W1381's W897-to-W895 step. -/
theorem w1513RouteDataProviderRunsThroughW897W895
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        routeDataProviderOfClosedEmbeddingClosednessFieldsComparisonW897
          (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1512RouteDataProviderRunsThroughW898W897Convergence input
    _ =
        routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w897RouteDataProviderRunsThroughW895W1381
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 composes W1512's direct calculus with W1381's W897-to-W895 step. -/
theorem w1513DirectCalculusRunsThroughW897W895
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
          (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1512DirectCalculusRunsThroughW898W897Convergence input
    _ =
        directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w897DirectCalculusRunsThroughW895W1381
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 composes W1512's stable package with W1381's W897-to-W895 step. -/
theorem w1513StablePackageRunsThroughW897W895
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
          (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1512StablePackageRunsThroughW898W897Convergence input
    _ =
        boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w897StablePackageRunsThroughW895W1381
        (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 further composes W1512's concrete leaves through W895 to W894. -/
theorem w1513ConcreteLeavesRunThroughW895W894
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      concreteLeavesOfRelationFieldsComparisonW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1513ConcreteLeavesRunThroughW897W895 input
    _ =
        concreteLeavesOfRelationFieldsComparisonW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w895ConcreteLeavesRunThroughW894W1381
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 further composes W1512's route data through W895 to W894. -/
theorem w1513RouteDataProviderRunsThroughW895W894
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      routeDataProviderOfRelationFieldsComparisonW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1513RouteDataProviderRunsThroughW897W895 input
    _ =
        routeDataProviderOfRelationFieldsComparisonW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w895RouteDataProviderRunsThroughW894W1381
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 further composes W1512's direct calculus through W895 to W894. -/
theorem w1513DirectCalculusRunsThroughW895W894
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      directBoundedLeftCalculusOfRelationFieldsComparisonStableExactAtW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1513DirectCalculusRunsThroughW897W895 input
    _ =
        directBoundedLeftCalculusOfRelationFieldsComparisonStableExactAtW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w895DirectCalculusRunsThroughW894W1381
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 further composes W1512's stable package through W895 to W894. -/
theorem w1513StablePackageRunsThroughW895W894
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
      boundedDerivedInfinityCategoryOfRelationFieldsComparisonStableExactAtW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
        input =
        boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
          (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w1513StablePackageRunsThroughW897W895 input
    _ =
        boundedDerivedInfinityCategoryOfRelationFieldsComparisonStableExactAtW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
            input) :=
      w895StablePackageRunsThroughW894W1381
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
          input)

/-- W1513 keeps the W1512 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceInputNamesW1512

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointHomologyFreeConvergenceInputNamesW1512_count

/-- Current W1513 nonterminal target-branch convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceStateW1513 :
    Type where
  seed : String
  declarations : List String
  targetBranchResult : String
  relationRouteResult : String
  remainingInputs : List String
  w897RemainingInputs : List String
  w895RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1513 records the W1512-to-W1381 target-branch convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceStateW1513 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceStateW1513 where
  seed :=
    "w1513-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-target-branch-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513",
      "closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513",
      "w1513ClosedEmbeddingClosednessFieldLeavesRunThroughW1511W1510",
      "w1513ClosedEmbeddingClosednessDataRunsThroughW897W1381",
      "w1513ConcreteLeavesRunThroughW897W895",
      "w1513RouteDataProviderRunsThroughW897W895",
      "w1513DirectCalculusRunsThroughW897W895",
      "w1513StablePackageRunsThroughW897W895",
      "w1513ConcreteLeavesRunThroughW895W894",
      "w1513RouteDataProviderRunsThroughW895W894",
      "w1513DirectCalculusRunsThroughW895W894",
      "w1513StablePackageRunsThroughW895W894",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513_count"]
  targetBranchResult :=
    "proved: W1512's W898/W897 endpoint-homology-free surface composes with\
      W1381's W897 closed-embedding branch convergence into W895"
  relationRouteResult :=
    "proved: W1513 further composes the concrete leaves, route data, direct\
      calculus, and stable package through W895 into the W894 relation route"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513
  w897RemainingInputs :=
    closedEmbeddingClosednessFieldsComparisonStableExactAtInputNamesW897
  w895RemainingInputs :=
    targetSurjectiveCompactFieldsComparisonStableExactAtInputNamesW895
  productSuccessClaimed := false

theorem currentW1513W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceStateW1513.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
