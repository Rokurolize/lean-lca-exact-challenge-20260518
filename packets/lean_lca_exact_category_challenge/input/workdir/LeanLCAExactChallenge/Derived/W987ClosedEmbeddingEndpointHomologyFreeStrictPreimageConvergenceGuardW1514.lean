import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeTargetBranchConvergenceGuardW1513
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataStrictPreimageBoundaryRelationComparisonStableConvergenceFieldSplitGuardW1380

/-!
W1514 composes the W1513 W987 relation-route surface with the existing W1380
strict-preimage/boundary/relation convergence guard. W1513 reaches W894; W1380
records the W894-to-W893, W893-to-W892, W892-to-W891, and W891-to-W890
delegations.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

/-- W1514 reuses the W1513 target-branch convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputW1513

/-- W1514 names the W894 relation-field leaves reached by W1513. -/
def relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppRelationFieldLeavesW894 :=
  relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    input

/-- W1514 projects W1513's W894 leaves to W893 boundary-field leaves. -/
def boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppBoundaryFieldLeavesW893 :=
  boundaryFieldLeavesOfRelationFieldsW894
    (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input)

/-- W1514 projects W1513 through W893 to W892 strict-preimage map-field leaves. -/
def strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppStrictPreimageMapFieldLeavesW892 :=
  strictPreimageMapFieldLeavesOfBoundaryFieldsW893
    (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input)

/-- W1514 projects W1513 through W892 to W891 strict-preimage object-field leaves. -/
def strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppStrictPreimageObjectFieldLeavesW891 :=
  strictRepresentativeObjectFieldLeavesOfMapFieldsW892
    (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input)

/-- W1514 projects W1513 through W891 to W890 strict-representative leaves. -/
def strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppStrictRepresentativeLiftBlueprintFieldLeavesW890 :=
  strictRepresentativeFieldLeavesOfObjectFieldsW891
    (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input)

/-- W1514 exposes the same concrete leaves as W1513. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    input

/-- W1514 exposes the same route data as W1513. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    input

/-- W1514 exposes the same direct bounded left calculus package as W1513. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    input

/-- W1514 exposes the same bounded derived infinity-category package as W1513. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceW1513
    input

/-- W1514 specializes W1380's W894 relation-data assembly to W1513 leaves. -/
theorem w1514RelationDataRunsThroughW894W1380
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    relationDataOfFieldsW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input).relationPullbackProvider
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input).targetRelationLiftsProvider =
      { relationPullbackProvider :=
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input).relationPullbackProvider
        targetRelationLiftsProvider :=
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input).targetRelationLiftsProvider } :=
  w894RelationDataRunsThroughFieldsW1380
    (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input).relationPullbackProvider
    (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input).targetRelationLiftsProvider

/-- W1514 specializes W1380's W893 boundary-data assembly to W1513 leaves. -/
theorem w1514BoundaryDataRunsThroughW893W1380
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    boundaryDataOfFieldsW893
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input).rightOpenBoundary
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input).sourcePiZeroBoundary =
      { rightOpenBoundary :=
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input).rightOpenBoundary
        sourcePiZeroBoundary :=
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input).sourcePiZeroBoundary } :=
  w893BoundaryDataRunsThroughFieldsW1380
    (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input).rightOpenBoundary
    (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
      input).sourcePiZeroBoundary

/-- W1514 composes W1513's W894 route with W1380's W894-to-W893 step. -/
theorem w1514ConcreteLeavesRunThroughW894W893
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      concreteLeavesOfBoundaryFieldsComparisonW893
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        concreteLeavesOfRelationFieldsComparisonW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1513ConcreteLeavesRunThroughW895W894 input
    _ =
        concreteLeavesOfBoundaryFieldsComparisonW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w894ConcreteLeavesRunThroughW893W1380
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514RouteDataProviderRunsThroughW894W893
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      routeDataProviderOfBoundaryFieldsComparisonW893
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        routeDataProviderOfRelationFieldsComparisonW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1513RouteDataProviderRunsThroughW895W894 input
    _ =
        routeDataProviderOfBoundaryFieldsComparisonW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w894RouteDataProviderRunsThroughW893W1380
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514DirectCalculusRunsThroughW894W893
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      directBoundedLeftCalculusOfBoundaryFieldsComparisonStableExactAtW893
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        directBoundedLeftCalculusOfRelationFieldsComparisonStableExactAtW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1513DirectCalculusRunsThroughW895W894 input
    _ =
        directBoundedLeftCalculusOfBoundaryFieldsComparisonStableExactAtW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w894DirectCalculusRunsThroughW893W1380
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514StablePackageRunsThroughW894W893
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      boundedDerivedInfinityCategoryOfBoundaryFieldsComparisonStableExactAtW893
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        boundedDerivedInfinityCategoryOfRelationFieldsComparisonStableExactAtW894
          (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1513StablePackageRunsThroughW895W894 input
    _ =
        boundedDerivedInfinityCategoryOfBoundaryFieldsComparisonStableExactAtW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w894StablePackageRunsThroughW893W1380
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

/-- W1514 further composes through W893 to W892. -/
theorem w1514ConcreteLeavesRunThroughW893W892
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      concreteLeavesOfStrictPreimageMapFieldsComparisonW892
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        concreteLeavesOfBoundaryFieldsComparisonW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514ConcreteLeavesRunThroughW894W893 input
    _ =
        concreteLeavesOfStrictPreimageMapFieldsComparisonW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w893ConcreteLeavesRunThroughW892W1380
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514RouteDataProviderRunsThroughW893W892
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      routeDataProviderOfStrictPreimageMapFieldsComparisonW892
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        routeDataProviderOfBoundaryFieldsComparisonW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514RouteDataProviderRunsThroughW894W893 input
    _ =
        routeDataProviderOfStrictPreimageMapFieldsComparisonW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w893RouteDataProviderRunsThroughW892W1380
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514DirectCalculusRunsThroughW893W892
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      directBoundedLeftCalculusOfStrictPreimageMapFieldsComparisonStableExactAtW892
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        directBoundedLeftCalculusOfBoundaryFieldsComparisonStableExactAtW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514DirectCalculusRunsThroughW894W893 input
    _ =
        directBoundedLeftCalculusOfStrictPreimageMapFieldsComparisonStableExactAtW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w893DirectCalculusRunsThroughW892W1380
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514StablePackageRunsThroughW893W892
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      boundedDerivedInfinityCategoryOfStrictPreimageMapFieldsComparisonStableExactAtW892
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        boundedDerivedInfinityCategoryOfBoundaryFieldsComparisonStableExactAtW893
          (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514StablePackageRunsThroughW894W893 input
    _ =
        boundedDerivedInfinityCategoryOfStrictPreimageMapFieldsComparisonStableExactAtW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w893StablePackageRunsThroughW892W1380
        (boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

/-- W1514 further composes through W892 to W891. -/
theorem w1514ConcreteLeavesRunThroughW892W891
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      concreteLeavesOfStrictPreimageObjectFieldsComparisonW891
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        concreteLeavesOfStrictPreimageMapFieldsComparisonW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514ConcreteLeavesRunThroughW893W892 input
    _ =
        concreteLeavesOfStrictPreimageObjectFieldsComparisonW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w892ConcreteLeavesRunThroughW891W1380
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514RouteDataProviderRunsThroughW892W891
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      routeDataProviderOfStrictPreimageObjectFieldsComparisonW891
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        routeDataProviderOfStrictPreimageMapFieldsComparisonW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514RouteDataProviderRunsThroughW893W892 input
    _ =
        routeDataProviderOfStrictPreimageObjectFieldsComparisonW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w892RouteDataProviderRunsThroughW891W1380
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514DirectCalculusRunsThroughW892W891
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        directBoundedLeftCalculusOfStrictPreimageMapFieldsComparisonStableExactAtW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514DirectCalculusRunsThroughW893W892 input
    _ =
        directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w892DirectCalculusRunsThroughW891W1380
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514StablePackageRunsThroughW892W891
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        boundedDerivedInfinityCategoryOfStrictPreimageMapFieldsComparisonStableExactAtW892
          (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514StablePackageRunsThroughW893W892 input
    _ =
        boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w892StablePackageRunsThroughW891W1380
        (strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

/-- W1514 further composes through W891 to W890. -/
theorem w1514ConcreteLeavesRunThroughW891W890
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      concreteLeavesOfStrictRepresentativeFieldsComparisonW890
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        concreteLeavesOfStrictPreimageObjectFieldsComparisonW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514ConcreteLeavesRunThroughW892W891 input
    _ =
        concreteLeavesOfStrictRepresentativeFieldsComparisonW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w891ConcreteLeavesRunThroughW890W1380
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514RouteDataProviderRunsThroughW891W890
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      routeDataProviderOfStrictRepresentativeFieldsComparisonW890
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        routeDataProviderOfStrictPreimageObjectFieldsComparisonW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514RouteDataProviderRunsThroughW892W891 input
    _ =
        routeDataProviderOfStrictRepresentativeFieldsComparisonW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w891RouteDataProviderRunsThroughW890W1380
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514DirectCalculusRunsThroughW891W890
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514DirectCalculusRunsThroughW892W891 input
    _ =
        directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w891DirectCalculusRunsThroughW890W1380
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

theorem w1514StablePackageRunsThroughW891W890
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514) :
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
      boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
        (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input) := by
  calc
    boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
        input =
        boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
          (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w1514StablePackageRunsThroughW892W891 input
    _ =
        boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
          (strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
            input) :=
      w891StablePackageRunsThroughW890W1380
        (strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514
          input)

/-- W1514 keeps the W1513 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetBranchConvergenceInputNamesW1513_count

/-- Current W1514 nonterminal strict-preimage convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceStateW1514 :
    Type where
  seed : String
  declarations : List String
  relationBoundaryResult : String
  strictPreimageResult : String
  remainingInputs : List String
  w894RemainingInputs : List String
  w893RemainingInputs : List String
  w892RemainingInputs : List String
  w891RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1514 records the W1513-to-W1380 strict-preimage convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceStateW1514 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceStateW1514 where
  seed :=
    "w1514-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-strict-preimage-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputW1514",
      "relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514",
      "boundaryFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514",
      "strictPreimageMapFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514",
      "strictPreimageObjectFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514",
      "strictRepresentativeFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceW1514",
      "w1514RelationDataRunsThroughW894W1380",
      "w1514BoundaryDataRunsThroughW893W1380",
      "w1514ConcreteLeavesRunThroughW894W893",
      "w1514RouteDataProviderRunsThroughW894W893",
      "w1514DirectCalculusRunsThroughW894W893",
      "w1514StablePackageRunsThroughW894W893",
      "w1514ConcreteLeavesRunThroughW893W892",
      "w1514RouteDataProviderRunsThroughW893W892",
      "w1514DirectCalculusRunsThroughW893W892",
      "w1514StablePackageRunsThroughW893W892",
      "w1514ConcreteLeavesRunThroughW892W891",
      "w1514RouteDataProviderRunsThroughW892W891",
      "w1514DirectCalculusRunsThroughW892W891",
      "w1514StablePackageRunsThroughW892W891",
      "w1514ConcreteLeavesRunThroughW891W890",
      "w1514RouteDataProviderRunsThroughW891W890",
      "w1514DirectCalculusRunsThroughW891W890",
      "w1514StablePackageRunsThroughW891W890",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514_count"]
  relationBoundaryResult :=
    "proved: W1513's W894 relation route specializes W1380's W894-to-W893\
      relation and boundary convergence"
  strictPreimageResult :=
    "proved: W1514 further composes the concrete leaves, route data, direct\
      calculus, and stable package through W893, W892, W891, and W890"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceInputNamesW1514
  w894RemainingInputs :=
    relationFieldsComparisonStableExactAtInputNamesW894
  w893RemainingInputs :=
    boundaryFieldsComparisonStableExactAtInputNamesW893
  w892RemainingInputs :=
    strictPreimageMapFieldsComparisonStableExactAtInputNamesW892
  w891RemainingInputs :=
    strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891
  productSuccessClaimed := false

theorem currentW1514W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StrictPreimageConvergenceStateW1514.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
