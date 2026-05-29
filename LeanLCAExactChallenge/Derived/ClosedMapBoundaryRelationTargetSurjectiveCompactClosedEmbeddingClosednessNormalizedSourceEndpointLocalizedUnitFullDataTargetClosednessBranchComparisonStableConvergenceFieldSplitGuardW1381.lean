import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataStrictPreimageBoundaryRelationComparisonStableConvergenceFieldSplitGuardW1380
import LeanLCAExactChallenge.Derived.ClosedMapClosednessFieldsComparisonStableExactAtRoute
import LeanLCAExactChallenge.Derived.ClosedEmbeddingClosednessFieldsComparisonStableExactAtRoute

/-!
W1381 records the definitional convergence of the W895/W896/W897 comparison
stable ExactAt route from target-surjective/compact fields and explicit
closed-map/closed-embedding closedness branch fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W895 target provider is assembled from target-surjectivity and target-compactness. -/
theorem w895TargetSurjectiveCompactRunsThroughFieldsW1381
    (targetDifferenceSurjectiveForTargetProvider :
      TargetDifferenceSurjectiveForTargetProviderW713)
    (targetCodomainCompactSpaceProvider :
      TargetCodomainCompactSpaceProviderW601) :
    targetSurjectiveCompactForTargetOfFieldsW895
        targetDifferenceSurjectiveForTargetProvider
        targetCodomainCompactSpaceProvider =
      fun Y =>
        ⟨targetDifferenceSurjectiveForTargetProvider Y,
          targetCodomainCompactSpaceProvider Y⟩ :=
  rfl

/-- W895 concrete leaves delegate to W894 after target-field assembly. -/
theorem w895ConcreteLeavesRunThroughW894W1381
    (leaves : MetrizableWppTargetSurjectiveCompactFieldLeavesW895) :
    concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895 leaves =
      concreteLeavesOfRelationFieldsComparisonW894
        (relationFieldLeavesOfTargetSurjectiveCompactFieldsW895 leaves) :=
  rfl

/-- W895 route data delegates to W894 after target-field assembly. -/
theorem w895RouteDataProviderRunsThroughW894W1381
    (leaves : MetrizableWppTargetSurjectiveCompactFieldLeavesW895) :
    routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895 leaves =
      routeDataProviderOfRelationFieldsComparisonW894
        (relationFieldLeavesOfTargetSurjectiveCompactFieldsW895 leaves) :=
  rfl

/-- W895 direct calculus delegates to W894 after target-field assembly. -/
theorem w895DirectCalculusRunsThroughW894W1381
    (leaves : MetrizableWppTargetSurjectiveCompactFieldLeavesW895) :
    directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        leaves =
      directBoundedLeftCalculusOfRelationFieldsComparisonStableExactAtW894
        (relationFieldLeavesOfTargetSurjectiveCompactFieldsW895 leaves) :=
  rfl

/-- W895 stable package delegates to W894 after target-field assembly. -/
theorem w895StablePackageRunsThroughW894W1381
    (leaves : MetrizableWppTargetSurjectiveCompactFieldLeavesW895) :
    boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        leaves =
      boundedDerivedInfinityCategoryOfRelationFieldsComparisonStableExactAtW894
        (relationFieldLeavesOfTargetSurjectiveCompactFieldsW895 leaves) :=
  rfl

/-- W896 W725 closed-map branch is assembled from closed-map branch fields. -/
theorem w896ClosedMapClosednessDataRunsThroughFieldsW1381
    (globalClosedMapComponents :
      SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    diagramAndMappedCokernelClosednessDataOfClosedMapFieldsW896
        globalClosedMapComponents mappedCokernelClosedMapProvider =
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725.closedMap
        globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W896 concrete leaves delegate to W895 after closed-map branch assembly. -/
theorem w896ConcreteLeavesRunThroughW895W1381
    (leaves : MetrizableWppClosedMapClosednessFieldLeavesW896) :
    concreteLeavesOfClosedMapClosednessFieldsComparisonW896 leaves =
      concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfClosedMapClosednessFieldsW896
          leaves) :=
  rfl

/-- W896 route data delegates to W895 after closed-map branch assembly. -/
theorem w896RouteDataProviderRunsThroughW895W1381
    (leaves : MetrizableWppClosedMapClosednessFieldLeavesW896) :
    routeDataProviderOfClosedMapClosednessFieldsComparisonW896 leaves =
      routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfClosedMapClosednessFieldsW896
          leaves) :=
  rfl

/-- W896 direct calculus delegates to W895 after closed-map branch assembly. -/
theorem w896DirectCalculusRunsThroughW895W1381
    (leaves : MetrizableWppClosedMapClosednessFieldLeavesW896) :
    directBoundedLeftCalculusOfClosedMapClosednessFieldsComparisonStableExactAtW896
        leaves =
      directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfClosedMapClosednessFieldsW896
          leaves) :=
  rfl

/-- W896 stable package delegates to W895 after closed-map branch assembly. -/
theorem w896StablePackageRunsThroughW895W1381
    (leaves : MetrizableWppClosedMapClosednessFieldLeavesW896) :
    boundedDerivedInfinityCategoryOfClosedMapClosednessFieldsComparisonStableExactAtW896
        leaves =
      boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfClosedMapClosednessFieldsW896
          leaves) :=
  rfl

/-- W897 W725 closed-embedding branch is assembled from closed-embedding branch fields. -/
theorem w897ClosedEmbeddingClosednessDataRunsThroughFieldsW1381
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    diagramAndMappedCokernelClosednessDataOfClosedEmbeddingFieldsW897
        globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725.closedEmbedding
        globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W897 concrete leaves delegate to W895 after closed-embedding branch assembly. -/
theorem w897ConcreteLeavesRunThroughW895W1381
    (leaves : MetrizableWppClosedEmbeddingClosednessFieldLeavesW897) :
    concreteLeavesOfClosedEmbeddingClosednessFieldsComparisonW897 leaves =
      concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
          leaves) :=
  rfl

/-- W897 route data delegates to W895 after closed-embedding branch assembly. -/
theorem w897RouteDataProviderRunsThroughW895W1381
    (leaves : MetrizableWppClosedEmbeddingClosednessFieldLeavesW897) :
    routeDataProviderOfClosedEmbeddingClosednessFieldsComparisonW897 leaves =
      routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
          leaves) :=
  rfl

/-- W897 direct calculus delegates to W895 after closed-embedding branch assembly. -/
theorem w897DirectCalculusRunsThroughW895W1381
    (leaves : MetrizableWppClosedEmbeddingClosednessFieldLeavesW897) :
    directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
        leaves =
      directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
          leaves) :=
  rfl

/-- W897 stable package delegates to W895 after closed-embedding branch assembly. -/
theorem w897StablePackageRunsThroughW895W1381
    (leaves : MetrizableWppClosedEmbeddingClosednessFieldLeavesW897) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
        leaves =
      boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
        (targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
          leaves) :=
  rfl

/-- W1381 keeps the W895 target-field count visible. -/
theorem w1381TargetSurjectiveCompactFieldsComparisonStableExactAtInputCountMatchesW895 :
    targetSurjectiveCompactFieldsComparisonStableExactAtInputNamesW895.length =
      37 :=
  targetSurjectiveCompactFieldsComparisonStableExactAtInputNamesW895_count

/-- W1381 keeps the W896 closed-map branch-field count visible. -/
theorem w1381ClosedMapClosednessFieldsComparisonStableExactAtInputCountMatchesW896 :
    closedMapClosednessFieldsComparisonStableExactAtInputNamesW896.length =
      38 :=
  closedMapClosednessFieldsComparisonStableExactAtInputNamesW896_count

/-- W1381 keeps the W897 closed-embedding branch-field count visible. -/
theorem
    w1381ClosedEmbeddingClosednessFieldsComparisonStableExactAtInputCountMatchesW897 :
    closedEmbeddingClosednessFieldsComparisonStableExactAtInputNamesW897.length =
      38 :=
  closedEmbeddingClosednessFieldsComparisonStableExactAtInputNamesW897_count

/-- Current W1381 nonterminal state. -/
structure TargetClosednessBranchComparisonStableConvergenceStateW1381 :
    Type where
  seed : String
  declarations : List String
  targetFieldResult : String
  closedMapBranchResult : String
  closedEmbeddingBranchResult : String
  remainingClosedMapInputs : List String
  remainingClosedEmbeddingInputs : List String
  productSuccessClaimed : Bool

/-- W1381 records W895-W897 convergence into the comparison stable ExactAt route. -/
def currentTargetClosednessBranchComparisonStableConvergenceStateW1381 :
    TargetClosednessBranchComparisonStableConvergenceStateW1381 where
  seed := "w1381-target-closedness-branch-comparison-stable-convergence"
  declarations :=
    ["w895TargetSurjectiveCompactRunsThroughFieldsW1381",
      "w895ConcreteLeavesRunThroughW894W1381",
      "w895RouteDataProviderRunsThroughW894W1381",
      "w895DirectCalculusRunsThroughW894W1381",
      "w895StablePackageRunsThroughW894W1381",
      "w896ClosedMapClosednessDataRunsThroughFieldsW1381",
      "w896ConcreteLeavesRunThroughW895W1381",
      "w896RouteDataProviderRunsThroughW895W1381",
      "w896DirectCalculusRunsThroughW895W1381",
      "w896StablePackageRunsThroughW895W1381",
      "w897ClosedEmbeddingClosednessDataRunsThroughFieldsW1381",
      "w897ConcreteLeavesRunThroughW895W1381",
      "w897RouteDataProviderRunsThroughW895W1381",
      "w897DirectCalculusRunsThroughW895W1381",
      "w897StablePackageRunsThroughW895W1381",
      "w1381TargetSurjectiveCompactFieldsComparisonStableExactAtInputCountMatchesW895",
      "w1381ClosedMapClosednessFieldsComparisonStableExactAtInputCountMatchesW896",
      "w1381ClosedEmbeddingClosednessFieldsComparisonStableExactAtInputCountMatchesW897"]
  targetFieldResult :=
    "proved: W895 assembles W715 target-surjective-compact data from explicit \
      target fields and delegates to W894"
  closedMapBranchResult :=
    "proved: W896 assembles the W725 closed-map branch and delegates to W895"
  closedEmbeddingBranchResult :=
    "proved: W897 assembles the W725 closed-embedding branch and delegates to W895"
  remainingClosedMapInputs :=
    closedMapClosednessFieldsComparisonStableExactAtInputNamesW896
  remainingClosedEmbeddingInputs :=
    closedEmbeddingClosednessFieldsComparisonStableExactAtInputNamesW897
  productSuccessClaimed := false

theorem currentW1381TargetClosednessBranchComparisonStableConvergence_productSuccess :
    currentTargetClosednessBranchComparisonStableConvergenceStateW1381.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
