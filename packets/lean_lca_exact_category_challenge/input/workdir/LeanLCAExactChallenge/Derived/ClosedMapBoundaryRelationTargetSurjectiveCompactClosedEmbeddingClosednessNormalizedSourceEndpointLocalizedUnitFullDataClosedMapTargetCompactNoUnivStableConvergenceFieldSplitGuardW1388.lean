import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapPrimitiveTargetStableConvergenceFieldSplitGuardW1387
import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipPrimitiveFieldRoute

/-!
W1388 records definitional convergence for the closed-map W925-W930
target-compactness refinement chain, from filter compactness through cluster,
nonbottom, outer-nonbottom, no-principal, and no-univ-membership primitive
surfaces.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W925 concrete leaves delegate to W924 after filter compactness primitive bundling. -/
theorem w925ConcreteLeavesRunThroughW924W1388
    (leaves : MetrizableWppClosedMapTargetCompactFilterPrimitiveFieldLeavesW925) :
    concreteLeavesOfClosedMapTargetCompactFilterPrimitiveFieldsW925 leaves =
      concreteLeavesOfClosedMapTargetCompactPrimitiveFieldsW924
        (w924LeavesOfTargetCompactFilterPrimitiveFieldsW925 leaves) :=
  rfl

/-- W925 route data delegates to W924 after filter compactness primitive bundling. -/
theorem w925RouteDataProviderRunsThroughW924W1388
    (leaves : MetrizableWppClosedMapTargetCompactFilterPrimitiveFieldLeavesW925) :
    routeDataProviderOfClosedMapTargetCompactFilterPrimitiveFieldsW925 leaves =
      routeDataProviderOfClosedMapTargetCompactPrimitiveFieldsW924
        (w924LeavesOfTargetCompactFilterPrimitiveFieldsW925 leaves) :=
  rfl

/-- W925 direct calculus delegates to W924 after filter compactness primitive bundling. -/
theorem w925DirectCalculusRunsThroughW924W1388
    (leaves : MetrizableWppClosedMapTargetCompactFilterPrimitiveFieldLeavesW925) :
    directBoundedLeftCalculusOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactPrimitiveFieldsW924
        (w924LeavesOfTargetCompactFilterPrimitiveFieldsW925 leaves) :=
  rfl

/-- W925 stable package delegates to W924 after filter compactness primitive bundling. -/
theorem w925StablePackageRunsThroughW924W1388
    (leaves : MetrizableWppClosedMapTargetCompactFilterPrimitiveFieldLeavesW925) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactPrimitiveFieldsW924
        (w924LeavesOfTargetCompactFilterPrimitiveFieldsW925 leaves) :=
  rfl

/-- W926 concrete leaves delegate to W925 after cluster compactness primitive bundling. -/
theorem w926ConcreteLeavesRunThroughW925W1388
    (leaves : MetrizableWppClosedMapTargetCompactClusterPrimitiveFieldLeavesW926) :
    concreteLeavesOfClosedMapTargetCompactClusterPrimitiveFieldsW926 leaves =
      concreteLeavesOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        (w925LeavesOfTargetCompactClusterPrimitiveFieldsW926 leaves) :=
  rfl

/-- W926 route data delegates to W925 after cluster compactness primitive bundling. -/
theorem w926RouteDataProviderRunsThroughW925W1388
    (leaves : MetrizableWppClosedMapTargetCompactClusterPrimitiveFieldLeavesW926) :
    routeDataProviderOfClosedMapTargetCompactClusterPrimitiveFieldsW926 leaves =
      routeDataProviderOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        (w925LeavesOfTargetCompactClusterPrimitiveFieldsW926 leaves) :=
  rfl

/-- W926 direct calculus delegates to W925 after cluster compactness primitive bundling. -/
theorem w926DirectCalculusRunsThroughW925W1388
    (leaves : MetrizableWppClosedMapTargetCompactClusterPrimitiveFieldLeavesW926) :
    directBoundedLeftCalculusOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        (w925LeavesOfTargetCompactClusterPrimitiveFieldsW926 leaves) :=
  rfl

/-- W926 stable package delegates to W925 after cluster compactness primitive bundling. -/
theorem w926StablePackageRunsThroughW925W1388
    (leaves : MetrizableWppClosedMapTargetCompactClusterPrimitiveFieldLeavesW926) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactFilterPrimitiveFieldsW925
        (w925LeavesOfTargetCompactClusterPrimitiveFieldsW926 leaves) :=
  rfl

/-- W927 concrete leaves delegate to W926 after nonbottom compactness primitive bundling. -/
theorem w927ConcreteLeavesRunThroughW926W1388
    (leaves : MetrizableWppClosedMapTargetCompactNonbottomPrimitiveFieldLeavesW927) :
    concreteLeavesOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927 leaves =
      concreteLeavesOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        (w926LeavesOfTargetCompactNonbottomPrimitiveFieldsW927 leaves) :=
  rfl

/-- W927 route data delegates to W926 after nonbottom compactness primitive bundling. -/
theorem w927RouteDataProviderRunsThroughW926W1388
    (leaves : MetrizableWppClosedMapTargetCompactNonbottomPrimitiveFieldLeavesW927) :
    routeDataProviderOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927 leaves =
      routeDataProviderOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        (w926LeavesOfTargetCompactNonbottomPrimitiveFieldsW927 leaves) :=
  rfl

/-- W927 direct calculus delegates to W926 after nonbottom compactness primitive bundling. -/
theorem w927DirectCalculusRunsThroughW926W1388
    (leaves : MetrizableWppClosedMapTargetCompactNonbottomPrimitiveFieldLeavesW927) :
    directBoundedLeftCalculusOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        (w926LeavesOfTargetCompactNonbottomPrimitiveFieldsW927 leaves) :=
  rfl

/-- W927 stable package delegates to W926 after nonbottom compactness primitive bundling. -/
theorem w927StablePackageRunsThroughW926W1388
    (leaves : MetrizableWppClosedMapTargetCompactNonbottomPrimitiveFieldLeavesW927) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactClusterPrimitiveFieldsW926
        (w926LeavesOfTargetCompactNonbottomPrimitiveFieldsW927 leaves) :=
  rfl

/-- W928 concrete leaves delegate to W927 after outer-nonbottom compactness primitive bundling. -/
theorem w928ConcreteLeavesRunThroughW927W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactOuterNonbottomPrimitiveFieldLeavesW928) :
    concreteLeavesOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        leaves =
      concreteLeavesOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        (w927LeavesOfTargetCompactOuterNonbottomPrimitiveFieldsW928 leaves) :=
  rfl

/-- W928 route data delegates to W927 after outer-nonbottom compactness primitive bundling. -/
theorem w928RouteDataProviderRunsThroughW927W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactOuterNonbottomPrimitiveFieldLeavesW928) :
    routeDataProviderOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        leaves =
      routeDataProviderOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        (w927LeavesOfTargetCompactOuterNonbottomPrimitiveFieldsW928 leaves) :=
  rfl

/-- W928 direct calculus delegates to W927 after outer-nonbottom compactness primitive bundling. -/
theorem w928DirectCalculusRunsThroughW927W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactOuterNonbottomPrimitiveFieldLeavesW928) :
    directBoundedLeftCalculusOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        (w927LeavesOfTargetCompactOuterNonbottomPrimitiveFieldsW928 leaves) :=
  rfl

/-- W928 stable package delegates to W927 after outer-nonbottom compactness primitive bundling. -/
theorem w928StablePackageRunsThroughW927W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactOuterNonbottomPrimitiveFieldLeavesW928) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactNonbottomPrimitiveFieldsW927
        (w927LeavesOfTargetCompactOuterNonbottomPrimitiveFieldsW928 leaves) :=
  rfl

/-- W929 concrete leaves delegate to W928 after no-principal compactness primitive bundling. -/
theorem w929ConcreteLeavesRunThroughW928W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoPrincipalPrimitiveFieldLeavesW929) :
    concreteLeavesOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929 leaves =
      concreteLeavesOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        (w928LeavesOfTargetCompactNoPrincipalPrimitiveFieldsW929 leaves) :=
  rfl

/-- W929 route data delegates to W928 after no-principal compactness primitive bundling. -/
theorem w929RouteDataProviderRunsThroughW928W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoPrincipalPrimitiveFieldLeavesW929) :
    routeDataProviderOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929 leaves =
      routeDataProviderOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        (w928LeavesOfTargetCompactNoPrincipalPrimitiveFieldsW929 leaves) :=
  rfl

/-- W929 direct calculus delegates to W928 after no-principal compactness primitive bundling. -/
theorem w929DirectCalculusRunsThroughW928W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoPrincipalPrimitiveFieldLeavesW929) :
    directBoundedLeftCalculusOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        (w928LeavesOfTargetCompactNoPrincipalPrimitiveFieldsW929 leaves) :=
  rfl

/-- W929 stable package delegates to W928 after no-principal compactness primitive bundling. -/
theorem w929StablePackageRunsThroughW928W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoPrincipalPrimitiveFieldLeavesW929) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactOuterNonbottomPrimitiveFieldsW928
        (w928LeavesOfTargetCompactNoPrincipalPrimitiveFieldsW929 leaves) :=
  rfl

/-- W930 concrete leaves delegate to W929 after no-univ-membership compactness primitive bundling. -/
theorem w930ConcreteLeavesRunThroughW929W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoUnivMembershipPrimitiveFieldLeavesW930) :
    concreteLeavesOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        leaves =
      concreteLeavesOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        (w929LeavesOfTargetCompactNoUnivMembershipPrimitiveFieldsW930 leaves) :=
  rfl

/-- W930 route data delegates to W929 after no-univ-membership compactness primitive bundling. -/
theorem w930RouteDataProviderRunsThroughW929W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoUnivMembershipPrimitiveFieldLeavesW930) :
    routeDataProviderOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        leaves =
      routeDataProviderOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        (w929LeavesOfTargetCompactNoUnivMembershipPrimitiveFieldsW930 leaves) :=
  rfl

/-- W930 direct calculus delegates to W929 after no-univ-membership compactness primitive bundling. -/
theorem w930DirectCalculusRunsThroughW929W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoUnivMembershipPrimitiveFieldLeavesW930) :
    directBoundedLeftCalculusOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        (w929LeavesOfTargetCompactNoUnivMembershipPrimitiveFieldsW930 leaves) :=
  rfl

/-- W930 stable package delegates to W929 after no-univ-membership compactness primitive bundling. -/
theorem w930StablePackageRunsThroughW929W1388
    (leaves :
      MetrizableWppClosedMapTargetCompactNoUnivMembershipPrimitiveFieldLeavesW930) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactNoPrincipalPrimitiveFieldsW929
        (w929LeavesOfTargetCompactNoUnivMembershipPrimitiveFieldsW930 leaves) :=
  rfl

/-- W1388 keeps W925-W930 input counts visible. -/
theorem w1388ClosedMapW925ToW930InputCounts :
    closedMapTargetCompactFilterPrimitiveFieldsInputNamesW925.length = 39 ∧
      closedMapTargetCompactClusterPrimitiveFieldsInputNamesW926.length = 39 ∧
      closedMapTargetCompactNonbottomPrimitiveFieldsInputNamesW927.length = 39 ∧
      closedMapTargetCompactOuterNonbottomPrimitiveFieldsInputNamesW928.length = 39 ∧
      closedMapTargetCompactNoPrincipalPrimitiveFieldsInputNamesW929.length = 39 ∧
      closedMapTargetCompactNoUnivMembershipPrimitiveFieldsInputNamesW930.length = 39 :=
  ⟨closedMapTargetCompactFilterPrimitiveFieldsInputNamesW925_count,
    closedMapTargetCompactClusterPrimitiveFieldsInputNamesW926_count,
    closedMapTargetCompactNonbottomPrimitiveFieldsInputNamesW927_count,
    closedMapTargetCompactOuterNonbottomPrimitiveFieldsInputNamesW928_count,
    closedMapTargetCompactNoPrincipalPrimitiveFieldsInputNamesW929_count,
    closedMapTargetCompactNoUnivMembershipPrimitiveFieldsInputNamesW930_count⟩

/-- Current W1388 nonterminal state. -/
structure ClosedMapTargetCompactNoUnivStableConvergenceStateW1388 :
    Type where
  seed : String
  declarations : List String
  filterPrimitiveResult : String
  clusterPrimitiveResult : String
  nonbottomPrimitiveResult : String
  outerNonbottomPrimitiveResult : String
  noPrincipalPrimitiveResult : String
  noUnivMembershipPrimitiveResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1388 records W925-W930 convergence into the closed-map stable route. -/
def currentClosedMapTargetCompactNoUnivStableConvergenceStateW1388 :
    ClosedMapTargetCompactNoUnivStableConvergenceStateW1388 where
  seed := "w1388-closed-map-target-compact-no-univ-stable-convergence"
  declarations :=
    ["w925ConcreteLeavesRunThroughW924W1388",
      "w925RouteDataProviderRunsThroughW924W1388",
      "w925DirectCalculusRunsThroughW924W1388",
      "w925StablePackageRunsThroughW924W1388",
      "w926ConcreteLeavesRunThroughW925W1388",
      "w926RouteDataProviderRunsThroughW925W1388",
      "w926DirectCalculusRunsThroughW925W1388",
      "w926StablePackageRunsThroughW925W1388",
      "w927ConcreteLeavesRunThroughW926W1388",
      "w927RouteDataProviderRunsThroughW926W1388",
      "w927DirectCalculusRunsThroughW926W1388",
      "w927StablePackageRunsThroughW926W1388",
      "w928ConcreteLeavesRunThroughW927W1388",
      "w928RouteDataProviderRunsThroughW927W1388",
      "w928DirectCalculusRunsThroughW927W1388",
      "w928StablePackageRunsThroughW927W1388",
      "w929ConcreteLeavesRunThroughW928W1388",
      "w929RouteDataProviderRunsThroughW928W1388",
      "w929DirectCalculusRunsThroughW928W1388",
      "w929StablePackageRunsThroughW928W1388",
      "w930ConcreteLeavesRunThroughW929W1388",
      "w930RouteDataProviderRunsThroughW929W1388",
      "w930DirectCalculusRunsThroughW929W1388",
      "w930StablePackageRunsThroughW929W1388",
      "w1388ClosedMapW925ToW930InputCounts"]
  filterPrimitiveResult :=
    "proved: W925 filter compactness primitive delegates into W924"
  clusterPrimitiveResult :=
    "proved: W926 cluster compactness primitive delegates into W925"
  nonbottomPrimitiveResult :=
    "proved: W927 nonbottom compactness primitive delegates into W926"
  outerNonbottomPrimitiveResult :=
    "proved: W928 outer-nonbottom compactness primitive delegates into W927"
  noPrincipalPrimitiveResult :=
    "proved: W929 no-principal compactness primitive delegates into W928"
  noUnivMembershipPrimitiveResult :=
    "proved: W930 no-univ-membership compactness primitive delegates into W929"
  remainingInputs :=
    closedMapTargetCompactNoUnivMembershipPrimitiveFieldsInputNamesW930
  productSuccessClaimed := false

theorem currentW1388ClosedMapTargetCompactNoUnivStableConvergence_productSuccess :
    currentClosedMapTargetCompactNoUnivStableConvergenceStateW1388.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
