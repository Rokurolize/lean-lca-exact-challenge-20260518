import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataLocalizedNormalizedStrictRepresentativeComparisonStableConvergenceFieldSplitGuardW1379
import LeanLCAExactChallenge.Derived.RelationFieldsComparisonStableExactAtRoute

/-!
W1380 records the definitional convergence of the W891/W892/W893/W894
comparison stable ExactAt route from strict-preimage object/map fields through
explicit WPP boundary and relation fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W891 concrete leaves delegate to W890 after strict-preimage object-field assembly. -/
theorem w891ConcreteLeavesRunThroughW890W1380
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    concreteLeavesOfStrictPreimageObjectFieldsComparisonW891 leaves =
      concreteLeavesOfStrictRepresentativeFieldsComparisonW890
        (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves) :=
  rfl

/-- W891 route data delegates to W890 after strict-preimage object-field assembly. -/
theorem w891RouteDataProviderRunsThroughW890W1380
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    routeDataProviderOfStrictPreimageObjectFieldsComparisonW891 leaves =
      routeDataProviderOfStrictRepresentativeFieldsComparisonW890
        (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves) :=
  rfl

/-- W891 direct calculus delegates to W890 after strict-preimage object-field assembly. -/
theorem w891DirectCalculusRunsThroughW890W1380
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        leaves =
      directBoundedLeftCalculusOfStrictRepresentativeFieldsComparisonStableExactAtW890
        (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves) :=
  rfl

/-- W891 stable package delegates to W890 after strict-preimage object-field assembly. -/
theorem w891StablePackageRunsThroughW890W1380
    (leaves : MetrizableWppStrictPreimageObjectFieldLeavesW891) :
    boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        leaves =
      boundedDerivedInfinityCategoryOfStrictRepresentativeFieldsComparisonStableExactAtW890
        (strictRepresentativeFieldLeavesOfObjectFieldsW891 leaves) :=
  rfl

/-- W892 concrete leaves delegate to W891 after strict-preimage map-field assembly. -/
theorem w892ConcreteLeavesRunThroughW891W1380
    (leaves : MetrizableWppStrictPreimageMapFieldLeavesW892) :
    concreteLeavesOfStrictPreimageMapFieldsComparisonW892 leaves =
      concreteLeavesOfStrictPreimageObjectFieldsComparisonW891
        (strictRepresentativeObjectFieldLeavesOfMapFieldsW892 leaves) :=
  rfl

/-- W892 route data delegates to W891 after strict-preimage map-field assembly. -/
theorem w892RouteDataProviderRunsThroughW891W1380
    (leaves : MetrizableWppStrictPreimageMapFieldLeavesW892) :
    routeDataProviderOfStrictPreimageMapFieldsComparisonW892 leaves =
      routeDataProviderOfStrictPreimageObjectFieldsComparisonW891
        (strictRepresentativeObjectFieldLeavesOfMapFieldsW892 leaves) :=
  rfl

/-- W892 direct calculus delegates to W891 after strict-preimage map-field assembly. -/
theorem w892DirectCalculusRunsThroughW891W1380
    (leaves : MetrizableWppStrictPreimageMapFieldLeavesW892) :
    directBoundedLeftCalculusOfStrictPreimageMapFieldsComparisonStableExactAtW892
        leaves =
      directBoundedLeftCalculusOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        (strictRepresentativeObjectFieldLeavesOfMapFieldsW892 leaves) :=
  rfl

/-- W892 stable package delegates to W891 after strict-preimage map-field assembly. -/
theorem w892StablePackageRunsThroughW891W1380
    (leaves : MetrizableWppStrictPreimageMapFieldLeavesW892) :
    boundedDerivedInfinityCategoryOfStrictPreimageMapFieldsComparisonStableExactAtW892
        leaves =
      boundedDerivedInfinityCategoryOfStrictPreimageObjectFieldsComparisonStableExactAtW891
        (strictRepresentativeObjectFieldLeavesOfMapFieldsW892 leaves) :=
  rfl

/-- W893 boundary data is assembled from the right-open and source-pi-zero fields. -/
theorem w893BoundaryDataRunsThroughFieldsW1380
    (rightOpenBoundary :
      Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary)
    (sourcePiZeroBoundary :
      Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary) :
    boundaryDataOfFieldsW893 rightOpenBoundary sourcePiZeroBoundary =
      { rightOpenBoundary := rightOpenBoundary
        sourcePiZeroBoundary := sourcePiZeroBoundary } :=
  rfl

/-- W893 concrete leaves delegate to W892 after boundary-field assembly. -/
theorem w893ConcreteLeavesRunThroughW892W1380
    (leaves : MetrizableWppBoundaryFieldLeavesW893) :
    concreteLeavesOfBoundaryFieldsComparisonW893 leaves =
      concreteLeavesOfStrictPreimageMapFieldsComparisonW892
        (strictPreimageMapFieldLeavesOfBoundaryFieldsW893 leaves) :=
  rfl

/-- W893 route data delegates to W892 after boundary-field assembly. -/
theorem w893RouteDataProviderRunsThroughW892W1380
    (leaves : MetrizableWppBoundaryFieldLeavesW893) :
    routeDataProviderOfBoundaryFieldsComparisonW893 leaves =
      routeDataProviderOfStrictPreimageMapFieldsComparisonW892
        (strictPreimageMapFieldLeavesOfBoundaryFieldsW893 leaves) :=
  rfl

/-- W893 direct calculus delegates to W892 after boundary-field assembly. -/
theorem w893DirectCalculusRunsThroughW892W1380
    (leaves : MetrizableWppBoundaryFieldLeavesW893) :
    directBoundedLeftCalculusOfBoundaryFieldsComparisonStableExactAtW893
        leaves =
      directBoundedLeftCalculusOfStrictPreimageMapFieldsComparisonStableExactAtW892
        (strictPreimageMapFieldLeavesOfBoundaryFieldsW893 leaves) :=
  rfl

/-- W893 stable package delegates to W892 after boundary-field assembly. -/
theorem w893StablePackageRunsThroughW892W1380
    (leaves : MetrizableWppBoundaryFieldLeavesW893) :
    boundedDerivedInfinityCategoryOfBoundaryFieldsComparisonStableExactAtW893
        leaves =
      boundedDerivedInfinityCategoryOfStrictPreimageMapFieldsComparisonStableExactAtW892
        (strictPreimageMapFieldLeavesOfBoundaryFieldsW893 leaves) :=
  rfl

/-- W894 relation data is assembled from relation-pullback and target-relation-lift fields. -/
theorem w894RelationDataRunsThroughFieldsW1380
    (relationPullbackProvider :
      ClosedNatTransOrdinaryRelationPullbackProviderW712)
    (targetRelationLiftsProvider :
      ClosedNatTransOrdinaryTargetRelationLiftsProviderW712) :
    relationDataOfFieldsW894 relationPullbackProvider
        targetRelationLiftsProvider =
      { relationPullbackProvider := relationPullbackProvider
        targetRelationLiftsProvider := targetRelationLiftsProvider } :=
  rfl

/-- W894 concrete leaves delegate to W893 after relation-field assembly. -/
theorem w894ConcreteLeavesRunThroughW893W1380
    (leaves : MetrizableWppRelationFieldLeavesW894) :
    concreteLeavesOfRelationFieldsComparisonW894 leaves =
      concreteLeavesOfBoundaryFieldsComparisonW893
        (boundaryFieldLeavesOfRelationFieldsW894 leaves) :=
  rfl

/-- W894 route data delegates to W893 after relation-field assembly. -/
theorem w894RouteDataProviderRunsThroughW893W1380
    (leaves : MetrizableWppRelationFieldLeavesW894) :
    routeDataProviderOfRelationFieldsComparisonW894 leaves =
      routeDataProviderOfBoundaryFieldsComparisonW893
        (boundaryFieldLeavesOfRelationFieldsW894 leaves) :=
  rfl

/-- W894 direct calculus delegates to W893 after relation-field assembly. -/
theorem w894DirectCalculusRunsThroughW893W1380
    (leaves : MetrizableWppRelationFieldLeavesW894) :
    directBoundedLeftCalculusOfRelationFieldsComparisonStableExactAtW894
        leaves =
      directBoundedLeftCalculusOfBoundaryFieldsComparisonStableExactAtW893
        (boundaryFieldLeavesOfRelationFieldsW894 leaves) :=
  rfl

/-- W894 stable package delegates to W893 after relation-field assembly. -/
theorem w894StablePackageRunsThroughW893W1380
    (leaves : MetrizableWppRelationFieldLeavesW894) :
    boundedDerivedInfinityCategoryOfRelationFieldsComparisonStableExactAtW894
        leaves =
      boundedDerivedInfinityCategoryOfBoundaryFieldsComparisonStableExactAtW893
        (boundaryFieldLeavesOfRelationFieldsW894 leaves) :=
  rfl

/-- W1380 keeps the W891 strict-preimage object-field count visible. -/
theorem w1380StrictPreimageObjectFieldsComparisonStableExactAtInputCountMatchesW891 :
    strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891.length =
      29 :=
  strictPreimageObjectFieldsComparisonStableExactAtInputNamesW891_count

/-- W1380 keeps the W892 strict-preimage map-field count visible. -/
theorem w1380StrictPreimageMapFieldsComparisonStableExactAtInputCountMatchesW892 :
    strictPreimageMapFieldsComparisonStableExactAtInputNamesW892.length =
      34 :=
  strictPreimageMapFieldsComparisonStableExactAtInputNamesW892_count

/-- W1380 keeps the W893 boundary-field count visible. -/
theorem w1380BoundaryFieldsComparisonStableExactAtInputCountMatchesW893 :
    boundaryFieldsComparisonStableExactAtInputNamesW893.length = 35 :=
  boundaryFieldsComparisonStableExactAtInputNamesW893_count

/-- W1380 keeps the W894 relation-field count visible. -/
theorem w1380RelationFieldsComparisonStableExactAtInputCountMatchesW894 :
    relationFieldsComparisonStableExactAtInputNamesW894.length = 36 :=
  relationFieldsComparisonStableExactAtInputNamesW894_count

/-- Current W1380 nonterminal state. -/
structure StrictPreimageBoundaryRelationComparisonStableConvergenceStateW1380 :
    Type where
  seed : String
  declarations : List String
  strictPreimageObjectResult : String
  strictPreimageMapResult : String
  boundaryFieldResult : String
  relationFieldResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1380 records W891-W894 convergence into the comparison stable ExactAt route. -/
def currentStrictPreimageBoundaryRelationComparisonStableConvergenceStateW1380 :
    StrictPreimageBoundaryRelationComparisonStableConvergenceStateW1380 where
  seed := "w1380-strict-preimage-boundary-relation-comparison-stable-convergence"
  declarations :=
    ["w891ConcreteLeavesRunThroughW890W1380",
      "w891RouteDataProviderRunsThroughW890W1380",
      "w891DirectCalculusRunsThroughW890W1380",
      "w891StablePackageRunsThroughW890W1380",
      "w892ConcreteLeavesRunThroughW891W1380",
      "w892RouteDataProviderRunsThroughW891W1380",
      "w892DirectCalculusRunsThroughW891W1380",
      "w892StablePackageRunsThroughW891W1380",
      "w893BoundaryDataRunsThroughFieldsW1380",
      "w893ConcreteLeavesRunThroughW892W1380",
      "w893RouteDataProviderRunsThroughW892W1380",
      "w893DirectCalculusRunsThroughW892W1380",
      "w893StablePackageRunsThroughW892W1380",
      "w894RelationDataRunsThroughFieldsW1380",
      "w894ConcreteLeavesRunThroughW893W1380",
      "w894RouteDataProviderRunsThroughW893W1380",
      "w894DirectCalculusRunsThroughW893W1380",
      "w894StablePackageRunsThroughW893W1380",
      "w1380StrictPreimageObjectFieldsComparisonStableExactAtInputCountMatchesW891",
      "w1380StrictPreimageMapFieldsComparisonStableExactAtInputCountMatchesW892",
      "w1380BoundaryFieldsComparisonStableExactAtInputCountMatchesW893",
      "w1380RelationFieldsComparisonStableExactAtInputCountMatchesW894"]
  strictPreimageObjectResult :=
    "proved: W891 delegates strict-preimage object fields to W890"
  strictPreimageMapResult :=
    "proved: W892 delegates strict-preimage map fields to W891"
  boundaryFieldResult :=
    "proved: W893 assembles W716 boundary data from explicit boundary fields \
      and delegates to W892"
  relationFieldResult :=
    "proved: W894 assembles W717 relation data from explicit relation fields \
      and delegates to W893"
  remainingInputs :=
    relationFieldsComparisonStableExactAtInputNamesW894
  productSuccessClaimed := false

theorem currentW1380StrictPreimageBoundaryRelationComparisonStableConvergence_productSuccess :
    currentStrictPreimageBoundaryRelationComparisonStableConvergenceStateW1380.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
