import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetClosednessBranchComparisonStableConvergenceFieldSplitGuardW1381
import LeanLCAExactChallenge.Derived.ClosedEmbeddingEndpointHomologyFreeComparisonStableExactAtRoute
import LeanLCAExactChallenge.Derived.ClosedMapEndpointHomologyFreeComparisonStableExactAtRoute

/-!
W1382 records the definitional convergence of the W898/W899 endpoint-homology-free
comparison stable ExactAt routes through the W856 closed-branch homology
derivations and W896/W897 closedness-field branches.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W898 endpoint homology preservation is exactly the W856 closed-embedding branch. -/
theorem w898EndpointHomologyRunsThroughW856W1382
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    endpointForgetPreservesHomologyOfClosedEmbeddingFieldsW898
        mappedCokernelClosedEmbeddingProvider =
      endpointForgetPreservesHomologyOfClosedEmbeddingW856
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W898 concrete leaves delegate to W897 after deriving endpoint homology. -/
theorem w898ConcreteLeavesRunThroughW897W1382
    (leaves : MetrizableWppClosedEmbeddingEndpointHomologyFreeLeavesW898) :
    concreteLeavesOfClosedEmbeddingEndpointHomologyFreeComparisonW898 leaves =
      concreteLeavesOfClosedEmbeddingClosednessFieldsComparisonW897
        (closedEmbeddingClosednessFieldLeavesOfEndpointHomologyFreeW898 leaves) :=
  rfl

/-- W898 route data delegates to W897 after deriving endpoint homology. -/
theorem w898RouteDataProviderRunsThroughW897W1382
    (leaves : MetrizableWppClosedEmbeddingEndpointHomologyFreeLeavesW898) :
    routeDataProviderOfClosedEmbeddingEndpointHomologyFreeComparisonW898 leaves =
      routeDataProviderOfClosedEmbeddingClosednessFieldsComparisonW897
        (closedEmbeddingClosednessFieldLeavesOfEndpointHomologyFreeW898 leaves) :=
  rfl

/-- W898 direct calculus delegates to W897 after deriving endpoint homology. -/
theorem w898DirectCalculusRunsThroughW897W1382
    (leaves : MetrizableWppClosedEmbeddingEndpointHomologyFreeLeavesW898) :
    directBoundedLeftCalculusOfClosedEmbeddingEndpointHomologyFreeComparisonStableExactAtW898
        leaves =
      directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
        (closedEmbeddingClosednessFieldLeavesOfEndpointHomologyFreeW898 leaves) :=
  rfl

/-- W898 stable package delegates to W897 after deriving endpoint homology. -/
theorem w898StablePackageRunsThroughW897W1382
    (leaves : MetrizableWppClosedEmbeddingEndpointHomologyFreeLeavesW898) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingEndpointHomologyFreeComparisonStableExactAtW898
        leaves =
      boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
        (closedEmbeddingClosednessFieldLeavesOfEndpointHomologyFreeW898 leaves) :=
  rfl

/-- W899 endpoint homology preservation is exactly the W856 closed-map branch. -/
theorem w899EndpointHomologyRunsThroughW856W1382
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    endpointForgetPreservesHomologyOfClosedMapFieldsW899
        mappedCokernelClosedMapProvider =
      endpointForgetPreservesHomologyOfClosedMapW856
        mappedCokernelClosedMapProvider :=
  rfl

/-- W899 concrete leaves delegate to W896 after deriving endpoint homology. -/
theorem w899ConcreteLeavesRunThroughW896W1382
    (leaves : MetrizableWppClosedMapEndpointHomologyFreeLeavesW899) :
    concreteLeavesOfClosedMapEndpointHomologyFreeComparisonW899 leaves =
      concreteLeavesOfClosedMapClosednessFieldsComparisonW896
        (closedMapClosednessFieldLeavesOfEndpointHomologyFreeW899 leaves) :=
  rfl

/-- W899 route data delegates to W896 after deriving endpoint homology. -/
theorem w899RouteDataProviderRunsThroughW896W1382
    (leaves : MetrizableWppClosedMapEndpointHomologyFreeLeavesW899) :
    routeDataProviderOfClosedMapEndpointHomologyFreeComparisonW899 leaves =
      routeDataProviderOfClosedMapClosednessFieldsComparisonW896
        (closedMapClosednessFieldLeavesOfEndpointHomologyFreeW899 leaves) :=
  rfl

/-- W899 direct calculus delegates to W896 after deriving endpoint homology. -/
theorem w899DirectCalculusRunsThroughW896W1382
    (leaves : MetrizableWppClosedMapEndpointHomologyFreeLeavesW899) :
    directBoundedLeftCalculusOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
        leaves =
      directBoundedLeftCalculusOfClosedMapClosednessFieldsComparisonStableExactAtW896
        (closedMapClosednessFieldLeavesOfEndpointHomologyFreeW899 leaves) :=
  rfl

/-- W899 stable package delegates to W896 after deriving endpoint homology. -/
theorem w899StablePackageRunsThroughW896W1382
    (leaves : MetrizableWppClosedMapEndpointHomologyFreeLeavesW899) :
    boundedDerivedInfinityCategoryOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapClosednessFieldsComparisonStableExactAtW896
        (closedMapClosednessFieldLeavesOfEndpointHomologyFreeW899 leaves) :=
  rfl

/-- W1382 keeps the W898 endpoint-homology-free branch-field count visible. -/
theorem
    w1382ClosedEmbeddingEndpointHomologyFreeComparisonStableExactAtInputCountMatchesW898 :
    closedEmbeddingEndpointHomologyFreeComparisonStableExactAtInputNamesW898.length =
      37 :=
  closedEmbeddingEndpointHomologyFreeComparisonStableExactAtInputNamesW898_count

/-- W1382 keeps the W899 endpoint-homology-free branch-field count visible. -/
theorem w1382ClosedMapEndpointHomologyFreeComparisonStableExactAtInputCountMatchesW899 :
    closedMapEndpointHomologyFreeComparisonStableExactAtInputNamesW899.length =
      37 :=
  closedMapEndpointHomologyFreeComparisonStableExactAtInputNamesW899_count

/-- Current W1382 nonterminal state. -/
structure EndpointHomologyFreeComparisonStableConvergenceStateW1382 :
    Type where
  seed : String
  declarations : List String
  closedEmbeddingEndpointHomologyResult : String
  closedMapEndpointHomologyResult : String
  remainingClosedEmbeddingInputs : List String
  remainingClosedMapInputs : List String
  productSuccessClaimed : Bool

/--
W1382 records W898/W899 convergence after removing the explicit endpoint
forgetful homology-preservation field from both closedness branches.
-/
def currentEndpointHomologyFreeComparisonStableConvergenceStateW1382 :
    EndpointHomologyFreeComparisonStableConvergenceStateW1382 where
  seed := "w1382-endpoint-homology-free-comparison-stable-convergence"
  declarations :=
    ["w898EndpointHomologyRunsThroughW856W1382",
      "w898ConcreteLeavesRunThroughW897W1382",
      "w898RouteDataProviderRunsThroughW897W1382",
      "w898DirectCalculusRunsThroughW897W1382",
      "w898StablePackageRunsThroughW897W1382",
      "w899EndpointHomologyRunsThroughW856W1382",
      "w899ConcreteLeavesRunThroughW896W1382",
      "w899RouteDataProviderRunsThroughW896W1382",
      "w899DirectCalculusRunsThroughW896W1382",
      "w899StablePackageRunsThroughW896W1382",
      "w1382ClosedEmbeddingEndpointHomologyFreeComparisonStableExactAtInputCountMatchesW898",
      "w1382ClosedMapEndpointHomologyFreeComparisonStableExactAtInputCountMatchesW899"]
  closedEmbeddingEndpointHomologyResult :=
    "proved: W898 derives closed-embedding endpoint homology preservation from \
      W519 mapped cokernel closed-embedding data through W856 and delegates to W897"
  closedMapEndpointHomologyResult :=
    "proved: W899 derives closed-map endpoint homology preservation from W519 \
      mapped cokernel closed-map data through W856 and delegates to W896"
  remainingClosedEmbeddingInputs :=
    closedEmbeddingEndpointHomologyFreeComparisonStableExactAtInputNamesW898
  remainingClosedMapInputs :=
    closedMapEndpointHomologyFreeComparisonStableExactAtInputNamesW899
  productSuccessClaimed := false

theorem currentW1382EndpointHomologyFreeComparisonStableConvergence_productSuccess :
    currentEndpointHomologyFreeComparisonStableConvergenceStateW1382.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
