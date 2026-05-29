import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW732W735SelectedCochainStableConvergenceFieldSplitGuardW1375
import LeanLCAExactChallenge.Derived.SelectedCochainConcreteLeavesStableExactAtRoute

/-!
W1376 records the definitional convergence of the W877/W878 concrete-leaves
selected-cochain stable ExactAt route into the W733/W855/W875 route-data
constructors already exposed by the previous field-split guards.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W877 route-data construction is exactly the W733 concrete-leaves constructor. -/
theorem w877RouteDataProviderRunsThroughW733W1376
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    routeDataProviderOfConcreteLeavesW877 leaves =
      boundaryRelationTargetClosednessNormalizedDataProvider_of_concreteLeavesW733
        leaves :=
  rfl

/-- W877 direct calculus delegates to W875 after W733 route-data construction. -/
theorem w877DirectCalculusRunsThroughW875W1376
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
        leaves =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfConcreteLeavesW877 leaves) :=
  rfl

/-- W877 stable package delegates to W875 after W733 route-data construction. -/
theorem w877StablePackageRunsThroughW875W1376
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
        leaves =
      boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfConcreteLeavesW877 leaves) :=
  rfl

/-- W878 closed-map concrete leaves are exactly the W855 concrete-leaves constructor. -/
theorem w878ClosedMapConcreteLeavesRunsThroughW855W1376
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    concreteLeavesOfClosedMapSelectedCochainDirectSourceW878 data =
      closedMapConcreteLeavesOfComparisonBijectivityW855 data.exactInputs :=
  rfl

/-- W878 closed-embedding concrete leaves are exactly the W855 concrete-leaves constructor. -/
theorem w878ClosedEmbeddingConcreteLeavesRunsThroughW855W1376
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878 data =
      closedEmbeddingConcreteLeavesOfComparisonBijectivityW855 data.exactInputs :=
  rfl

/-- W878 closed-map direct calculus delegates to W877 through W855 concrete leaves. -/
theorem w878ClosedMapDirectCalculusRunsThroughW877W1376
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    directBoundedLeftCalculusOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        data =
      directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
        (concreteLeavesOfClosedMapSelectedCochainDirectSourceW878 data) :=
  rfl

/-- W878 closed-embedding direct calculus delegates to W877 through W855 concrete leaves. -/
theorem w878ClosedEmbeddingDirectCalculusRunsThroughW877W1376
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        data =
      directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
        (concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878 data) :=
  rfl

/-- W878 closed-map stable package delegates to W877 through W855 concrete leaves. -/
theorem w878ClosedMapStablePackageRunsThroughW877W1376
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    boundedDerivedInfinityCategoryOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        data =
      boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
        (concreteLeavesOfClosedMapSelectedCochainDirectSourceW878 data) :=
  rfl

/-- W878 closed-embedding stable package delegates to W877 through W855 concrete leaves. -/
theorem w878ClosedEmbeddingStablePackageRunsThroughW877W1376
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        data =
      boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
        (concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878 data) :=
  rfl

/-- W1376 keeps the W877 concrete-leaves input count visible. -/
theorem w1376ConcreteLeavesSelectedCochainStableExactAtInputCountMatchesW877 :
    concreteLeavesSelectedCochainStableExactAtInputNamesW877.length = 8 :=
  concreteLeavesSelectedCochainStableExactAtInputNamesW877_count

/-- W1376 keeps the W878 selected-cochain direct-source input count visible. -/
theorem w1376SelectedCochainConcreteLeavesStableExactAtInputCountMatchesW878 :
    selectedCochainConcreteLeavesStableExactAtInputNamesW878.length = 1 :=
  selectedCochainConcreteLeavesStableExactAtInputNamesW878_count

/-- W1376 keeps the W878 expanded selected-cochain field count visible. -/
theorem w1376SelectedCochainConcreteLeavesStableExactAtExpandedInputCountMatchesW878 :
    selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878.length = 2 :=
  selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878_count

/-- Current W1376 nonterminal state. -/
structure ConcreteLeavesSelectedCochainStableConvergenceStateW1376 : Type where
  seed : String
  declarations : List String
  concreteLeavesRouteDataResult : String
  selectedCochainConcreteLeavesResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1376 records W877/W878 concrete-leaves convergence into stable ExactAt evidence. -/
def currentConcreteLeavesSelectedCochainStableConvergenceStateW1376 :
    ConcreteLeavesSelectedCochainStableConvergenceStateW1376 where
  seed := "w1376-concrete-leaves-selected-cochain-stable-convergence"
  declarations :=
    ["w877RouteDataProviderRunsThroughW733W1376",
      "w877DirectCalculusRunsThroughW875W1376",
      "w877StablePackageRunsThroughW875W1376",
      "w878ClosedMapConcreteLeavesRunsThroughW855W1376",
      "w878ClosedEmbeddingConcreteLeavesRunsThroughW855W1376",
      "w878ClosedMapDirectCalculusRunsThroughW877W1376",
      "w878ClosedEmbeddingDirectCalculusRunsThroughW877W1376",
      "w878ClosedMapStablePackageRunsThroughW877W1376",
      "w878ClosedEmbeddingStablePackageRunsThroughW877W1376",
      "w1376ConcreteLeavesSelectedCochainStableExactAtInputCountMatchesW877",
      "w1376SelectedCochainConcreteLeavesStableExactAtInputCountMatchesW878",
      "w1376SelectedCochainConcreteLeavesStableExactAtExpandedInputCountMatchesW878"]
  concreteLeavesRouteDataResult :=
    "proved: W877 W733 concrete leaves construct W732 route data and delegate \
      direct calculus/stable package to W875"
  selectedCochainConcreteLeavesResult :=
    "proved: W878 W847 selected-cochain direct-source data construct W733 \
      concrete leaves through W855 and delegate direct calculus/stable package \
      to W877"
  remainingInputs :=
    selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878
  productSuccessClaimed := false

theorem currentW1376ConcreteLeavesSelectedCochainStableConvergence_productSuccess :
    currentConcreteLeavesSelectedCochainStableConvergenceStateW1376.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
