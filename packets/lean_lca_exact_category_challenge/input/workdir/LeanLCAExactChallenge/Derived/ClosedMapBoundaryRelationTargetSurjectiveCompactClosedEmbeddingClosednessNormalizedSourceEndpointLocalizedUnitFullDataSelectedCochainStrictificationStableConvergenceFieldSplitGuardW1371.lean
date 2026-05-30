import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetExactAtDirectSourceStableConvergenceFieldSplitGuardW1370
import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainDirectSourceStableExactAtRoute

/-!
W1371 records the definitional convergence from W847 selected-cochain
strictification data into the W867/W868 stable ExactAt route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W847 closed-map conversion preserves the exact-input branch. -/
theorem w847ClosedMapStrictRealizationExactInputsFieldW1371
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (closedMapStrictRealizationDataOfSelectedCochainW847 data).exactInputs =
      data.exactInputs :=
  rfl

/-- W847 closed-embedding conversion preserves the exact-input branch. -/
theorem w847ClosedEmbeddingStrictRealizationExactInputsFieldW1371
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data).exactInputs =
      data.exactInputs :=
  rfl

/-- W868 closed-map direct calculus is W847-to-W846 followed by W867. -/
theorem w868ClosedMapDirectCalculusRunsThroughW847W846W867W1371
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        data =
      directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfSelectedCochainW847 data) :=
  rfl

/-- W868 closed-embedding direct calculus is W847-to-W846 followed by W867. -/
theorem w868ClosedEmbeddingDirectCalculusRunsThroughW847W846W867W1371
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        data =
      directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data) :=
  rfl

/-- W868 closed-map stable package is W847-to-W846 followed by W867. -/
theorem w868ClosedMapStablePackageRunsThroughW847W846W867W1371
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        data =
      boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfSelectedCochainW847 data) :=
  rfl

/-- W868 closed-embedding stable package is W847-to-W846 followed by W867. -/
theorem w868ClosedEmbeddingStablePackageRunsThroughW847W846W867W1371
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        data =
      boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data) :=
  rfl

/-- W1371 keeps the W868 bundled input count visible. -/
theorem w1371SelectedCochainDirectSourceStableExactAtInputCountMatchesW868 :
    selectedCochainDirectSourceStableExactAtInputNamesW868.length = 1 :=
  selectedCochainDirectSourceStableExactAtInputNamesW868_count

/-- W1371 keeps the expanded W868 field count visible. -/
theorem w1371SelectedCochainDirectSourceStableExactAtExpandedCountMatchesW868 :
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868.length = 2 :=
  selectedCochainDirectSourceStableExactAtExpandedInputNamesW868_count

/-- Current W1371 nonterminal state. -/
structure SelectedCochainStrictificationStableConvergenceStateW1371 :
    Type where
  seed : String
  declarations : List String
  selectedCochainConversionResult : String
  stableExactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1371 records W847 selected-cochain convergence into the W868 route. -/
def currentSelectedCochainStrictificationStableConvergenceStateW1371 :
    SelectedCochainStrictificationStableConvergenceStateW1371 where
  seed := "w1371-selected-cochain-strictification-stable-convergence"
  declarations :=
    ["w847ClosedMapStrictRealizationExactInputsFieldW1371",
      "w847ClosedEmbeddingStrictRealizationExactInputsFieldW1371",
      "w868ClosedMapDirectCalculusRunsThroughW847W846W867W1371",
      "w868ClosedEmbeddingDirectCalculusRunsThroughW847W846W867W1371",
      "w868ClosedMapStablePackageRunsThroughW847W846W867W1371",
      "w868ClosedEmbeddingStablePackageRunsThroughW847W846W867W1371",
      "w1371SelectedCochainDirectSourceStableExactAtInputCountMatchesW868",
      "w1371SelectedCochainDirectSourceStableExactAtExpandedCountMatchesW868"]
  selectedCochainConversionResult :=
    "proved: W847 selected-cochain strictification data feed W846 \
      strict-realization data while preserving exact-input branches"
  stableExactAtResult :=
    "proved: W868 direct calculus and stable package route through W847-to-W846 \
      conversion and W867"
  remainingInputs :=
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868
  productSuccessClaimed := false

theorem currentW1371SelectedCochainStrictificationStableConvergence_productSuccess :
    currentSelectedCochainStrictificationStableConvergenceStateW1371.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
