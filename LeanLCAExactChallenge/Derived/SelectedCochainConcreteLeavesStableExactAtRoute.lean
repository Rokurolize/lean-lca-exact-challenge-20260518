import LeanLCAExactChallenge.Derived.W733ConcreteLeavesSelectedCochainStableExactAtRoute
import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainStrictificationRoute
import LeanLCAExactChallenge.Derived.RouteDataProviderFromComparisonBijectivity

/-!
W878 feeds the W877 concrete-leaves selected-cochain stable-ExactAt route from
the W847 selected-cochain direct-source surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W878 closed-map W733 concrete leaves from W847 selected-cochain data. -/
def concreteLeavesOfClosedMapSelectedCochainDirectSourceW878
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  closedMapConcreteLeavesOfComparisonBijectivityW855
    data.exactInputs

/-- W878 closed-embedding W733 concrete leaves from W847 selected-cochain data. -/
def concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  closedEmbeddingConcreteLeavesOfComparisonBijectivityW855
    data.exactInputs

/--
W878 closed-map direct bounded left calculus through the W877 concrete-leaves
stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
    (concreteLeavesOfClosedMapSelectedCochainDirectSourceW878 data)

/--
W878 closed-embedding direct bounded left calculus through the W877
concrete-leaves stable ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
    (concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878 data)

/--
W878 closed-map bounded derived infinity-category package through the W877
concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
    (concreteLeavesOfClosedMapSelectedCochainDirectSourceW878 data)

/--
W878 closed-embedding bounded derived infinity-category package through the W877
concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
    (concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878 data)

/-- W878 has one bundled input: W847 selected-cochain direct-source data. -/
def selectedCochainConcreteLeavesStableExactAtInputNamesW878 :
    List String :=
  Dbounded.selectedCochainDirectSourceStableRouteInputNamesW847

theorem selectedCochainConcreteLeavesStableExactAtInputNamesW878_count :
    selectedCochainConcreteLeavesStableExactAtInputNamesW878.length =
      1 :=
  Dbounded.selectedCochainDirectSourceStableRouteInputNamesW847_count

/-- Expanded W878 requirements are exactly the two concrete W847 fields. -/
def selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878 :
    List String :=
  Dbounded.selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847

theorem selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878_count :
    selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878.length =
      2 :=
  Dbounded.selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847_count

/-- Current checked W878 state. -/
structure MetrizableSelectedCochainConcreteLeavesStableExactAtRouteStateW878 :
    Type where
  seed : String
  declarations : List String
  concreteLeavesResult : String
  stableExactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSelectedCochainConcreteLeavesStableExactAtRouteStateW878 :
    MetrizableSelectedCochainConcreteLeavesStableExactAtRouteStateW878
    where
  seed := "w878-selected-cochain-concrete-leaves-stable-exact-at-route"
  declarations :=
    ["concreteLeavesOfClosedMapSelectedCochainDirectSourceW878",
      "concreteLeavesOfClosedEmbeddingSelectedCochainDirectSourceW878",
      "directBoundedLeftCalculusOfClosedMapSelectedCochain" ++
        "ConcreteLeavesStableExactAtW878",
      "directBoundedLeftCalculusOfClosedEmbeddingSelectedCochain" ++
        "ConcreteLeavesStableExactAtW878",
      "boundedDerivedInfinityCategoryOfClosedMapSelectedCochain" ++
        "ConcreteLeavesStableExactAtW878",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochain" ++
        "ConcreteLeavesStableExactAtW878",
      "selectedCochainConcreteLeavesStableExactAtInputNamesW878",
      "selectedCochainConcreteLeavesStableExactAtInputNamesW878_count",
      "selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878",
      "selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878_count"]
  concreteLeavesResult :=
    "proved: W847 selected-cochain data supply W733 concrete leaves through W855"
  stableExactAtResult :=
    "proved: W847 selected-cochain data feed the W877 stable ExactAt route"
  replacedInputs :=
    concreteLeavesSelectedCochainStableExactAtInputNamesW877
  remainingInputs :=
    selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878
  productSuccessClaimed := false

theorem currentW878SelectedCochainConcreteLeavesStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableSelectedCochainConcreteLeavesStableExactAtRouteStateW878;
      state.productSuccessClaimed) =
        false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
