import LeanLCAExactChallenge.Derived.W732ComparisonConcreteLeavesStableExactAtRoute
import LeanLCAExactChallenge.Derived.W733ConcreteLeavesSelectedCochainStableExactAtRoute

/-!
W883 feeds the W882 W732 comparison concrete-leaves stable-ExactAt route from
W733 concrete leaves.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W883 W732 route data assembled from W733 concrete leaves. -/
def routeDataProviderOfConcreteLeavesForW883
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfConcreteLeavesW877 leaves

/--
W883 direct bounded left calculus from W733 concrete leaves through the latest
W882 comparison concrete-leaves stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
    (routeDataProviderOfConcreteLeavesForW883 leaves)

/--
W883 bounded derived infinity-category package from W733 concrete leaves through
the latest W882 comparison concrete-leaves stable ExactAt route.
-/
noncomputable def boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
    (routeDataProviderOfConcreteLeavesForW883 leaves)

/-- W883 exposes the eight W733 concrete leaf providers. -/
def concreteLeavesComparisonStableExactAtInputNamesW883 : List String :=
  concreteLeavesSelectedCochainStableExactAtInputNamesW877

theorem concreteLeavesComparisonStableExactAtInputNamesW883_count :
    concreteLeavesComparisonStableExactAtInputNamesW883.length =
      8 :=
  concreteLeavesSelectedCochainStableExactAtInputNamesW877_count

/-- Current checked W883 state. -/
structure MetrizableConcreteLeavesComparisonStableExactAtRouteStateW883 :
    Type where
  seed : String
  declarations : List String
  routeDataConstructionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableConcreteLeavesComparisonStableExactAtRouteStateW883 :
    MetrizableConcreteLeavesComparisonStableExactAtRouteStateW883
    where
  seed := "w883-w733-concrete-leaves-comparison-stable-exact-at"
  declarations :=
    ["routeDataProviderOfConcreteLeavesForW883",
      "directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883",
      "boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883",
      "concreteLeavesComparisonStableExactAtInputNamesW883",
      "concreteLeavesComparisonStableExactAtInputNamesW883_count"]
  routeDataConstructionResult :=
    "proved: W733 concrete leaves construct the W732 provider consumed by W882"
  exactAtResult :=
    "proved: W733 concrete leaves feed the W882 stable ExactAt route"
  replacedInputs :=
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882
  remainingInputs :=
    concreteLeavesComparisonStableExactAtInputNamesW883
  productSuccessClaimed := false

theorem currentW883ConcreteLeavesComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableConcreteLeavesComparisonStableExactAtRouteStateW883;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
