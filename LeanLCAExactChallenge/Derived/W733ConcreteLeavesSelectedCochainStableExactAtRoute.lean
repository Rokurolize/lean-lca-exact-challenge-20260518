import LeanLCAExactChallenge.Derived.W732SelectedCochainStableExactAtRoute

/-!
W877 feeds the W875 W732 selected-cochain stable-ExactAt route from W733
concrete leaves by using the existing W733-to-W732 route-data constructor.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W877 W732 route data assembled from W733 concrete leaves. -/
def routeDataProviderOfConcreteLeavesW877
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  boundaryRelationTargetClosednessNormalizedDataProvider_of_concreteLeavesW733
    leaves

/--
W877 direct bounded left calculus from W733 concrete leaves through the W875
stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfConcreteLeavesW877 leaves)

/--
W877 bounded derived infinity-category package from W733 concrete leaves
through W875 stable ExactAt evidence.
-/
noncomputable def boundedDerivedInfinityCategoryOfConcreteLeavesSelectedCochainStableExactAtW877
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfConcreteLeavesW877 leaves)

/-- W877 exposes the eight W733 concrete leaf providers. -/
def concreteLeavesSelectedCochainStableExactAtInputNamesW877 : List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "source homological-triangulation data provider",
    "endpoint strict-topology data provider",
    "bounded homotopy localized-right-adjoint data provider"]

theorem concreteLeavesSelectedCochainStableExactAtInputNamesW877_count :
    concreteLeavesSelectedCochainStableExactAtInputNamesW877.length = 8 :=
  rfl

/-- Current checked W877 state. -/
structure MetrizableConcreteLeavesSelectedCochainStableExactAtRouteStateW877 :
    Type where
  seed : String
  declarations : List String
  routeDataConstructionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableConcreteLeavesSelectedCochainStableExactAtRouteStateW877 :
    MetrizableConcreteLeavesSelectedCochainStableExactAtRouteStateW877
    where
  seed := "w877-w733-concrete-leaves-selected-cochain-stable-exact-at-route"
  declarations :=
    ["routeDataProviderOfConcreteLeavesW877",
      "directBoundedLeftCalculusOfConcreteLeavesSelectedCochainStableExactAtW877",
      "boundedDerivedInfinityCategoryOfConcreteLeaves" ++
        "SelectedCochainStableExactAtW877",
      "concreteLeavesSelectedCochainStableExactAtInputNamesW877",
      "concreteLeavesSelectedCochainStableExactAtInputNamesW877_count"]
  routeDataConstructionResult :=
    "proved: W733 concrete leaves construct the W732 route-data provider"
  exactAtResult :=
    "proved: W733 concrete leaves feed the W875 stable ExactAt route"
  replacedInputs :=
    w732SelectedCochainStableExactAtInputNamesW875
  remainingInputs :=
    concreteLeavesSelectedCochainStableExactAtInputNamesW877
  productSuccessClaimed := false

theorem currentW877ConcreteLeavesSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableConcreteLeavesSelectedCochainStableExactAtRouteStateW877;
      state.productSuccessClaimed) =
        false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
