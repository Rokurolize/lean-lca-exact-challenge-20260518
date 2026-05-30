import LeanLCAExactChallenge.Derived.RouteDataSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableExactAtRoute

/-!
W871 composes the W852 route-data selected-cochain route with the W870
stable-ExactAt route. This moves the latest stable ExactAt boundary from one
W735 exact-input branch to one W732 route-data provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W871 direct bounded left calculus from one W732 route-data provider. -/
theorem directBoundedLeftCalculusOfRouteDataComparisonSelectedCochainStableExactAtW871
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  let leaves :=
    boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData
  match leaves.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfRouteDataLeavesW852 leaves
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfRouteDataLeavesW852 leaves
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/--
W871 bounded derived infinity-category package from one W732 route-data
provider, routed through the stable ExactAt bridge.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfRouteDataComparisonSelectedCochainStableExactAtW871
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  let leaves :=
    boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData
  match leaves.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfRouteDataLeavesW852 leaves
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfRouteDataLeavesW852 leaves
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/-- W871 has one input: the W732 route-data provider. -/
def routeDataSelectedCochainStableExactAtInputNamesW871 : List String :=
  routeDataSelectedCochainStableRouteInputNamesW852

theorem routeDataSelectedCochainStableExactAtInputNamesW871_count :
    routeDataSelectedCochainStableExactAtInputNamesW871.length =
      1 :=
  routeDataSelectedCochainStableRouteInputNamesW852_count

/-- Current checked W871 state. -/
structure MetrizableRouteDataSelectedCochainStableExactAtRouteStateW871 :
    Type where
  seed : String
  declarations : List String
  leafProjectionResult : String
  branchAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableRouteDataSelectedCochainStableExactAtRouteStateW871 :
    MetrizableRouteDataSelectedCochainStableExactAtRouteStateW871
    where
  seed := "w871-route-data-selected-cochain-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfRouteDataComparison" ++
        "SelectedCochainStableExactAtW871",
      "boundedDerivedInfinityCategoryOfRouteDataComparison" ++
        "SelectedCochainStableExactAtW871",
      "routeDataSelectedCochainStableExactAtInputNamesW871",
      "routeDataSelectedCochainStableExactAtInputNamesW871_count"]
  leafProjectionResult :=
    "proved: W763 projects one W732 route-data provider to W733 concrete leaves"
  branchAssemblyResult :=
    "proved: W852 rebuilds the W735 branch required by W870"
  exactAtResult :=
    "proved: one W732 route-data provider supplies the stable ExactAt package"
  replacedInputs :=
    ["one W735 closed-map or closed-embedding exact-input branch at the W870 \
      boundary"]
  remainingInputs :=
    routeDataSelectedCochainStableExactAtInputNamesW871
  productSuccessClaimed := false

theorem currentW871RouteDataSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableRouteDataSelectedCochainStableExactAtRouteStateW871;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
