import LeanLCAExactChallenge.Derived.EndpointLocalizedComparisonConcreteLeavesStableExactAtRoute
import LeanLCAExactChallenge.Derived.W732SelectedCochainStableExactAtRoute

/-!
W882 feeds the W881 endpoint/localized comparison concrete-leaves stable-ExactAt
route from the one-provider W732 route-data surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W882 restores the W874 provider from one W732 route-data provider. -/
def endpointLocalizedRouteDataProviderOfW732ForW882
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874 :=
  routeDataProviderOfW732W875 routeData

/--
W882 direct bounded left calculus from one W732 route-data provider through the
latest W881 comparison concrete-leaves stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
    (endpointLocalizedRouteDataProviderOfW732ForW882 routeData)

/--
W882 bounded derived infinity-category package from one W732 route-data provider
through the latest W881 comparison concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
    (endpointLocalizedRouteDataProviderOfW732ForW882 routeData)

/-- W882 has one bundled input: the W732 route-data provider. -/
def w732ComparisonConcreteLeavesStableExactAtInputNamesW882 :
    List String :=
  w732SelectedCochainStableExactAtInputNamesW875

theorem w732ComparisonConcreteLeavesStableExactAtInputNamesW882_count :
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882.length =
      1 :=
  w732SelectedCochainStableExactAtInputNamesW875_count

/-- The W882 expanded boundary is still the one W732 route-data provider. -/
def w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882 :
    List String :=
  w732SelectedCochainStableExactAtInputNamesW875

theorem w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882_count :
    w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882.length =
      1 :=
  w732SelectedCochainStableExactAtInputNamesW875_count

/-- Current checked W882 state. -/
structure MetrizableW732ComparisonConcreteLeavesStableExactAtRouteStateW882 :
    Type where
  seed : String
  declarations : List String
  w732ProjectionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  expandedRemainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableW732ComparisonConcreteLeavesStableExactAtRouteStateW882 :
    MetrizableW732ComparisonConcreteLeavesStableExactAtRouteStateW882
    where
  seed := "w882-w732-comparison-concrete-leaves-stable-exact-at"
  declarations :=
    ["endpointLocalizedRouteDataProviderOfW732ForW882",
      "directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882",
      "boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882",
      "w732ComparisonConcreteLeavesStableExactAtInputNamesW882",
      "w732ComparisonConcreteLeavesStableExactAtInputNamesW882_count",
      "w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882",
      "w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882_count"]
  w732ProjectionResult :=
    "proved: W875 restores the W874 endpoint/localized provider from W732 route data"
  exactAtResult :=
    "proved: one W732 route-data provider supplies the W881 stable ExactAt package"
  replacedInputs :=
    endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881
  remainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882
  expandedRemainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882
  productSuccessClaimed := false

theorem currentW882W732ComparisonConcreteLeavesStableExactAtRoute_productSuccess :
    currentMetrizableW732ComparisonConcreteLeavesStableExactAtRouteStateW882.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
