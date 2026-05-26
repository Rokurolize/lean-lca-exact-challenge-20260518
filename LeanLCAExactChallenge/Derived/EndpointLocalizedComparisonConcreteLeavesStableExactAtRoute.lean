import LeanLCAExactChallenge.Derived.EndpointLocalizedHomologyFreeSelectedCochainStableExactAtRoute
import LeanLCAExactChallenge.Derived.HomologyFreeComparisonConcreteLeavesStableExactAtRoute

/-!
W881 feeds the W880 homology-free comparison concrete-leaves stable-ExactAt
route from the W874 endpoint/localized provider surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W881 restores the W853 provider from the W874 endpoint/localized surface. -/
def homologyFreeRouteDataProviderOfEndpointLocalizedW881
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData)

/--
W881 direct bounded left calculus from W874 endpoint/localized data through the
W880 comparison concrete-leaves stable ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
    (homologyFreeRouteDataProviderOfEndpointLocalizedW881 routeData)

/--
W881 bounded derived infinity-category package from W874 endpoint/localized data
through the W880 comparison concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
    (homologyFreeRouteDataProviderOfEndpointLocalizedW881 routeData)

/-- W881 has one bundled input: the W874 endpoint/localized provider. -/
def endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881 :
    List String :=
  ["one W874 endpoint/localized homology-free selected-cochain provider"]

theorem endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881_count :
    endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881.length =
      1 :=
  rfl

/-- Expanded W881 requirements are the seven fields of the W874 provider. -/
def endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881 :
    List String :=
  endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874

theorem
    endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881_count :
    endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881.length =
      7 :=
  endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874_count

/-- Current checked W881 state. -/
structure MetrizableEndpointLocalizedComparisonConcreteLeavesStableExactAtRouteStateW881 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedProjectionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  expandedRemainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedComparisonConcreteLeavesStableExactAtRouteStateW881 :
    MetrizableEndpointLocalizedComparisonConcreteLeavesStableExactAtRouteStateW881
    where
  seed := "w881-endpoint-localized-comparison-concrete-leaves-stable-exact-at"
  declarations :=
    ["homologyFreeRouteDataProviderOfEndpointLocalizedW881",
      "directBoundedLeftCalculusOfEndpointLocalizedComparison" ++
        "ConcreteLeavesStableExactAtW881",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedComparison" ++
        "ConcreteLeavesStableExactAtW881",
      "endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881",
      "endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881_count",
      "endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881",
      "endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881_count"]
  endpointLocalizedProjectionResult :=
    "proved: W874 endpoint/localized data restores the W853 provider consumed by W880"
  exactAtResult :=
    "proved: one W874 endpoint/localized provider supplies the W880 stable ExactAt package"
  replacedInputs :=
    homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880
  remainingInputs :=
    endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881
  expandedRemainingInputs :=
    endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881
  productSuccessClaimed := false

theorem currentW881EndpointLocalizedComparisonConcreteLeavesStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedComparisonConcreteLeavesStableExactAtRouteStateW881;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
