import LeanLCAExactChallenge.Derived.EndpointTopologyFromClosednessBranch
import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableExactAtRoute

/-!
W873 composes the W856 endpoint-facts route with the W872 homology-free
selected-cochain stable-ExactAt route. This records the latest stable ExactAt
boundary at the endpoint-facts provider surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W873 direct bounded left calculus from endpoint facts plus W519 closedness. -/
theorem directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
    (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
      routeData)

/--
W873 bounded derived infinity-category package from endpoint facts plus W519
closedness, routed through W872 stable ExactAt evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
    (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
      routeData)

/-- W873 expands the endpoint-facts W856 provider into its eight concrete fields. -/
def endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873 :
    List String :=
  endpointFactsHomologyFreeRouteDataInputNamesW856

theorem endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873_count :
    endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873.length =
      8 :=
  endpointFactsHomologyFreeRouteDataInputNamesW856_count

/-- Current checked W873 state. -/
structure MetrizableEndpointFactsHomologyFreeSelectedCochainStableExactAtRouteStateW873 :
    Type where
  seed : String
  declarations : List String
  endpointReconstructionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointFactsHomologyFreeSelectedCochainStableExactAtRouteStateW873 :
    MetrizableEndpointFactsHomologyFreeSelectedCochainStableExactAtRouteStateW873
    where
  seed := "w873-endpoint-facts-homology-free-selected-cochain-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfEndpointFactsHomologyFree" ++
        "SelectedCochainStableExactAtW873",
      "boundedDerivedInfinityCategoryOfEndpointFactsHomologyFree" ++
        "SelectedCochainStableExactAtW873",
      "endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873",
      "endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873_count"]
  endpointReconstructionResult :=
    "proved: W856 reconstructs the W853 endpoint strict-topology field from\
      endpoint facts and W519 closedness"
  exactAtResult :=
    "proved: one W856 endpoint-facts provider supplies the stable ExactAt package"
  replacedInputs :=
    ["one opaque W853 homology-free selected-cochain route-data provider at the\
      W872 boundary"]
  remainingInputs :=
    endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873
  productSuccessClaimed := false

theorem currentW873EndpointFactsHomologyFreeSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointFactsHomologyFreeSelectedCochainStableExactAtRouteStateW873;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
