import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableExactAtRoute

/-!
W872 composes the W853 homology-free selected-cochain route with the W870
stable-ExactAt route. This records the stable ExactAt boundary at the
homology-free selected-cochain provider surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W872 direct bounded left calculus from the homology-free W853 provider. -/
theorem directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/--
W872 bounded derived infinity-category package from the homology-free W853
provider, routed through W870 stable ExactAt evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/-- W872 has one input: the W853 homology-free selected-cochain provider. -/
def homologyFreeSelectedCochainStableExactAtInputNamesW872 : List String :=
  homologyFreeSelectedCochainStableRouteInputNamesW853

theorem homologyFreeSelectedCochainStableExactAtInputNamesW872_count :
    homologyFreeSelectedCochainStableExactAtInputNamesW872.length =
      1 :=
  homologyFreeSelectedCochainStableRouteInputNamesW853_count

/-- Current checked W872 state. -/
structure MetrizableHomologyFreeSelectedCochainStableExactAtRouteStateW872 :
    Type where
  seed : String
  declarations : List String
  branchAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableHomologyFreeSelectedCochainStableExactAtRouteStateW872 :
    MetrizableHomologyFreeSelectedCochainStableExactAtRouteStateW872
    where
  seed := "w872-homology-free-selected-cochain-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfHomologyFreeComparison" ++
        "SelectedCochainStableExactAtW872",
      "boundedDerivedInfinityCategoryOfHomologyFreeComparison" ++
        "SelectedCochainStableExactAtW872",
      "homologyFreeSelectedCochainStableExactAtInputNamesW872",
      "homologyFreeSelectedCochainStableExactAtInputNamesW872_count"]
  branchAssemblyResult :=
    "proved: W853 rebuilds the W735 branch required by W870"
  exactAtResult :=
    "proved: one homology-free W853 provider supplies the stable ExactAt package"
  replacedInputs :=
    ["one W732 boundary/relation target/closedness normalized route-data\
      provider at the W871 boundary"]
  remainingInputs :=
    homologyFreeSelectedCochainStableExactAtInputNamesW872
  productSuccessClaimed := false

theorem currentW872HomologyFreeSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableHomologyFreeSelectedCochainStableExactAtRouteStateW872;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
