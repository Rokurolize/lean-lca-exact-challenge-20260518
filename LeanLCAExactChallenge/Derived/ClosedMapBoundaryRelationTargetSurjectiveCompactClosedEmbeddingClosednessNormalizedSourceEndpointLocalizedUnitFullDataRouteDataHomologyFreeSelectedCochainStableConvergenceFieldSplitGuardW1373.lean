import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataExactInputsComparisonSelectedCochainStableConvergenceFieldSplitGuardW1372
import LeanLCAExactChallenge.Derived.RouteDataSelectedCochainStableExactAtRoute
import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableExactAtRoute

/-!
W1373 records the definitional convergence from W732 route data and W853
homology-free selected-cochain data into the W870 stable ExactAt branch route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W871 direct calculus is W763 leaves followed by W870 branch dispatch. -/
theorem w871DirectCalculusRunsThroughLeavesAndW870W1373
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    directBoundedLeftCalculusOfRouteDataComparisonSelectedCochainStableExactAtW871
        routeData =
      (let leaves :=
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
              mappedCokernelClosedEmbeddingProvider)) :=
  rfl

/-- W871 stable package is W763 leaves followed by W870 branch dispatch. -/
theorem w871StablePackageRunsThroughLeavesAndW870W1373
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    boundedDerivedInfinityCategoryOfRouteDataComparisonSelectedCochainStableExactAtW871
        routeData =
      (let leaves :=
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
              mappedCokernelClosedEmbeddingProvider)) :=
  rfl

/-- W872 direct calculus is W853 closedness-branch dispatch into W870. -/
theorem w872DirectCalculusRunsThroughW853BranchAndW870W1373
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        routeData =
      (match routeData.diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
            (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedEmbeddingComponents
              mappedCokernelClosedEmbeddingProvider)) :=
  rfl

/-- W872 stable package is W853 closedness-branch dispatch into W870. -/
theorem w872StablePackageRunsThroughW853BranchAndW870W1373
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        routeData =
      (match routeData.diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
            (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedEmbeddingComponents
              mappedCokernelClosedEmbeddingProvider)) :=
  rfl

/-- W1373 keeps the W871 route-data input count visible. -/
theorem w1373RouteDataSelectedCochainStableExactAtInputCountMatchesW871 :
    routeDataSelectedCochainStableExactAtInputNamesW871.length = 1 :=
  routeDataSelectedCochainStableExactAtInputNamesW871_count

/-- W1373 keeps the W872 homology-free input count visible. -/
theorem w1373HomologyFreeSelectedCochainStableExactAtInputCountMatchesW872 :
    homologyFreeSelectedCochainStableExactAtInputNamesW872.length = 1 :=
  homologyFreeSelectedCochainStableExactAtInputNamesW872_count

/-- Current W1373 nonterminal state. -/
structure RouteDataHomologyFreeSelectedCochainStableConvergenceStateW1373 :
    Type where
  seed : String
  declarations : List String
  routeDataResult : String
  homologyFreeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1373 records W732/W853 convergence into W870 stable ExactAt evidence. -/
def currentRouteDataHomologyFreeSelectedCochainStableConvergenceStateW1373 :
    RouteDataHomologyFreeSelectedCochainStableConvergenceStateW1373 where
  seed := "w1373-route-data-homology-free-selected-cochain-stable-convergence"
  declarations :=
    ["w871DirectCalculusRunsThroughLeavesAndW870W1373",
      "w871StablePackageRunsThroughLeavesAndW870W1373",
      "w872DirectCalculusRunsThroughW853BranchAndW870W1373",
      "w872StablePackageRunsThroughW853BranchAndW870W1373",
      "w1373RouteDataSelectedCochainStableExactAtInputCountMatchesW871",
      "w1373HomologyFreeSelectedCochainStableExactAtInputCountMatchesW872"]
  routeDataResult :=
    "proved: W871 route-data direct calculus and stable package route through \
      W763 concrete leaves and W870 branch dispatch"
  homologyFreeResult :=
    "proved: W872 homology-free selected-cochain direct calculus and stable \
      package route through W853 branch dispatch and W870"
  remainingInputs :=
    homologyFreeSelectedCochainStableExactAtInputNamesW872
  productSuccessClaimed := false

theorem currentW1373RouteDataHomologyFreeSelectedCochainStableConvergence_productSuccess :
    currentRouteDataHomologyFreeSelectedCochainStableConvergenceStateW1373.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
