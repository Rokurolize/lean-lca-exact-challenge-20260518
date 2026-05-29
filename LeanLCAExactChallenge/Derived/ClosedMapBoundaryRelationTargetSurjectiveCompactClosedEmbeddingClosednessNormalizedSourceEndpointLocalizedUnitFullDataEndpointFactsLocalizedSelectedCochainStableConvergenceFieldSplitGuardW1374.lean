import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRouteDataHomologyFreeSelectedCochainStableConvergenceFieldSplitGuardW1373
import LeanLCAExactChallenge.Derived.EndpointLocalizedHomologyFreeSelectedCochainStableExactAtRoute

/-!
W1374 records the definitional convergence from W856 endpoint-facts data and
W726 endpoint/localized data into the W873/W874 selected-cochain stable ExactAt
route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W873 direct calculus is W856-to-W853 followed by W872. -/
theorem w873DirectCalculusRunsThroughW856W872W1374
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        routeData =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
          routeData) :=
  rfl

/-- W873 stable package is W856-to-W853 followed by W872. -/
theorem w873StablePackageRunsThroughW856W872W1374
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        routeData =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
          routeData) :=
  rfl

/-- W874 closed-embedding endpoint facts are projected from W726's W720 data. -/
theorem w874EndpointClosedEmbeddingFieldUsesW726W1374
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointTopologyFactsOfEndpointLocalizedW874
        endpointLocalizedData).endpointClosedEmbedding =
      fun K i =>
        endpointClosedEmbedding_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i :=
  rfl

/-- W874 open-map endpoint facts are projected from W726's W720 data. -/
theorem w874EndpointOpenMapFieldUsesW726W1374
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointTopologyFactsOfEndpointLocalizedW874
        endpointLocalizedData).endpointOpenMap =
      fun K i =>
        endpointOpenMap_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i :=
  rfl

/-- W874 ExactAt-to-epi endpoint facts are projected from W726's W720 data. -/
theorem w874EndpointEpiFieldUsesW726W1374
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointTopologyFactsOfEndpointLocalizedW874
        endpointLocalizedData).endpointEpiOfExactAt =
      fun K i hExact =>
        endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i hExact :=
  rfl

/-- W874 preserves boundary data when rebuilding the W856 provider. -/
theorem w874EndpointFactsProviderBoundaryFieldW1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData).boundaryData =
      routeData.boundaryData :=
  rfl

/-- W874 preserves closedness branch data when rebuilding the W856 provider. -/
theorem w874EndpointFactsProviderClosednessFieldW1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874
        routeData).diagramAndMappedCokernelClosednessData =
      routeData.diagramAndMappedCokernelClosednessData :=
  rfl

/-- W874 supplies W856 endpoint facts from the W726 endpoint/localized field. -/
theorem w874EndpointFactsProviderEndpointFactsFieldW1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874
        routeData).endpointTopologyFacts =
      endpointTopologyFactsOfEndpointLocalizedW874
        routeData.endpointLocalizedRightAdjointData :=
  rfl

/-- W874 supplies localized-right-adjoint data from the W726 endpoint/localized field. -/
theorem w874EndpointFactsProviderLocalizedFieldW1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874
        routeData).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        routeData.endpointLocalizedRightAdjointData :=
  rfl

/-- W874 direct calculus is W874 provider projection followed by W873. -/
theorem w874DirectCalculusRunsThroughW873W1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        routeData =
      directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData) :=
  rfl

/-- W874 stable package is W874 provider projection followed by W873. -/
theorem w874StablePackageRunsThroughW873W1374
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        routeData =
      boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData) :=
  rfl

/-- W1374 keeps the W873 endpoint-facts input count visible. -/
theorem w1374EndpointFactsHomologyFreeSelectedCochainInputCountMatchesW873 :
    endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873.length =
      8 :=
  endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873_count

/-- W1374 keeps the W874 endpoint-localized input count visible. -/
theorem w1374EndpointLocalizedHomologyFreeSelectedCochainInputCountMatchesW874 :
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874.length =
      7 :=
  endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874_count

/-- Current W1374 nonterminal state. -/
structure EndpointFactsLocalizedSelectedCochainStableConvergenceStateW1374 :
    Type where
  seed : String
  declarations : List String
  endpointFactsResult : String
  endpointLocalizedResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1374 records W856/W726 convergence into W873/W874 stable ExactAt evidence. -/
def currentEndpointFactsLocalizedSelectedCochainStableConvergenceStateW1374 :
    EndpointFactsLocalizedSelectedCochainStableConvergenceStateW1374 where
  seed := "w1374-endpoint-facts-localized-selected-cochain-stable-convergence"
  declarations :=
    ["w873DirectCalculusRunsThroughW856W872W1374",
      "w873StablePackageRunsThroughW856W872W1374",
      "w874EndpointClosedEmbeddingFieldUsesW726W1374",
      "w874EndpointOpenMapFieldUsesW726W1374",
      "w874EndpointEpiFieldUsesW726W1374",
      "w874EndpointFactsProviderBoundaryFieldW1374",
      "w874EndpointFactsProviderClosednessFieldW1374",
      "w874EndpointFactsProviderEndpointFactsFieldW1374",
      "w874EndpointFactsProviderLocalizedFieldW1374",
      "w874DirectCalculusRunsThroughW873W1374",
      "w874StablePackageRunsThroughW873W1374",
      "w1374EndpointFactsHomologyFreeSelectedCochainInputCountMatchesW873",
      "w1374EndpointLocalizedHomologyFreeSelectedCochainInputCountMatchesW874"]
  endpointFactsResult :=
    "proved: W873 direct calculus and stable package route through W856-to-W853 \
      reconstruction and W872"
  endpointLocalizedResult :=
    "proved: W874 endpoint/localized provider projects W726 data into W856 and \
      delegates direct calculus and stable package construction to W873"
  remainingInputs :=
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874
  productSuccessClaimed := false

theorem currentW1374EndpointFactsLocalizedSelectedCochainStableConvergence_productSuccess :
    currentEndpointFactsLocalizedSelectedCochainStableConvergenceStateW1374.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
