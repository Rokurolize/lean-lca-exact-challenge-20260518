import LeanLCAExactChallenge.Derived.EndpointFactsHomologyFreeSelectedCochainStableExactAtRoute

/-!
W874 composes W726 endpoint/localized data with the W873 endpoint-facts
selected-cochain stable-ExactAt route. This replaces the separate W856 endpoint
topology facts plus localized-right-adjoint fields by one W726 provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W874 derives W856 endpoint topology facts from W726 endpoint/localized data. -/
def endpointTopologyFactsOfEndpointLocalizedW874
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    MetrizableWppEndpointTopologyFactsProviderW856
    where
  endpointClosedEmbedding := by
    intro K i
    exact
      endpointClosedEmbedding_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i
  endpointOpenMap := by
    intro K i
    exact
      endpointOpenMap_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i
  endpointEpiOfExactAt := by
    intro K i hExact
    exact
      endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i hExact

/--
W874 provider surface after combining W856 endpoint topology facts and
localized-right-adjoint data into one W726 provider.
-/
structure MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointLocalizedRightAdjointData :
    MetrizableWppEndpointLocalizedRightAdjointDataProviderW726

/-- W874 restores the W873 provider by projecting W726 endpoint/localized data. -/
def endpointFactsRouteDataProviderOfEndpointLocalizedW874
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856
    where
  boundaryData := routeData.boundaryData
  relationData := routeData.relationData
  targetSurjectiveCompactForTargetProvider :=
    routeData.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    routeData.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := routeData.normalizedFixedTargetData
  sourceTriangulationData := routeData.sourceTriangulationData
  endpointTopologyFacts :=
    endpointTopologyFactsOfEndpointLocalizedW874
      routeData.endpointLocalizedRightAdjointData
  localizedRightAdjointData :=
    localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
      routeData.endpointLocalizedRightAdjointData

/-- W874 direct bounded left calculus from endpoint/localized route data. -/
theorem directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData)

/--
W874 bounded derived infinity-category package from endpoint/localized route
data, routed through W873 stable ExactAt evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
    (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData)

/-- W874 expands the endpoint/localized provider into its seven concrete fields. -/
def endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation ordinary relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "W726 endpoint/localized-right-adjoint data provider"]

theorem endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874_count :
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874.length =
      7 :=
  rfl

/-- Current checked W874 state. -/
structure MetrizableEndpointLocalizedHomologyFreeSelectedCochainStableExactAtRouteStateW874 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedProjectionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedHomologyFreeSelectedCochainStableExactAtRouteStateW874 :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainStableExactAtRouteStateW874
    where
  seed := "w874-endpoint-localized-homology-free-selected-cochain-exact-at-route"
  declarations :=
    ["endpointTopologyFactsOfEndpointLocalizedW874",
      "MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874",
      "endpointFactsRouteDataProviderOfEndpointLocalizedW874",
      "directBoundedLeftCalculusOfEndpointLocalizedHomologyFree" ++
        "SelectedCochainStableExactAtW874",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFree" ++
        "SelectedCochainStableExactAtW874",
      "endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874",
      "endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874_count"]
  endpointLocalizedProjectionResult :=
    "proved: W726 endpoint/localized data supplies W856 endpoint facts and W721\
      localized-right-adjoint data"
  exactAtResult :=
    "proved: one W874 endpoint/localized provider supplies the stable ExactAt package"
  replacedInputs :=
    ["separate W856 endpoint topology facts provider",
      "separate W721 localized-right-adjoint data provider"]
  remainingInputs :=
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874
  productSuccessClaimed := false

theorem currentW874EndpointLocalizedHomologyFreeSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedHomologyFreeSelectedCochainStableExactAtRouteStateW874;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
