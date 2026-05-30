import LeanLCAExactChallenge.Derived.EndpointLocalizedHomologyFreeSelectedCochainStableExactAtRoute

/-!
W875 feeds the W874 endpoint-localized selected-cochain stable-ExactAt route
from the one-provider W732 boundary/relation target/closedness normalized route
data surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W875 projects the boundary/relation provider bundled in W732. -/
def boundaryRelationDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  boundaryRelationData_of_boundaryRelationTargetClosednessNormalizedDataW732
    routeData

/-- W875 projects the target/normalized provider bundled in W732. -/
def targetNormalizedDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppTargetClosednessNormalizedSourceEndpointDataProviderW731 :=
  targetClosednessNormalizedSourceEndpointData_of_boundaryRelationTargetClosednessNormalizedDataW732
    routeData

/-- W875 projects target closedness data from W732. -/
def targetClosednessDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppTargetSurjectiveCompactClosednessDataProviderW729 :=
  targetClosednessData_of_targetClosednessNormalizedSourceEndpointDataW731
    (targetNormalizedDataOfW732ForW875 routeData)

/-- W875 projects normalized source/endpoint data from W732. -/
def normalizedSourceEndpointDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppNormalizedFixedTargetSourceEndpointDataProviderW728 :=
  normalizedFixedTargetSourceEndpointData_of_targetClosednessNormalizedSourceEndpointDataW731
    (targetNormalizedDataOfW732ForW875 routeData)

/-- W875 projects source/endpoint data from W732. -/
def sourceEndpointDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppSourceHomologicalEndpointLocalizedDataProviderW727 :=
  sourceHomologicalEndpointLocalizedData_of_normalizedSourceEndpointDataW728
    (normalizedSourceEndpointDataOfW732ForW875 routeData)

/-- W875 derives the W722 source triangulation provider from W732. -/
def sourceTriangulationDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppSourceTriangulationDataProviderW722 :=
  sourceTriangulationData_of_sourceHomologicalTriangulationDataW724
    (sourceHomologicalTriangulationData_of_sourceHomologicalEndpointLocalizedDataW727
      (sourceEndpointDataOfW732ForW875 routeData))

/-- W875 derives the W726 endpoint/localized provider from W732. -/
def endpointLocalizedDataOfW732ForW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppEndpointLocalizedRightAdjointDataProviderW726 :=
  endpointLocalizedRightAdjointData_of_sourceHomologicalEndpointLocalizedDataW727
    (sourceEndpointDataOfW732ForW875 routeData)

/-- W875 restores the W874 provider from the one-provider W732 surface. -/
def routeDataProviderOfW732W875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874
    where
  boundaryData :=
    boundaryData_of_boundaryRelationDataW730
      (boundaryRelationDataOfW732ForW875 routeData)
  relationData :=
    relationData_of_boundaryRelationDataW730
      (boundaryRelationDataOfW732ForW875 routeData)
  targetSurjectiveCompactForTargetProvider :=
    targetSurjectiveCompactForTargetProvider_of_targetClosednessDataW729
      (targetClosednessDataOfW732ForW875 routeData)
  diagramAndMappedCokernelClosednessData :=
    diagramAndMappedCokernelClosednessData_of_targetClosednessDataW729
      (targetClosednessDataOfW732ForW875 routeData)
  normalizedFixedTargetData :=
    normalizedFixedTargetData_of_normalizedSourceEndpointDataW728
      (normalizedSourceEndpointDataOfW732ForW875 routeData)
  sourceTriangulationData :=
    sourceTriangulationDataOfW732ForW875 routeData
  endpointLocalizedRightAdjointData :=
    endpointLocalizedDataOfW732ForW875 routeData

/-- W875 direct bounded left calculus from one W732 route-data provider. -/
theorem directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
    (routeDataProviderOfW732W875 routeData)

/--
W875 bounded derived infinity-category package from one W732 route-data
provider, routed through W874 stable ExactAt evidence.
-/
noncomputable def boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
    (routeDataProviderOfW732W875 routeData)

/-- W875 reduces the stable ExactAt route to the one-provider W732 surface. -/
def w732SelectedCochainStableExactAtInputNamesW875 : List String :=
  ["W732 boundary/relation target/closedness normalized source/endpoint \
    route-data provider"]

theorem w732SelectedCochainStableExactAtInputNamesW875_count :
    w732SelectedCochainStableExactAtInputNamesW875.length = 1 :=
  rfl

/-- Current checked W875 state. -/
structure MetrizableW732SelectedCochainStableExactAtRouteStateW875 :
    Type where
  seed : String
  declarations : List String
  w732ProjectionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableW732SelectedCochainStableExactAtRouteStateW875 :
    MetrizableW732SelectedCochainStableExactAtRouteStateW875
    where
  seed := "w875-w732-selected-cochain-stable-exact-at-route"
  declarations :=
    ["boundaryRelationDataOfW732ForW875",
      "targetNormalizedDataOfW732ForW875",
      "targetClosednessDataOfW732ForW875",
      "normalizedSourceEndpointDataOfW732ForW875",
      "sourceEndpointDataOfW732ForW875",
      "sourceTriangulationDataOfW732ForW875",
      "endpointLocalizedDataOfW732ForW875",
      "routeDataProviderOfW732W875",
      "directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875",
      "boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875",
      "w732SelectedCochainStableExactAtInputNamesW875",
      "w732SelectedCochainStableExactAtInputNamesW875_count"]
  w732ProjectionResult :=
    "proved: W732 projects to the seven W874 endpoint-localized route fields"
  exactAtResult :=
    "proved: one W732 route-data provider supplies the stable ExactAt package"
  replacedInputs :=
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874
  remainingInputs := w732SelectedCochainStableExactAtInputNamesW875
  productSuccessClaimed := false

theorem currentW875W732SelectedCochainStableExactAtRoute_productSuccess :
    currentMetrizableW732SelectedCochainStableExactAtRouteStateW875.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
