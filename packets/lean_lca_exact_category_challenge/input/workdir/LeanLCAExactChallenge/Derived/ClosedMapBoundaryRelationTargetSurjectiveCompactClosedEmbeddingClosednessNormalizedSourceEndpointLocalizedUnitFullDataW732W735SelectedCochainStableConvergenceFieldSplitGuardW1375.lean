import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointFactsLocalizedSelectedCochainStableConvergenceFieldSplitGuardW1374
import LeanLCAExactChallenge.Derived.W735W732SelectedCochainStableExactAtRoute

/-!
W1375 records the definitional convergence from W732 route data and W735 branch
records into the W875/W876 selected-cochain stable ExactAt route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W875 W732-to-W874 reconstruction preserves the projected boundary data. -/
theorem w875RouteDataProviderBoundaryFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875 routeData).boundaryData =
      boundaryData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW732ForW875 routeData) :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected relation data. -/
theorem w875RouteDataProviderRelationFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875 routeData).relationData =
      relationData_of_boundaryRelationDataW730
        (boundaryRelationDataOfW732ForW875 routeData) :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected target compact data. -/
theorem w875RouteDataProviderTargetFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875
        routeData).targetSurjectiveCompactForTargetProvider =
      targetSurjectiveCompactForTargetProvider_of_targetClosednessDataW729
        (targetClosednessDataOfW732ForW875 routeData) :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected closedness branch. -/
theorem w875RouteDataProviderClosednessFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875
        routeData).diagramAndMappedCokernelClosednessData =
      diagramAndMappedCokernelClosednessData_of_targetClosednessDataW729
        (targetClosednessDataOfW732ForW875 routeData) :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected normalized target data. -/
theorem w875RouteDataProviderNormalizedFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875 routeData).normalizedFixedTargetData =
      normalizedFixedTargetData_of_normalizedSourceEndpointDataW728
        (normalizedSourceEndpointDataOfW732ForW875 routeData) :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected source triangulation. -/
theorem w875RouteDataProviderSourceTriangulationFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875 routeData).sourceTriangulationData =
      sourceTriangulationDataOfW732ForW875 routeData :=
  rfl

/-- W875 W732-to-W874 reconstruction preserves the projected endpoint/localized data. -/
theorem w875RouteDataProviderEndpointLocalizedFieldW1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (routeDataProviderOfW732W875
        routeData).endpointLocalizedRightAdjointData =
      endpointLocalizedDataOfW732ForW875 routeData :=
  rfl

/-- W875 direct calculus delegates to W874 after W732 reconstruction. -/
theorem w875DirectCalculusRunsThroughW874W1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        routeData =
      directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (routeDataProviderOfW732W875 routeData) :=
  rfl

/-- W875 stable package delegates to W874 after W732 reconstruction. -/
theorem w875StablePackageRunsThroughW874W1375
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        routeData =
      boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (routeDataProviderOfW732W875 routeData) :=
  rfl

/-- W876 closed-map W735 route data is exactly the W855 route-data constructor. -/
theorem w876ClosedMapRouteDataRunsThroughW855W1375
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    routeDataProviderOfClosedMapW735ForW876 inputs =
      closedMapRouteDataProviderOfComparisonBijectivityW855 inputs :=
  rfl

/-- W876 closed-embedding W735 route data is exactly the W855 route-data constructor. -/
theorem w876ClosedEmbeddingRouteDataRunsThroughW855W1375
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    routeDataProviderOfClosedEmbeddingW735ForW876 inputs =
      closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs :=
  rfl

/-- W876 closed-map direct calculus delegates to W875 after W855 route-data construction. -/
theorem w876ClosedMapDirectCalculusRunsThroughW875W1375
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedMapW735W732SelectedCochainStableExactAtW876
        inputs =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735ForW876 inputs) :=
  rfl

/-- W876 closed-embedding direct calculus delegates to W875 after W855 route-data construction. -/
theorem w876ClosedEmbeddingDirectCalculusRunsThroughW875W1375
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
        inputs =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735ForW876 inputs) :=
  rfl

/-- W876 closed-map stable package delegates to W875 after W855 route-data construction. -/
theorem w876ClosedMapStablePackageRunsThroughW875W1375
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedMapW735W732SelectedCochainStableExactAtW876
        inputs =
      boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735ForW876 inputs) :=
  rfl

/-- W876 closed-embedding stable package delegates to W875 after W855 route-data construction. -/
theorem w876ClosedEmbeddingStablePackageRunsThroughW875W1375
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
        inputs =
      boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735ForW876 inputs) :=
  rfl

/-- W1375 keeps the W875 W732 input count visible. -/
theorem w1375W732SelectedCochainStableExactAtInputCountMatchesW875 :
    w732SelectedCochainStableExactAtInputNamesW875.length = 1 :=
  w732SelectedCochainStableExactAtInputNamesW875_count

/-- W1375 keeps the W876 W735 branch input count visible. -/
theorem w1375W735W732SelectedCochainStableExactAtInputCountMatchesW876 :
    w735W732SelectedCochainStableExactAtInputNamesW876.length = 9 :=
  w735W732SelectedCochainStableExactAtInputNamesW876_count

/-- Current W1375 nonterminal state. -/
structure W732W735SelectedCochainStableConvergenceStateW1375 : Type where
  seed : String
  declarations : List String
  w732ProjectionResult : String
  w735RouteDataResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1375 records W732/W735 convergence into W875/W876 stable ExactAt evidence. -/
def currentW732W735SelectedCochainStableConvergenceStateW1375 :
    W732W735SelectedCochainStableConvergenceStateW1375 where
  seed := "w1375-w732-w735-selected-cochain-stable-convergence"
  declarations :=
    ["w875RouteDataProviderBoundaryFieldW1375",
      "w875RouteDataProviderRelationFieldW1375",
      "w875RouteDataProviderTargetFieldW1375",
      "w875RouteDataProviderClosednessFieldW1375",
      "w875RouteDataProviderNormalizedFieldW1375",
      "w875RouteDataProviderSourceTriangulationFieldW1375",
      "w875RouteDataProviderEndpointLocalizedFieldW1375",
      "w875DirectCalculusRunsThroughW874W1375",
      "w875StablePackageRunsThroughW874W1375",
      "w876ClosedMapRouteDataRunsThroughW855W1375",
      "w876ClosedEmbeddingRouteDataRunsThroughW855W1375",
      "w876ClosedMapDirectCalculusRunsThroughW875W1375",
      "w876ClosedEmbeddingDirectCalculusRunsThroughW875W1375",
      "w876ClosedMapStablePackageRunsThroughW875W1375",
      "w876ClosedEmbeddingStablePackageRunsThroughW875W1375",
      "w1375W732SelectedCochainStableExactAtInputCountMatchesW875",
      "w1375W735W732SelectedCochainStableExactAtInputCountMatchesW876"]
  w732ProjectionResult :=
    "proved: W875 reconstructs the seven-field W874 endpoint-localized route \
      surface from the one-provider W732 route-data surface"
  w735RouteDataResult :=
    "proved: W876 closed-map and closed-embedding W735 branches construct W732 \
      route data through W855 and delegate direct calculus/stable package to W875"
  remainingInputs :=
    w735W732SelectedCochainStableExactAtInputNamesW876
  productSuccessClaimed := false

theorem currentW1375W732W735SelectedCochainStableConvergence_productSuccess :
    currentW732W735SelectedCochainStableConvergenceStateW1375.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
