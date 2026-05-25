import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableRoute

/-!
W853 uses the W831 comparison route to avoid carrying category-homology data in
the remaining selected-cochain provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W853 one-provider surface for the data W851 actually consumes after W831
supplies the comparison route.
-/
structure MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :
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
  endpointStrictTopologyData :
    MetrizableWppEndpointStrictTopologyDataProviderW720
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W853 closed-map W735 branch rebuilt from the homology-free provider. -/
def closedMapExactInputsOfHomologyFreeRouteDataW853
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853)
    (globalClosedMapComponents :
      SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := routeData.boundaryData
  relationData := routeData.relationData
  targetSurjectiveCompactForTargetProvider :=
    routeData.targetSurjectiveCompactForTargetProvider
  globalClosedMapComponents := globalClosedMapComponents
  mappedCokernelClosedMapProvider := mappedCokernelClosedMapProvider
  normalizedFixedTargetData := routeData.normalizedFixedTargetData
  sourceTriangulationData := routeData.sourceTriangulationData
  endpointStrictTopologyData := routeData.endpointStrictTopologyData
  localizedRightAdjointData := routeData.localizedRightAdjointData

/-- W853 closed-embedding W735 branch rebuilt from the homology-free provider. -/
def closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := routeData.boundaryData
  relationData := routeData.relationData
  targetSurjectiveCompactForTargetProvider :=
    routeData.targetSurjectiveCompactForTargetProvider
  globalClosedEmbeddingComponents := globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider := mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData := routeData.normalizedFixedTargetData
  sourceTriangulationData := routeData.sourceTriangulationData
  endpointStrictTopologyData := routeData.endpointStrictTopologyData
  localizedRightAdjointData := routeData.localizedRightAdjointData

/-- Branch-shaped W847 data produced from the W853 provider. -/
inductive MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :
    Type 2 where
  | closedMap
      (data :
        MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847)
  | closedEmbedding
      (data :
        MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847)

/-- W853 turns the homology-free provider into W847 selected-cochain data. -/
noncomputable def selectedCochainDirectSourceDataOfHomologyFreeRouteDataW853
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      .closedMap
        (closedMapSelectedCochainDirectSourceDataOfComparisonW851
          (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
            globalClosedMapComponents mappedCokernelClosedMapProvider))
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      .closedEmbedding
        (closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851
          (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
            globalClosedEmbeddingComponents
            mappedCokernelClosedEmbeddingProvider))

/-- W853 direct bounded left calculus from the homology-free provider. -/
theorem directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainW853
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainW851
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainW851
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/--
W853 bounded derived infinity-category package from the homology-free provider.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainW853
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainW851
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainW851
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

def homologyFreeSelectedCochainStableRouteInputNamesW853 : List String :=
  ["one homology-free selected-cochain route-data provider"]

theorem homologyFreeSelectedCochainStableRouteInputNamesW853_count :
    homologyFreeSelectedCochainStableRouteInputNamesW853.length =
      1 :=
  rfl

structure MetrizableHomologyFreeSelectedCochainStableRouteStateW853 :
    Type where
  seed : String
  declarations : List String
  removedPayloadResult : String
  branchAssemblyResult : String
  leftCalculusResult : String
  stablePackageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableHomologyFreeSelectedCochainStableRouteStateW853 :
    MetrizableHomologyFreeSelectedCochainStableRouteStateW853
    where
  seed := "w853-homology-free-selected-cochain-stable-route"
  declarations :=
    ["Dbounded.MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853",
      "Dbounded.closedMapExactInputsOfHomologyFreeRouteDataW853",
      "Dbounded.closedEmbeddingExactInputsOfHomologyFreeRouteDataW853",
      "Dbounded.selectedCochainDirectSourceDataOfHomologyFreeRouteDataW853",
      "Dbounded.directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainW853",
      "Dbounded.boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainW853",
      "Dbounded.homologyFreeSelectedCochainStableRouteInputNamesW853",
      "Dbounded.homologyFreeSelectedCochainStableRouteInputNamesW853_count"]
  removedPayloadResult :=
    "proved: W831 removes the need to carry category-homology data in this provider"
  branchAssemblyResult :=
    "proved: the provider's closedness branch rebuilds the matching W735 branch"
  leftCalculusResult :=
    "proved: one homology-free provider supplies direct bounded left calculus"
  stablePackageResult :=
    "proved: one homology-free provider supplies the existing bounded derived\
      infinity-category package"
  remainingInputs :=
    ["construct a concrete homology-free selected-cochain route-data provider",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW853HomologyFreeSelectedCochainStableRoute_productSuccess :
    currentMetrizableHomologyFreeSelectedCochainStableRouteStateW853.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
