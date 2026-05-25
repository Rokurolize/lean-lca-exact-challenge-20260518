import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableRoute

/-!
W852 routes the W732 one-provider route-data surface into the W851
comparison-selected-cochain stable package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W852 closed-map W735 branch rebuilt from W763-projected W733 leaves. -/
def closedMapExactInputsOfRouteDataLeavesW852
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733)
    (globalClosedMapComponents :
      SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  globalClosedMapComponents := globalClosedMapComponents
  mappedCokernelClosedMapProvider := mappedCokernelClosedMapProvider
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData :=
    sourceTriangulationData_of_sourceHomologicalTriangulationDataW724
      leaves.sourceHomologicalTriangulationData
  endpointStrictTopologyData := leaves.endpointStrictTopologyData
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W852 closed-embedding W735 branch rebuilt from W763-projected W733 leaves. -/
def closedEmbeddingExactInputsOfRouteDataLeavesW852
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  globalClosedEmbeddingComponents := globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider := mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData :=
    sourceTriangulationData_of_sourceHomologicalTriangulationDataW724
      leaves.sourceHomologicalTriangulationData
  endpointStrictTopologyData := leaves.endpointStrictTopologyData
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- Branch-shaped W847 data produced from W732 route data. -/
inductive MetrizableRouteDataSelectedCochainDirectSourceDataW852 :
    Type 2 where
  | closedMap
      (data :
        MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847)
  | closedEmbedding
      (data :
        MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847)

/--
W852 turns one W732 route-data provider into W847 selected-cochain data, with
the closedness branch deciding the closed-map or closed-embedding path.
-/
noncomputable def selectedCochainDirectSourceDataOfRouteDataW852
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableRouteDataSelectedCochainDirectSourceDataW852 :=
  let leaves :=
    boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData
  match leaves.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      .closedMap
        (closedMapSelectedCochainDirectSourceDataOfComparisonW851
          (closedMapExactInputsOfRouteDataLeavesW852 leaves
            globalClosedMapComponents mappedCokernelClosedMapProvider))
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      .closedEmbedding
        (closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851
          (closedEmbeddingExactInputsOfRouteDataLeavesW852 leaves
            globalClosedEmbeddingComponents
            mappedCokernelClosedEmbeddingProvider))

/-- W852 direct bounded left calculus from one W732 route-data provider. -/
theorem directBoundedLeftCalculusOfRouteDataComparisonSelectedCochainW852
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  let leaves :=
    boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData
  match leaves.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainW851
        (closedMapExactInputsOfRouteDataLeavesW852 leaves
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainW851
        (closedEmbeddingExactInputsOfRouteDataLeavesW852 leaves
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

/--
W852 bounded derived infinity-category package from one W732 route-data
provider.
-/
noncomputable def boundedDerivedInfinityCategoryOfRouteDataComparisonSelectedCochainW852
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  let leaves :=
    boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData
  match leaves.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainW851
        (closedMapExactInputsOfRouteDataLeavesW852 leaves
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainW851
        (closedEmbeddingExactInputsOfRouteDataLeavesW852 leaves
          globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)

def routeDataSelectedCochainStableRouteInputNamesW852 : List String :=
  ["one W732 boundary/relation target/closedness normalized source/endpoint\
      route-data provider"]

theorem routeDataSelectedCochainStableRouteInputNamesW852_count :
    routeDataSelectedCochainStableRouteInputNamesW852.length =
      1 :=
  rfl

structure MetrizableRouteDataSelectedCochainStableRouteStateW852 :
    Type where
  seed : String
  declarations : List String
  leafProjectionResult : String
  branchAssemblyResult : String
  leftCalculusResult : String
  stablePackageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableRouteDataSelectedCochainStableRouteStateW852 :
    MetrizableRouteDataSelectedCochainStableRouteStateW852
    where
  seed := "w852-route-data-selected-cochain-stable-route"
  declarations :=
    ["Dbounded.closedMapExactInputsOfRouteDataLeavesW852",
      "Dbounded.closedEmbeddingExactInputsOfRouteDataLeavesW852",
      "Dbounded.MetrizableRouteDataSelectedCochainDirectSourceDataW852",
      "Dbounded.selectedCochainDirectSourceDataOfRouteDataW852",
      "Dbounded.directBoundedLeftCalculusOfRouteDataComparisonSelectedCochainW852",
      "Dbounded.boundedDerivedInfinityCategoryOfRouteDataComparisonSelectedCochainW852",
      "Dbounded.routeDataSelectedCochainStableRouteInputNamesW852",
      "Dbounded.routeDataSelectedCochainStableRouteInputNamesW852_count"]
  leafProjectionResult :=
    "proved: W763 projects one W732 route-data provider to W733 concrete leaves"
  branchAssemblyResult :=
    "proved: the W733 closedness branch rebuilds the matching W735 branch input"
  leftCalculusResult :=
    "proved: one W732 route-data provider supplies direct bounded left calculus"
  stablePackageResult :=
    "proved: one W732 route-data provider supplies the existing bounded derived\
      infinity-category package"
  remainingInputs :=
    ["construct a concrete W732 route-data provider",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW852RouteDataSelectedCochainStableRoute_productSuccess :
    currentMetrizableRouteDataSelectedCochainStableRouteStateW852.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
