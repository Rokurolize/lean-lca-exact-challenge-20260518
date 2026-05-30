import LeanLCAExactChallenge.Derived.ComparisonBijectivityRoute
import LeanLCAExactChallenge.Derived.HomologyFreeRouteDataProviderFromRouteData

/-!
W855 removes the explicit `CategoryWithHomology MetrizableLCA` premise from the
W735-to-W732 route-data surface by using the W821 comparison-bijectivity proof.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W855 exposes the W821 no-input homology structure in the namespace used by the
W732 route-data constructors.
-/
theorem categoryWithHomologyOfComparisonBijectivityW855 :
    CategoryWithHomology MetrizableLCA.{0} :=
  MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821

/-- W855 packages the W821 homology structure as the W723 provider. -/
def categoryWithHomologyProviderOfComparisonBijectivityW855 :
    MetrizableWppCategoryWithHomologyProviderW723
    where
  categoryWithHomology := categoryWithHomologyOfComparisonBijectivityW855

/--
W855 reconstructs source homological-triangulation data from ordinary source
triangulation data using W821, with no caller-supplied homology typeclass.
-/
def sourceHomologicalTriangulationDataOfComparisonBijectivityW855
    (sourceTriangulationData : MetrizableWppSourceTriangulationDataProviderW722) :
    MetrizableWppSourceHomologicalTriangulationDataProviderW724
    where
  categoryWithHomologyProvider :=
    categoryWithHomologyProviderOfComparisonBijectivityW855
  sourceTriangulationData := sourceTriangulationData

/--
W855 closed-map branch: W735 branch data now constructs W733 leaves using the
W821 homology theorem instead of an explicit `CategoryWithHomology` premise.
-/
def closedMapConcreteLeavesOfComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733
    where
  boundaryData := inputs.boundaryData
  relationData := inputs.relationData
  targetSurjectiveCompactForTargetProvider :=
    inputs.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    .closedMap inputs.globalClosedMapComponents
      inputs.mappedCokernelClosedMapProvider
  normalizedFixedTargetData := inputs.normalizedFixedTargetData
  sourceHomologicalTriangulationData :=
    sourceHomologicalTriangulationDataOfComparisonBijectivityW855
      inputs.sourceTriangulationData
  endpointStrictTopologyData := inputs.endpointStrictTopologyData
  localizedRightAdjointData := inputs.localizedRightAdjointData

/--
W855 closed-embedding branch: W735 branch data now constructs W733 leaves using
the W821 homology theorem instead of an explicit `CategoryWithHomology` premise.
-/
def closedEmbeddingConcreteLeavesOfComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733
    where
  boundaryData := inputs.boundaryData
  relationData := inputs.relationData
  targetSurjectiveCompactForTargetProvider :=
    inputs.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    .closedEmbedding inputs.globalClosedEmbeddingComponents
      inputs.mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData := inputs.normalizedFixedTargetData
  sourceHomologicalTriangulationData :=
    sourceHomologicalTriangulationDataOfComparisonBijectivityW855
      inputs.sourceTriangulationData
  endpointStrictTopologyData := inputs.endpointStrictTopologyData
  localizedRightAdjointData := inputs.localizedRightAdjointData

/-- W855 closed-map W732 route-data provider from a W735 branch record. -/
def closedMapRouteDataProviderOfComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  boundaryRelationTargetClosednessNormalizedDataProvider_of_concreteLeavesW733
    (closedMapConcreteLeavesOfComparisonBijectivityW855 inputs)

/-- W855 closed-embedding W732 route-data provider from a W735 branch record. -/
def closedEmbeddingRouteDataProviderOfComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  boundaryRelationTargetClosednessNormalizedDataProvider_of_concreteLeavesW733
    (closedEmbeddingConcreteLeavesOfComparisonBijectivityW855 inputs)

/-- W855 closed-map W853 provider through the W854 W732-to-homology-free route. -/
def homologyFreeRouteDataProviderOfClosedMapComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854
    (closedMapRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-embedding W853 provider through the W854 W732-to-homology-free route. -/
def homologyFreeRouteDataProviderOfClosedEmbeddingComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854
    (closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-map selected-cochain direct-source data. -/
noncomputable def selectedCochainDirectSourceDataOfClosedMapComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :=
  selectedCochainDirectSourceDataOfRouteDataViaHomologyFreeW854
    (closedMapRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-embedding selected-cochain direct-source data. -/
noncomputable def
    selectedCochainDirectSourceDataOfClosedEmbeddingComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :=
  selectedCochainDirectSourceDataOfRouteDataViaHomologyFreeW854
    (closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-map direct bounded left calculus from W735 branch data. -/
theorem directBoundedLeftCalculusOfClosedMapComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfRouteDataViaHomologyFreeW854
    (closedMapRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-embedding direct bounded left calculus from W735 branch data. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfRouteDataViaHomologyFreeW854
    (closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-map bounded derived infinity-category package from W735 branch data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapComparisonBijectivityW855
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfRouteDataViaHomologyFreeW854
    (closedMapRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- W855 closed-embedding bounded derived infinity-category package from W735 branch data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonBijectivityW855
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfRouteDataViaHomologyFreeW854
    (closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs)

/-- Concrete field names still carried by the W735 branch record after W855. -/
def comparisonBijectivityRouteDataBranchInputNamesW855 : List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation ordinary relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "closed-map or closed-embedding selected-difference component provider",
    "matching W519 mapped-explicit-cokernel closedness provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "endpoint strict-topology data provider",
    "bounded homotopy localized-right-adjoint data provider"]

theorem comparisonBijectivityRouteDataBranchInputNamesW855_count :
    comparisonBijectivityRouteDataBranchInputNamesW855.length = 9 :=
  rfl

structure MetrizableComparisonBijectivityRouteDataProviderStateW855 :
    Type where
  seed : String
  declarations : List String
  homologyResult : String
  routeDataResult : String
  selectedCochainResult : String
  leftCalculusResult : String
  stablePackageResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComparisonBijectivityRouteDataProviderStateW855 :
    MetrizableComparisonBijectivityRouteDataProviderStateW855
    where
  seed := "w855-comparison-bijectivity-w735-to-w732-route-data"
  declarations :=
    ["Dbounded.categoryWithHomologyOfComparisonBijectivityW855",
      "Dbounded.categoryWithHomologyProviderOfComparisonBijectivityW855",
      "Dbounded.sourceHomologicalTriangulationDataOfComparisonBijectivityW855",
      "Dbounded.closedMapConcreteLeavesOfComparisonBijectivityW855",
      "Dbounded.closedEmbeddingConcreteLeavesOfComparisonBijectivityW855",
      "Dbounded.closedMapRouteDataProviderOfComparisonBijectivityW855",
      "Dbounded.closedEmbeddingRouteDataProviderOfComparisonBijectivityW855",
      "Dbounded.homologyFreeRouteDataProviderOfClosedMapComparisonBijectivityW855",
      "Dbounded.homologyFreeRouteDataProviderOfClosedEmbeddingComparisonBijectivityW855",
      "Dbounded.selectedCochainDirectSourceDataOfClosedMapComparisonBijectivityW855",
      "Dbounded.selectedCochainDirectSourceDataOfClosedEmbeddingComparisonBijectivityW855",
      "Dbounded.directBoundedLeftCalculusOfClosedMapComparisonBijectivityW855",
      "Dbounded.directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityW855",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedMapComparisonBijectivityW855",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonBijectivityW855",
      "Dbounded.comparisonBijectivityRouteDataBranchInputNamesW855",
      "Dbounded.comparisonBijectivityRouteDataBranchInputNamesW855_count"]
  homologyResult :=
    "proved: W821 supplies CategoryWithHomology MetrizableLCA without an input"
  routeDataResult :=
    "proved: W735 branch records construct W732 route-data providers without a\
      CategoryWithHomology premise"
  selectedCochainResult :=
    "proved: the constructed W732 providers feed the W854 homology-free\
      selected-cochain direct-source route"
  leftCalculusResult :=
    "proved: W735 branch records now supply direct bounded left calculus through\
      W821, W732, and W854"
  stablePackageResult :=
    "proved: W735 branch records now supply the existing bounded derived\
      infinity-category package through W821, W732, and W854"
  removedInputs :=
    ["explicit CategoryWithHomology MetrizableLCA premise at the W735-to-W732\
      route-data surface"]
  remainingInputs :=
    ["construct concrete values for the nine W735 branch data fields",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW855ComparisonBijectivityRouteDataProvider_productSuccess :
    currentMetrizableComparisonBijectivityRouteDataProviderStateW855.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
