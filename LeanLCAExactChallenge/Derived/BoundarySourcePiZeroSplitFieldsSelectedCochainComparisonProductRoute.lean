import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.ClosedMapLocalizedRightAdjointFieldsEndpointFieldsRoute

/-!
W1616 feeds W1615 after replacing four bundled W855 providers with their
already-checked split fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-!
W1616 closed-map branch data with W716, W717, W715, and W721 split into
field-level inputs before reassembling the W1615 concrete-field surface.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectiveForTargetProvider :
    TargetDifferenceSurjectiveForTargetProviderW713
  targetCodomainCompactSpaceProvider :
    TargetCodomainCompactSpaceProviderW601
  globalClosedMapComponents :
    SelectedDifferenceClosedMapDiagramComponentProviderW718
  mappedCokernelClosedMapProvider :
    MappedExplicitCokernelClosedMapProviderW519
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictTopologyData :
    MetrizableWppEndpointStrictTopologyDataProviderW720
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedUnitMem :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      boundedHomotopyLocalizedAdjunction.unit

/-!
W1616 closed-embedding branch data with W716, W717, W715, and W721 split into
field-level inputs before reassembling the W1615 concrete-field surface.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
  targetDifferenceSurjectiveForTargetProvider :
    TargetDifferenceSurjectiveForTargetProviderW713
  targetCodomainCompactSpaceProvider :
    TargetCodomainCompactSpaceProviderW601
  globalClosedEmbeddingComponents :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
  mappedCokernelClosedEmbeddingProvider :
    MappedExplicitCokernelClosedEmbeddingProviderW519
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictTopologyData :
    MetrizableWppEndpointStrictTopologyDataProviderW720
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedUnitMem :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      boundedHomotopyLocalizedAdjunction.unit

/-! W1616 closed-map split fields converted to the W1615 concrete-field data. -/
def closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615
    where
  boundaryData :=
    boundaryDataOfFieldsW907 data.rightOpenBoundary data.sourcePiZeroBoundary
  relationData :=
    relationDataOfFieldsW908 data.relationPullbackProvider
      data.targetRelationLiftsProvider
  targetSurjectiveCompactForTargetProvider :=
    targetDataOfFieldsW909 data.targetDifferenceSurjectiveForTargetProvider
      data.targetCodomainCompactSpaceProvider
  globalClosedMapComponents := data.globalClosedMapComponents
  mappedCokernelClosedMapProvider := data.mappedCokernelClosedMapProvider
  normalizedFixedTargetData := data.normalizedFixedTargetData
  sourceTriangulationData := data.sourceTriangulationData
  endpointStrictTopologyData := data.endpointStrictTopologyData
  localizedRightAdjointData :=
    localizedRightAdjointDataOfFieldsW912
      data.boundedHomotopyLocalizedRightAdjoint
      data.boundedHomotopyLocalizedAdjunction
      data.boundedHomotopyLocalizedUnitMem

/-!
W1616 closed-embedding split fields converted to the W1615 concrete-field data.
-/
def closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615
    where
  boundaryData :=
    boundaryDataOfFieldsW907 data.rightOpenBoundary data.sourcePiZeroBoundary
  relationData :=
    relationDataOfFieldsW908 data.relationPullbackProvider
      data.targetRelationLiftsProvider
  targetSurjectiveCompactForTargetProvider :=
    targetDataOfFieldsW909 data.targetDifferenceSurjectiveForTargetProvider
      data.targetCodomainCompactSpaceProvider
  globalClosedEmbeddingComponents := data.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    data.mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData := data.normalizedFixedTargetData
  sourceTriangulationData := data.sourceTriangulationData
  endpointStrictTopologyData := data.endpointStrictTopologyData
  localizedRightAdjointData :=
    localizedRightAdjointDataOfFieldsW912
      data.boundedHomotopyLocalizedRightAdjoint
      data.boundedHomotopyLocalizedAdjunction
      data.boundedHomotopyLocalizedUnitMem

/-! W1616 closed-map product evidence through W1615. -/
noncomputable def productEvidenceOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616 data)

/-! W1616 closed-embedding product evidence through W1615. -/
noncomputable def
    productEvidenceOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
      data)

/-! W1616 closed-map direct finite-shape stable data through W1615. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616 data)

/-! W1616 closed-embedding direct finite-shape stable data through W1615. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
      data)

/-! W1616 closed-map stable-boundary inputs through W1615. -/
noncomputable def
    stableBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616 data)

/-! W1616 closed-embedding stable-boundary inputs through W1615. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
      data)

/-! W1616 closed-map accepted stable evidence through W1615. -/
noncomputable def acceptedStableOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616 data)

/-! W1616 closed-embedding accepted stable evidence through W1615. -/
noncomputable def
    acceptedStableOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
      data)

/-! W1616 closed-map bounded derived package through W1615. -/
noncomputable def boundedDerivedOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616 data)

/-! W1616 closed-embedding bounded derived package through W1615. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
      data)

/-!
Top-level input names for the W1616 split-field selected-cochain comparison
route.
-/
def boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616 :
    List String :=
  ["right-open closed-quotient-cover boundary field",
    "source-difference cokernel pi-zero boundary field",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "target-difference surjectivity for every target diagram",
    "target-codomain compactness for every target diagram",
    "selected-difference closed-map or closed-embedding component provider",
    "matching mapped explicit cokernel closedness provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "endpoint strict-topology data provider",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit membership in boundedHomotopyExactWeakEquivalence"]

theorem boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616_count :
    boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616.length =
      14 :=
  rfl

/-! Current checked W1616 split-field selected-cochain comparison route state. -/
structure
    MetrizableBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRouteStateW1616 :
    Type where
  seed : String
  declarations : List String
  splitFieldAssemblyResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1616 state: split fields assemble four W1615 concrete-field
providers before feeding W1615.
-/
def currentMetrizableBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRouteStateW1616 :
    MetrizableBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRouteStateW1616
    where
  seed :=
    "w1616-boundary-source-pi-zero-split-fields-selected-cochain-comparison-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616",
      "closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616",
      "closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616",
      "productEvidenceOfClosedMapSplitFieldsSelectedCochainComparisonW1616",
      "productEvidenceOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616",
      "directFiniteShapeStableDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616",
      "directFiniteShapeStableDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616",
      "stableBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616",
      "stableBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616",
      "acceptedStableOfClosedMapSplitFieldsSelectedCochainComparisonW1616",
      "acceptedStableOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616",
      "boundedDerivedOfClosedMapSplitFieldsSelectedCochainComparisonW1616",
      "boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616",
      "boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616",
      "boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616_count"]
  splitFieldAssemblyResult :=
    "proved: W716 boundary data, W717 relation data, W715 target data, and\
      W721 localized-right-adjoint data are assembled from split fields before\
      feeding W1615"
  closedMapResult :=
    "proved: closed-map split-field branch data feeds the W1615 selected\
      cochain comparison surface"
  closedEmbeddingResult :=
    "proved: closed-embedding split-field branch data feeds the W1615 selected\
      cochain comparison surface"
  replacedInputs :=
    ["W716 bundled WPP right-open quotient-cover and source-pi-zero boundary data",
      "W717 bundled closed natural transformation ordinary relation data",
      "W715 bundled target-difference surjectivity plus target-codomain compactness provider",
      "W721 bounded homotopy localized-right-adjoint data provider"]
  remainingInputs :=
    boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616 ++
      ["construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem
    currentW1616BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRouteStateW1616;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
