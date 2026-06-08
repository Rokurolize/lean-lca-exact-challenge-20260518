import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.RouteDataProviderFromComparisonBijectivity

/-!
W1615 feeds W1614 after exposing the W735 exact-input branch as its concrete
field surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-!
W1615 closed-map branch data with the concrete fields carried by the W735
closed-map exact-input record.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
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
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-!
W1615 closed-embedding branch data with the concrete fields carried by the
W735 closed-embedding exact-input record.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
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
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-!
W1615 closed-map concrete fields converted to the W1614 W735 exact-input
surface.
-/
def closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := data.boundaryData
  relationData := data.relationData
  targetSurjectiveCompactForTargetProvider :=
    data.targetSurjectiveCompactForTargetProvider
  globalClosedMapComponents := data.globalClosedMapComponents
  mappedCokernelClosedMapProvider := data.mappedCokernelClosedMapProvider
  normalizedFixedTargetData := data.normalizedFixedTargetData
  sourceTriangulationData := data.sourceTriangulationData
  endpointStrictTopologyData := data.endpointStrictTopologyData
  localizedRightAdjointData := data.localizedRightAdjointData

/-!
W1615 closed-embedding concrete fields converted to the W1614 W735 exact-input
surface.
-/
def closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
    where
  boundaryData := data.boundaryData
  relationData := data.relationData
  targetSurjectiveCompactForTargetProvider :=
    data.targetSurjectiveCompactForTargetProvider
  globalClosedEmbeddingComponents := data.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    data.mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData := data.normalizedFixedTargetData
  sourceTriangulationData := data.sourceTriangulationData
  endpointStrictTopologyData := data.endpointStrictTopologyData
  localizedRightAdjointData := data.localizedRightAdjointData

/-!
W1615 closed-map product evidence after unpacking concrete fields into W735
exact inputs.
-/
noncomputable def
    productEvidenceOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding product evidence after unpacking concrete fields into
W735 exact inputs.
-/
noncomputable def
    productEvidenceOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map direct finite-shape stable data through W1614.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding direct finite-shape stable data through W1614.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map stable-boundary inputs through W1614.
-/
noncomputable def
    stableBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding stable-boundary inputs through W1614.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map concrete fields as canonical direct-localization
stable-instance boundary inputs through W1614.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding concrete fields as canonical direct-localization
stable-instance boundary inputs through W1614.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map accepted stable evidence through W1614.
-/
noncomputable def acceptedStableOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding accepted stable evidence through W1614.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map bounded derived package through W1614.
-/
noncomputable def
    boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding bounded derived package through W1614.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
W1615 closed-map bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615 data)

/-!
W1615 closed-embedding bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
      data)

/-!
Top-level input names for the W1615 concrete-field selected-cochain comparison
route.
-/
def boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615 :
    List String :=
  comparisonBijectivityRouteDataBranchInputNamesW855

theorem
    boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615_count :
    boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615.length =
      9 :=
  comparisonBijectivityRouteDataBranchInputNamesW855_count

/-!
Current checked W1615 concrete-field selected-cochain comparison route state.
-/
structure
    MetrizableBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRouteStateW1615 :
    Type where
  seed : String
  declarations : List String
  exactInputAssemblyResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1615 state: concrete branch fields assemble the W735 record
consumed by W1614.
-/
def
    currentMetrizableBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRouteStateW1615 :
    MetrizableBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRouteStateW1615
    where
  seed :=
    "w1615-boundary-source-pi-zero-concrete-fields-selected-cochain-comparison-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615",
      "closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615",
      "closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615",
      "productEvidenceOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "productEvidenceOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "directFiniteShapeStableDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "directFiniteShapeStableDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "stableBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "stableBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "directLocalizationBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "directLocalizationBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "acceptedStableOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "acceptedStableOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "acceptedStableOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615",
      "acceptedStableOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615",
      "boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615",
      "boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615",
      "boundedDerivedOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615",
      "boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615",
      "boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615",
      "boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615_count"]
  exactInputAssemblyResult :=
    "proved: the W735 exact-input record is assembled from its concrete branch\
      fields before feeding W1614"
  closedMapResult :=
    "proved: closed-map concrete branch fields feed W1614 without leaving the\
      W735 wrapper as the top-level input, including the canonical\
      direct-localization stable-instance boundary"
  closedEmbeddingResult :=
    "proved: closed-embedding concrete branch fields feed W1614 without\
      leaving the W735 wrapper as the top-level input, including the canonical\
      direct-localization stable-instance boundary"
  replacedInputs :=
    boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614
  remainingInputs :=
    boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615 ++
      ["construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem
    currentW1615BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRouteStateW1615;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
