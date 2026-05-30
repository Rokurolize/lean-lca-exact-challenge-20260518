import LeanLCAExactChallenge.Derived.ClosedRangeDirectFiniteShapeProductRoute

/-!
W773 reuses the W722 source-triangulation data already carried by each W735
branch input as the W657 direct-localization source core required by W772.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W773 closed-map branch data using W735 source-triangulation data. -/
structure
    MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  directSource :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W773 closed-embedding branch data using W735 source-triangulation data. -/
structure
    MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  directSource :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W773 derives W657 direct-localization data from closed-map W735 source data. -/
def directLocalizationOfClosedMapSourceTriangulationW773
    (data :
      MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
    where
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData

/-- W773 derives W657 direct-localization data from closed-embedding W735 source data. -/
def directLocalizationOfClosedEmbeddingSourceTriangulationW773
    (data :
      MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
    where
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData

/-- W773 closed-map branch converted to W772 data. -/
noncomputable def closedMapClosedRangeDataOfSourceTriangulationW773
    (data :
      MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  closedRangeEndpointTopology := data.closedRangeEndpointTopology
  directLocalization :=
    directLocalizationOfClosedMapSourceTriangulationW773 data

/-- W773 closed-embedding branch converted to W772 data. -/
noncomputable def closedEmbeddingClosedRangeDataOfSourceTriangulationW773
    (data :
      MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  closedRangeEndpointTopology := data.closedRangeEndpointTopology
  directLocalization :=
    directLocalizationOfClosedEmbeddingSourceTriangulationW773 data

/-- W773 closed-map product evidence through W735 source data and W772. -/
noncomputable def
    productEvidence_of_closedMapSourceTriangulationClosedRangeDirectFiniteShapeRouteW773
    (data :
      MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapClosedRangeDirectFiniteShapeRouteW772
    (closedMapClosedRangeDataOfSourceTriangulationW773 data)

/-- W773 closed-embedding product evidence through W735 source data and W772. -/
noncomputable def
    productEvidence_of_closedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeRouteW773
    (data :
      MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingClosedRangeDirectFiniteShapeRouteW772
    (closedEmbeddingClosedRangeDataOfSourceTriangulationW773 data)

/-- W773 input names after W735 source-triangulation data supplies W657. -/
def sourceTriangulationClosedRangeDirectFiniteShapeProductRouteInputNamesW773 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W721 localized\
      and W722 source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "W696 closed-range endpoint topology data"]

theorem
    sourceTriangulationClosedRangeDirectFiniteShapeProductRouteInputNamesW773_count :
    sourceTriangulationClosedRangeDirectFiniteShapeProductRouteInputNamesW773.length =
      5 :=
  rfl

/-- Current checked W773 state. -/
structure MetrizableSourceTriangulationClosedRangeDirectFiniteShapeProductRouteStateW773 :
    Type where
  seed : String
  declarations : List String
  sourceTriangulationResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W773 state for source-triangulation direct finite-shape routes. -/
def currentMetrizableSourceTriangulationClosedRangeDirectFiniteShapeProductRouteSupportStateW773 :
    MetrizableSourceTriangulationClosedRangeDirectFiniteShapeProductRouteStateW773
    where
  seed := "w773-source-triangulation-closed-range-direct-finite-shape-product-route"
  declarations :=
    ["MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773",
      "MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773",
      "directLocalizationOfClosedMapSourceTriangulationW773",
      "directLocalizationOfClosedEmbeddingSourceTriangulationW773",
      "closedMapClosedRangeDataOfSourceTriangulationW773",
      "closedEmbeddingClosedRangeDataOfSourceTriangulationW773",
      "productEvidence_of_closedMapSourceTriangulationClosedRangeDirectFiniteShapeRouteW773",
      "productEvidence_of_closedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeRouteW773",
      "sourceTriangulationClosedRangeDirectFiniteShapeProductRouteInputNamesW773",
      "sourceTriangulationClosedRangeDirectFiniteShapeProductRouteInputNamesW773_count"]
  sourceTriangulationResult :=
    "proved: W735 branch source-triangulation data supplies the W772\
      direct-localization source core"
  closedMapResult :=
    "proved: closed-map W735 branch data plus W696 topology feed the W772\
      route without a separate direct-localization field"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus W696 topology feed the W772\
      route without a separate direct-localization field"
  replacedInputs :=
    ["separate MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct direct finite-shape WPP source data",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW773SourceTriangulationClosedRangeProductRouteState_productSuccess :
    (let state :=
      currentMetrizableSourceTriangulationClosedRangeDirectFiniteShapeProductRouteSupportStateW773;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
