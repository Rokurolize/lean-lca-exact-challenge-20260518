import LeanLCAExactChallenge.Derived.HomotopyObjectTriangulatedSelectedW461RowsProductRoute

/-!
W783 feeds W782 by replacing the exact-acyclic homotopy-object `Closed₂`
premise with the existing strict mapping-cone triangle-realization input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W783 strict realization input for exact-acyclic homotopy-object `Closed₂`. -/
abbrev MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 :
    Prop :=
  exactAcyclicHomotopyObjectTrianglehIso13Realization MetrizableLCA.{0}

/--
W783 turns the exact-acyclic homotopy-object strict-realization input into
W782's homotopy-object `Closed₂` input.
-/
theorem homotopyObjectClosed2OfTrianglehRealizationW783
    (realize :
      MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783) :
    MetrizableExactAcyclicHomotopyObjectClosed2InputW782 :=
  exactAcyclicHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
    MetrizableLCA.{0} realize

/--
W783 closed-map branch data using strict triangle-realization data instead of
W782's exact-acyclic homotopy-object `Closed₂` input.
-/
structure
    MetrizableClosedMapTrianglehRealizationHomotopyObjectBranchDataW783 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W783 closed-embedding branch data using strict triangle-realization data
instead of W782's exact-acyclic homotopy-object `Closed₂` input.
-/
structure
    MetrizableClosedEmbeddingTrianglehRealizationHomotopyObjectBranchDataW783 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W783 closed-map branch converted to W782 branch data. -/
noncomputable def closedMapHomotopyObjectDataOfTrianglehRealizationW783
    (data : MetrizableClosedMapTrianglehRealizationHomotopyObjectBranchDataW783) :
    MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782
    where
  comparisonIso := data.comparisonIso
  homotopyObjectClosed2 :=
    homotopyObjectClosed2OfTrianglehRealizationW783 data.trianglehRealization
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W783 closed-embedding branch converted to W782 branch data. -/
noncomputable def closedEmbeddingHomotopyObjectDataOfTrianglehRealizationW783
    (data :
      MetrizableClosedEmbeddingTrianglehRealizationHomotopyObjectBranchDataW783) :
    MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782
    where
  comparisonIso := data.comparisonIso
  homotopyObjectClosed2 :=
    homotopyObjectClosed2OfTrianglehRealizationW783 data.trianglehRealization
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W783 closed-map product evidence through strict triangle-realization data. -/
noncomputable def productEvidence_of_closedMapTrianglehRealizationRouteW783
    (data : MetrizableClosedMapTrianglehRealizationHomotopyObjectBranchDataW783) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapHomotopyObjectTriangulatedRouteW782
    (closedMapHomotopyObjectDataOfTrianglehRealizationW783 data)

/-- W783 closed-embedding product evidence through strict triangle-realization data. -/
noncomputable def productEvidence_of_closedEmbeddingTrianglehRealizationRouteW783
    (data :
      MetrizableClosedEmbeddingTrianglehRealizationHomotopyObjectBranchDataW783) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingHomotopyObjectTriangulatedRouteW782
    (closedEmbeddingHomotopyObjectDataOfTrianglehRealizationW783 data)

/-- W783 input names after replacing W782's homotopy-object `Closed₂` premise. -/
def trianglehRealizationHomotopyObjectProductRouteInputNamesW783 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exact-acyclic homotopy-object triangleh iso13 realization data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem trianglehRealizationHomotopyObjectProductRouteInputNamesW783_count :
    trianglehRealizationHomotopyObjectProductRouteInputNamesW783.length = 8 :=
  rfl

/-- Current checked W783 state. -/
structure MetrizableTrianglehRealizationHomotopyObjectRouteStateW783 :
    Type where
  seed : String
  declarations : List String
  transportResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W783 state for the strict triangle-realization route. -/
def currentMetrizableTrianglehRealizationHomotopyObjectRouteStateW783 :
    MetrizableTrianglehRealizationHomotopyObjectRouteStateW783
    where
  seed := "w783-triangleh-realization-homotopy-object-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783",
      "homotopyObjectClosed2OfTrianglehRealizationW783",
      "MetrizableClosedMapTrianglehRealizationHomotopyObjectBranchDataW783",
      "MetrizableClosedEmbeddingTrianglehRealizationHomotopyObjectBranchDataW783",
      "closedMapHomotopyObjectDataOfTrianglehRealizationW783",
      "closedEmbeddingHomotopyObjectDataOfTrianglehRealizationW783",
      "productEvidence_of_closedMapTrianglehRealizationRouteW783",
      "productEvidence_of_closedEmbeddingTrianglehRealizationRouteW783",
      "trianglehRealizationHomotopyObjectProductRouteInputNamesW783",
      "trianglehRealizationHomotopyObjectProductRouteInputNamesW783_count"]
  transportResult :=
    "proved: exact-acyclic homotopy-object triangleh realization supplies W782's Closed2 input"
  closedMapResult :=
    "proved: closed-map triangleh realization branch data feeds W782"
  closedEmbeddingResult :=
    "proved: closed-embedding triangleh realization branch data feeds W782"
  replacedInputs :=
    ["exactAcyclicHomotopyObject MetrizableLCA is triangulated closed"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object triangleh iso13 realization data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW783TrianglehRealizationRoute_productSuccess :
    (have state :=
      currentMetrizableTrianglehRealizationHomotopyObjectRouteStateW783;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
