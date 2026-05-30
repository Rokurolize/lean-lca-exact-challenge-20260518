import LeanLCAExactChallenge.Derived.TrianglehRealizationHomotopyObjectSelectedW461RowsProductRoute

/-!
W784 feeds W783 by replacing the strict exact-acyclic homotopy-object
triangle-realization input with the existing target-isomorphism realization
input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W784 target-isomorphism realization input for exact-acyclic homotopy objects. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :
    Prop :=
  exactAcyclicHomotopyObjectTrianglehIso13TargetIsoRealization
    MetrizableLCA.{0}

/--
W784 turns target-isomorphism realization data into W783's strict triangleh
realization input.
-/
theorem trianglehRealizationOfTargetIsoRealizationW784
    (realize : MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 :=
  exactAcyclicHomotopyObjectTrianglehIso13Realization_of_targetIsoRealization
    MetrizableLCA.{0} realize

/--
W784 closed-map branch data using target-isomorphism realization data instead
of W783's strict triangleh realization input.
-/
structure MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
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
W784 closed-embedding branch data using target-isomorphism realization data
instead of W783's strict triangleh realization input.
-/
structure MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
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

/-- W784 closed-map branch converted to W783 branch data. -/
noncomputable def closedMapTrianglehDataOfTargetIsoRealizationW784
    (data : MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784) :
    MetrizableClosedMapTrianglehRealizationHomotopyObjectBranchDataW783
    where
  comparisonIso := data.comparisonIso
  trianglehRealization :=
    trianglehRealizationOfTargetIsoRealizationW784 data.targetIsoRealization
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W784 closed-embedding branch converted to W783 branch data. -/
noncomputable def closedEmbeddingTrianglehDataOfTargetIsoRealizationW784
    (data : MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784) :
    MetrizableClosedEmbeddingTrianglehRealizationHomotopyObjectBranchDataW783
    where
  comparisonIso := data.comparisonIso
  trianglehRealization :=
    trianglehRealizationOfTargetIsoRealizationW784 data.targetIsoRealization
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W784 closed-map product evidence through target-isomorphism realization data. -/
noncomputable def productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (data : MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTrianglehRealizationRouteW783
    (closedMapTrianglehDataOfTargetIsoRealizationW784 data)

/-- W784 closed-embedding product evidence through target-isomorphism realization data. -/
noncomputable def productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (data : MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTrianglehRealizationRouteW783
    (closedEmbeddingTrianglehDataOfTargetIsoRealizationW784 data)

/-- W784 input names after replacing W783's strict triangleh realization premise. -/
def targetIsoRealizationTrianglehProductRouteInputNamesW784 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exact-acyclic homotopy-object triangleh target-isomorphism realization data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetIsoRealizationTrianglehProductRouteInputNamesW784_count :
    targetIsoRealizationTrianglehProductRouteInputNamesW784.length = 8 :=
  rfl

/-- Current checked W784 state. -/
structure MetrizableTargetIsoRealizationTrianglehRouteStateW784 : Type where
  seed : String
  declarations : List String
  transportResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W784 state for the target-isomorphism realization route. -/
def currentMetrizableTargetIsoRealizationTrianglehRouteStateW784 :
    MetrizableTargetIsoRealizationTrianglehRouteStateW784
    where
  seed := "w784-target-iso-realization-triangleh-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784",
      "trianglehRealizationOfTargetIsoRealizationW784",
      "MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784",
      "MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784",
      "closedMapTrianglehDataOfTargetIsoRealizationW784",
      "closedEmbeddingTrianglehDataOfTargetIsoRealizationW784",
      "productEvidence_of_closedMapTargetIsoRealizationRouteW784",
      "productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784",
      "targetIsoRealizationTrianglehProductRouteInputNamesW784",
      "targetIsoRealizationTrianglehProductRouteInputNamesW784_count"]
  transportResult :=
    "proved: exact-acyclic target-isomorphism realization supplies W783's triangleh input"
  closedMapResult :=
    "proved: closed-map target-isomorphism realization branch data feeds W783"
  closedEmbeddingResult :=
    "proved: closed-embedding target-isomorphism realization branch data feeds W783"
  replacedInputs :=
    ["exact-acyclic homotopy-object triangleh iso13 realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target-isomorphism realization\
        data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW784TargetIsoRealizationRoute_productSuccess :
    (have state :=
      currentMetrizableTargetIsoRealizationTrianglehRouteStateW784;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
