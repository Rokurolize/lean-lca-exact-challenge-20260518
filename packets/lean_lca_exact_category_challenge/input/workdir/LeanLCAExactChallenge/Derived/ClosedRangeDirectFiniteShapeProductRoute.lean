import LeanLCAExactChallenge.Derived.ClosureKernelDirectFiniteShapeProductRoute

/-!
W772 feeds the W696 closed-range endpoint-topology adapter into the W771
closure-kernel direct finite-shape product route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W772 closed-map branch data using W696 closed-range endpoint topology. -/
structure MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772 :
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
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W772 closed-embedding branch data using W696 closed-range endpoint topology. -/
structure MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772 :
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
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W772 extracts W694 closure-kernel topology from closed-map W696 data. -/
noncomputable def closureKernelEndpointTopologyOfClosedMapClosedRangeW772
    (data : MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableExactAtClosureKernelEndpointTopologyInputsW694 :=
  metrizableExactAtClosureKernelEndpointTopologyInputs_of_closedRangeEndpointTopologyW696
    data.closedRangeEndpointTopology

/-- W772 extracts W694 closure-kernel topology from closed-embedding W696 data. -/
noncomputable def closureKernelEndpointTopologyOfClosedEmbeddingClosedRangeW772
    (data : MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableExactAtClosureKernelEndpointTopologyInputsW694 :=
  metrizableExactAtClosureKernelEndpointTopologyInputs_of_closedRangeEndpointTopologyW696
    data.closedRangeEndpointTopology

/-- W772 closed-map branch converted to W771 data. -/
noncomputable def closedMapClosureKernelDataOfClosedRangeW772
    (data : MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  closureKernelEndpointTopology :=
    closureKernelEndpointTopologyOfClosedMapClosedRangeW772 data
  directLocalization := data.directLocalization

/-- W772 closed-embedding branch converted to W771 data. -/
noncomputable def closedEmbeddingClosureKernelDataOfClosedRangeW772
    (data : MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  closureKernelEndpointTopology :=
    closureKernelEndpointTopologyOfClosedEmbeddingClosedRangeW772 data
  directLocalization := data.directLocalization

/-- W772 closed-map product evidence through W771 and W696. -/
noncomputable def productEvidence_of_closedMapClosedRangeDirectFiniteShapeRouteW772
    (data : MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapClosureKernelDirectFiniteShapeRouteW771
    (closedMapClosureKernelDataOfClosedRangeW772 data)

/-- W772 closed-embedding product evidence through W771 and W696. -/
noncomputable def productEvidence_of_closedEmbeddingClosedRangeDirectFiniteShapeRouteW772
    (data : MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingClosureKernelDirectFiniteShapeRouteW771
    (closedEmbeddingClosureKernelDataOfClosedRangeW772 data)

/-- W772 input names after W696 supplies closure-kernel endpoint topology. -/
def closedRangeDirectFiniteShapeProductRouteInputNamesW772 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W721 localized data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "W696 closed-range endpoint topology data",
    "direct localization triangulated source data"]

theorem closedRangeDirectFiniteShapeProductRouteInputNamesW772_count :
    closedRangeDirectFiniteShapeProductRouteInputNamesW772.length =
      6 :=
  rfl

/-- Current checked W772 state. -/
structure MetrizableClosedRangeDirectFiniteShapeProductRouteStateW772 :
    Type where
  seed : String
  declarations : List String
  topologyProjectionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W772 state for closed-range direct finite-shape routes. -/
def currentMetrizableClosedRangeDirectFiniteShapeProductRouteSupportStateW772 :
    MetrizableClosedRangeDirectFiniteShapeProductRouteStateW772
    where
  seed := "w772-closed-range-direct-finite-shape-product-route"
  declarations :=
    ["MetrizableClosedMapClosedRangeDirectFiniteShapeBranchDataW772",
      "MetrizableClosedEmbeddingClosedRangeDirectFiniteShapeBranchDataW772",
      "closureKernelEndpointTopologyOfClosedMapClosedRangeW772",
      "closureKernelEndpointTopologyOfClosedEmbeddingClosedRangeW772",
      "closedMapClosureKernelDataOfClosedRangeW772",
      "closedEmbeddingClosureKernelDataOfClosedRangeW772",
      "productEvidence_of_closedMapClosedRangeDirectFiniteShapeRouteW772",
      "productEvidence_of_closedEmbeddingClosedRangeDirectFiniteShapeRouteW772",
      "closedRangeDirectFiniteShapeProductRouteInputNamesW772",
      "closedRangeDirectFiniteShapeProductRouteInputNamesW772_count"]
  topologyProjectionResult :=
    "proved: W696 closed-range endpoint topology supplies the W771 closure-kernel topology input"
  closedMapResult :=
    "proved: closed-map W735 branch data plus W696 topology feed the W771 route"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus W696 topology feed the W771 route"
  replacedInputs :=
    ["direct W694 closure-kernel endpoint-topology field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct direct finite-shape WPP source data",
      "construct W696 closed-range endpoint topology data",
      "construct direct localization triangulated source data"]
  productSuccessClaimed := false

theorem currentMetrizableClosedRangeDirectFiniteShapeProductRouteStateW772_productSuccess :
    (let state :=
      currentMetrizableClosedRangeDirectFiniteShapeProductRouteSupportStateW772;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
