import LeanLCAExactChallenge.Derived.BranchLocalizedDirectFiniteShapeProductRoute

/-!
W771 feeds the W695 closure-kernel endpoint-topology adapter into the W770
branch-localized direct finite-shape product route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W771 closed-map branch data using W695 closure-kernel endpoint topology. -/
structure MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771 :
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
  closureKernelEndpointTopology :
    MetrizableExactAtClosureKernelEndpointTopologyInputsW694
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W771 closed-embedding branch data using W695 closure-kernel endpoint topology. -/
structure MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771 :
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
  closureKernelEndpointTopology :
    MetrizableExactAtClosureKernelEndpointTopologyInputsW694
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W771 extracts kernel/cokernel topology from closed-map closure-kernel data. -/
noncomputable def kernelCokernelTopologyOfClosedMapClosureKernelW771
    (data : MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs :=
  metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closureKernelEndpointTopologyW695
    data.closureKernelEndpointTopology

/-- W771 extracts kernel/cokernel topology from closed-embedding closure data. -/
noncomputable def kernelCokernelTopologyOfClosedEmbeddingClosureKernelW771
    (data : MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs :=
  metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closureKernelEndpointTopologyW695
    data.closureKernelEndpointTopology

/-- W771 closed-map branch converted to W770 data. -/
noncomputable def closedMapBranchLocalizedDataOfClosureKernelW771
    (data : MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  kernelCokernelTopologyData :=
    kernelCokernelTopologyOfClosedMapClosureKernelW771 data
  directLocalization := data.directLocalization

/-- W771 closed-embedding branch converted to W770 data. -/
noncomputable def closedEmbeddingBranchLocalizedDataOfClosureKernelW771
    (data : MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := data.directSource
  kernelCokernelTopologyData :=
    kernelCokernelTopologyOfClosedEmbeddingClosureKernelW771 data
  directLocalization := data.directLocalization

/-- W771 closed-map product evidence through W770 and W695. -/
noncomputable def productEvidence_of_closedMapClosureKernelDirectFiniteShapeRouteW771
    (data : MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapBranchLocalizedDirectFiniteShapeRouteW770
    (closedMapBranchLocalizedDataOfClosureKernelW771 data)

/-- W771 closed-embedding product evidence through W770 and W695. -/
noncomputable def
    productEvidence_of_closedEmbeddingClosureKernelDirectFiniteShapeRouteW771
    (data : MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingBranchLocalizedDirectFiniteShapeRouteW770
    (closedEmbeddingBranchLocalizedDataOfClosureKernelW771 data)

/-- W771 input names after W695 supplies kernel/cokernel topology. -/
def closureKernelDirectFiniteShapeProductRouteInputNamesW771 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W721 localized data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "W694 closure-kernel endpoint topology data",
    "direct localization triangulated source data"]

theorem closureKernelDirectFiniteShapeProductRouteInputNamesW771_count :
    closureKernelDirectFiniteShapeProductRouteInputNamesW771.length =
      6 :=
  rfl

/-- Current checked W771 state. -/
structure MetrizableClosureKernelDirectFiniteShapeProductRouteStateW771 :
    Type where
  seed : String
  declarations : List String
  topologyProjectionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W771 state for closure-kernel direct finite-shape routes. -/
def currentMetrizableClosureKernelDirectFiniteShapeProductRouteSupportStateW771 :
    MetrizableClosureKernelDirectFiniteShapeProductRouteStateW771
    where
  seed := "w771-closure-kernel-direct-finite-shape-product-route"
  declarations :=
    ["MetrizableClosedMapClosureKernelDirectFiniteShapeBranchDataW771",
      "MetrizableClosedEmbeddingClosureKernelDirectFiniteShapeBranchDataW771",
      "kernelCokernelTopologyOfClosedMapClosureKernelW771",
      "kernelCokernelTopologyOfClosedEmbeddingClosureKernelW771",
      "closedMapBranchLocalizedDataOfClosureKernelW771",
      "closedEmbeddingBranchLocalizedDataOfClosureKernelW771",
      "productEvidence_of_closedMapClosureKernelDirectFiniteShapeRouteW771",
      "productEvidence_of_closedEmbeddingClosureKernelDirectFiniteShapeRouteW771",
      "closureKernelDirectFiniteShapeProductRouteInputNamesW771",
      "closureKernelDirectFiniteShapeProductRouteInputNamesW771_count"]
  topologyProjectionResult :=
    "proved: W695 closure-kernel endpoint topology supplies the W770 kernel/cokernel topology input"
  closedMapResult :=
    "proved: closed-map W735 branch data plus W694 topology feed the W770 route"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus W694 topology feed the W770 route"
  replacedInputs :=
    ["direct MetrizableExactAtKernelCokernelConditionedTopologyInputs field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct direct finite-shape WPP source data",
      "construct W694 closure-kernel endpoint topology data",
      "construct direct localization triangulated source data"]
  productSuccessClaimed := false

theorem currentMetrizableClosureKernelDirectFiniteShapeProductRouteStateW771_productSuccess :
    (let state :=
      currentMetrizableClosureKernelDirectFiniteShapeProductRouteSupportStateW771;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
