import LeanLCAExactChallenge.Derived.DirectFiniteShapeProductRoute

/-!
W770 reuses the W721 localized-right-adjoint data already carried by each W735
branch input in the W769 direct finite-shape product route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W770 closed-map branch data with stable localized data supplied by W735. -/
structure MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770 :
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
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W770 closed-embedding branch data with stable localized data supplied by W735. -/
structure
    MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770 :
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
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W770 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapBranchLocalizedW770
    (data : MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  directSource := data.directSource
  kernelCokernelTopologyData := data.kernelCokernelTopologyData
  localizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.exactInputs.localizedRightAdjointData
  directLocalization := data.directLocalization

/-- W770 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingBranchLocalizedW770
    (data :
      MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  directSource := data.directSource
  kernelCokernelTopologyData := data.kernelCokernelTopologyData
  localizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.exactInputs.localizedRightAdjointData
  directLocalization := data.directLocalization

/-- W770 closed-map branch stable certificate is ready through W769. -/
theorem stableCertificateOfClosedMapBranchLocalizedDirectFiniteShapeRouteW770_ready
    (data : MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
        (directFiniteShapeStableDataOfClosedMapBranchLocalizedW770 data))).ready :=
  stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready
    (directFiniteShapeStableDataOfClosedMapBranchLocalizedW770 data)

/-- W770 closed-embedding branch stable certificate is ready through W769. -/
theorem
    stableCertificateOfClosedEmbeddingBranchLocalizedDirectFiniteShapeRouteW770_ready
    (data :
      MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
        (directFiniteShapeStableDataOfClosedEmbeddingBranchLocalizedW770 data))).ready :=
  stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready
    (directFiniteShapeStableDataOfClosedEmbeddingBranchLocalizedW770 data)

/-- W770 closed-map product evidence reuses W735's localized-right-adjoint data. -/
noncomputable def
    productEvidence_of_closedMapBranchLocalizedDirectFiniteShapeRouteW770
    (data : MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapLeftRightComparisonDirectFiniteShapeRouteW769
    data.exactInputs
    (directFiniteShapeStableDataOfClosedMapBranchLocalizedW770 data)

/-- W770 closed-embedding product evidence reuses W735's localized data. -/
noncomputable def
    productEvidence_of_closedEmbeddingBranchLocalizedDirectFiniteShapeRouteW770
    (data :
      MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingLeftRightComparisonDirectFiniteShapeRouteW769
    data.exactInputs
    (directFiniteShapeStableDataOfClosedEmbeddingBranchLocalizedW770 data)

/-- W770 input names after stable localization is reused from the W735 branch. -/
def branchLocalizedDirectFiniteShapeProductRouteInputNamesW770 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W721 localized data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "direct localization triangulated source data"]

theorem branchLocalizedDirectFiniteShapeProductRouteInputNamesW770_count :
    branchLocalizedDirectFiniteShapeProductRouteInputNamesW770.length =
      6 :=
  rfl

/-- Current checked W770 state. -/
structure MetrizableBranchLocalizedDirectFiniteShapeProductRouteStateW770 :
    Type where
  seed : String
  declarations : List String
  localizedReuseResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W770 state for branch-localized direct finite-shape routes. -/
def currentMetrizableBranchLocalizedDirectFiniteShapeProductRouteSupportStateW770 :
    MetrizableBranchLocalizedDirectFiniteShapeProductRouteStateW770
    where
  seed := "w770-branch-localized-direct-finite-shape-product-route"
  declarations :=
    ["MetrizableClosedMapLeftRightComparisonDirectFiniteShapeBranchDataW770",
      "MetrizableClosedEmbeddingLeftRightComparisonDirectFiniteShapeBranchDataW770",
      "directFiniteShapeStableDataOfClosedMapBranchLocalizedW770",
      "directFiniteShapeStableDataOfClosedEmbeddingBranchLocalizedW770",
      "stableCertificateOfClosedMapBranchLocalizedDirectFiniteShapeRouteW770_ready",
      "stableCertificateOfClosedEmbeddingBranchLocalizedDirectFiniteShapeRouteW770_ready",
      "productEvidence_of_closedMapBranchLocalizedDirectFiniteShapeRouteW770",
      "productEvidence_of_closedEmbeddingBranchLocalizedDirectFiniteShapeRouteW770",
      "branchLocalizedDirectFiniteShapeProductRouteInputNamesW770",
      "branchLocalizedDirectFiniteShapeProductRouteInputNamesW770_count"]
  localizedReuseResult :=
    "proved: W735 branch-localized W721 data supplies the stable branch's\
      localized-right-adjoint input"
  closedMapResult :=
    "proved: closed-map W735 branch data feeds the W769 direct finite-shape\
      product evidence route"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data feeds the W769 direct finite-shape\
      product evidence route"
  replacedInputs :=
    ["separate stable-branch bounded homotopy localized-right-adjoint input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct direct finite-shape WPP source data",
      "construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "construct direct localization triangulated source data"]
  productSuccessClaimed := false

theorem
    currentMetrizableBranchLocalizedDirectFiniteShapeProductRouteStateW770_productSuccess :
    (let state :=
      currentMetrizableBranchLocalizedDirectFiniteShapeProductRouteSupportStateW770;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
