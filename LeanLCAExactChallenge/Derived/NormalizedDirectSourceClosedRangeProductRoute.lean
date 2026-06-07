import LeanLCAExactChallenge.Derived.SourceTriangulationClosedRangeDirectFiniteShapeProductRoute

/-!
W774 reuses the W719 normalized fixed-target data carried by each W735 branch
input to rebuild the W653 direct finite-shape source required by W773.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W774 closed-map branch data using W735 normalized fixed-target data. -/
structure MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W774 closed-embedding branch data using W735 normalized fixed-target data. -/
structure MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W774 closed-map normalized fixed-target inputs projected from W735 data. -/
def normalizedFixedTargetInputsOfClosedMapW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs
    where
  normalized :=
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData
  target_uniq :=
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData
  model_uniq :=
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData

/-- W774 closed-embedding normalized fixed-target inputs projected from W735 data. -/
def normalizedFixedTargetInputsOfClosedEmbeddingW774
    (data : MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs
    where
  normalized :=
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData
  target_uniq :=
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData
  model_uniq :=
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
      data.exactInputs.normalizedFixedTargetData

/-- W774 rebuilds the closed-map W653 direct source from normalized W735 data. -/
noncomputable def directSourceOfClosedMapNormalizedW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
    where
  finiteShapeInputs :=
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_normalized
      { limitStability := data.limitStability
        colimitStability := data.colimitStability
        normalizedInputs := normalizedFixedTargetInputsOfClosedMapW774 data }

/-- W774 rebuilds the closed-embedding W653 direct source from normalized W735 data. -/
noncomputable def directSourceOfClosedEmbeddingNormalizedW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
    where
  finiteShapeInputs :=
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_normalized
      { limitStability := data.limitStability
        colimitStability := data.colimitStability
        normalizedInputs := normalizedFixedTargetInputsOfClosedEmbeddingW774 data }

/-- W774 closed-map branch converted to W773 data. -/
noncomputable def closedMapSourceTriangulationDataOfNormalizedW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableClosedMapSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := directSourceOfClosedMapNormalizedW774 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W774 closed-embedding branch converted to W773 data. -/
noncomputable def closedEmbeddingSourceTriangulationDataOfNormalizedW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableClosedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeBranchDataW773
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  directSource := directSourceOfClosedEmbeddingNormalizedW774 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W774 closed-map product evidence through normalized direct-source data. -/
noncomputable def productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapSourceTriangulationClosedRangeDirectFiniteShapeRouteW773
    (closedMapSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-embedding product evidence through normalized direct-source data. -/
noncomputable def
    productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingSourceTriangulationClosedRangeDirectFiniteShapeRouteW773
    (closedEmbeddingSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapSourceTriangulationClosedRangeW773
    (closedMapSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingSourceTriangulationClosedRangeW773
    (closedEmbeddingSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapSourceTriangulationClosedRangeW773
    (closedMapSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingSourceTriangulationClosedRangeW773
    (closedEmbeddingSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def
    acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfClosedMapSourceTriangulationClosedRangeW773
    (closedMapSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def
    acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfClosedEmbeddingSourceTriangulationClosedRangeW773
    (closedEmbeddingSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774
    (data : MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSourceTriangulationClosedRangeStableBoundaryW773
    (closedMapSourceTriangulationDataOfNormalizedW774 data)

/-- W774 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774
    (data :
      MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingSourceTriangulationClosedRangeStableBoundaryW773
    (closedEmbeddingSourceTriangulationDataOfNormalizedW774 data)

/-- W774 input names after W735 normalized data supplies direct-source localization. -/
def normalizedDirectSourceClosedRangeProductRouteInputNamesW774 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W719 normalized\
      fixed-target data and W722 source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP limit stability for WalkingParallelPair",
    "WPP colimit stability for WalkingParallelPair",
    "W696 closed-range endpoint topology data"]

theorem normalizedDirectSourceClosedRangeProductRouteInputNamesW774_count :
    normalizedDirectSourceClosedRangeProductRouteInputNamesW774.length = 6 :=
  rfl

/-- Current checked W774 state. -/
structure MetrizableNormalizedDirectSourceClosedRangeProductRouteStateW774 :
    Type where
  seed : String
  declarations : List String
  normalizedSourceResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W774 state for normalized direct-source closed-range routes. -/
def currentMetrizableNormalizedDirectSourceClosedRangeProductRouteSupportStateW774 :
    MetrizableNormalizedDirectSourceClosedRangeProductRouteStateW774
    where
  seed := "w774-normalized-direct-source-closed-range-product-route"
  declarations :=
    ["MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774",
      "MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774",
      "normalizedFixedTargetInputsOfClosedMapW774",
      "normalizedFixedTargetInputsOfClosedEmbeddingW774",
      "directSourceOfClosedMapNormalizedW774",
      "directSourceOfClosedEmbeddingNormalizedW774",
      "closedMapSourceTriangulationDataOfNormalizedW774",
      "closedEmbeddingSourceTriangulationDataOfNormalizedW774",
      "productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774",
      "productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774",
      "directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774",
      "directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774",
      "stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774",
      "stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774",
      "acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774",
      "acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774",
      "boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774",
      "boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774",
      "normalizedDirectSourceClosedRangeProductRouteInputNamesW774",
      "normalizedDirectSourceClosedRangeProductRouteInputNamesW774_count"]
  normalizedSourceResult :=
    "proved: W735 normalized fixed-target data supplies the localization\
      portion of the W653 direct finite-shape source"
  stableBoundaryResult :=
    "proved: W774 normalized direct-source closed-range branches pass the W773\
      and W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus WPP stability and W696 topology\
      feed the W773 route"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus WPP stability and W696\
      topology feed the W773 route"
  replacedInputs :=
    ["separate MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653 field",
      "separate W773 direct finite-shape stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP limit stability for WalkingParallelPair",
      "construct WPP colimit stability for WalkingParallelPair",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW774NormalizedDirectSourceClosedRangeRoute_productSuccess :
    (let state :=
      currentMetrizableNormalizedDirectSourceClosedRangeProductRouteSupportStateW774;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
