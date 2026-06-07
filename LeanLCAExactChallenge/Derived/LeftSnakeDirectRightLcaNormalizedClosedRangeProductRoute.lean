import LeanLCAExactChallenge.Derived.DirectRightLcaLimitOpClosureNormalizedClosedRangeProductRoute

/-!
W778 feeds the direct-right-LCA WPP limit route and WPP-op left/Snake colimit
route into W774, replacing the WPP-op exact-acyclic colimit-closure field with
lower-level colimit certificates.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open DirectWppOpColimitFiniteShapeTransfer

namespace Dbounded

/-- W778 closed-map branch data using direct-right-LCA limits and WPP-op left/Snake colimits. -/
structure MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  limitComparison : MetrizableWppLimitComparisonInput
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W778 closed-embedding branch data using direct-right-LCA limits and WPP-op
left/Snake colimits.
-/
structure MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  limitComparison : MetrizableWppLimitComparisonInput
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W778 derives closed-map WPP limit stability from direct-right-LCA fields. -/
theorem limitStabilityOfClosedMapLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraicRightLca
    data.limitComparison
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/-- W778 derives closed-embedding WPP limit stability from direct-right-LCA fields. -/
theorem limitStabilityOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraicRightLca
    data.limitComparison
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/-- W778 derives closed-map WPP colimit stability from WPP-op left/Snake fields. -/
theorem colimitStabilityOfClosedMapLeftSnakeW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    data.opLeftClosed
    data.opSnake

/-- W778 derives closed-embedding WPP colimit stability from WPP-op left/Snake fields. -/
theorem colimitStabilityOfClosedEmbeddingLeftSnakeW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    data.opLeftClosed
    data.opSnake

/-- W778 closed-map branch converted to W774 data. -/
noncomputable def closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedMapLeftSnakeDirectRightLcaW778 data
  colimitStability := colimitStabilityOfClosedMapLeftSnakeW778 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W778 closed-embedding branch converted to W774 data. -/
noncomputable def closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedEmbeddingLeftSnakeDirectRightLcaW778 data
  colimitStability := colimitStabilityOfClosedEmbeddingLeftSnakeW778 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W778 closed-map product evidence through direct-right-LCA limit and left/Snake colimit data. -/
noncomputable def productEvidence_of_closedMapLeftSnakeDirectRightLcaRouteW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/--
W778 closed-embedding product evidence through direct-right-LCA limit and
left/Snake colimit data.
-/
noncomputable def productEvidence_of_closedEmbeddingLeftSnakeDirectRightLcaRouteW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapLeftSnakeDirectRightLcaStableBoundaryW778
    (data : MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedEmbeddingLeftSnakeDirectRightLcaStableBoundaryW778
    (data : MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778 data)

/-- W778 input names after WPP-op left/Snake supplies colimit stability. -/
def leftSnakeDirectRightLcaProductRouteInputNamesW778 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "mapping-cone WPP limit comparison",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "W696 closed-range endpoint topology data"]

theorem leftSnakeDirectRightLcaProductRouteInputNamesW778_count :
    leftSnakeDirectRightLcaProductRouteInputNamesW778.length = 9 :=
  rfl

/-- Current checked W778 state. -/
structure MetrizableLeftSnakeDirectRightLcaProductRouteStateW778 :
    Type where
  seed : String
  declarations : List String
  limitResult : String
  colimitResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W778 state for direct-right-LCA plus left/Snake routes. -/
def currentMetrizableLeftSnakeDirectRightLcaProductRouteSupportStateW778 :
    MetrizableLeftSnakeDirectRightLcaProductRouteStateW778
    where
  seed := "w778-left-snake-direct-right-lca-normalized-closed-range-route"
  declarations :=
    ["MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778",
      "MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778",
      "limitStabilityOfClosedMapLeftSnakeDirectRightLcaW778",
      "limitStabilityOfClosedEmbeddingLeftSnakeDirectRightLcaW778",
      "colimitStabilityOfClosedMapLeftSnakeW778",
      "colimitStabilityOfClosedEmbeddingLeftSnakeW778",
      "closedMapNormalizedDataOfLeftSnakeDirectRightLcaW778",
      "closedEmbeddingNormalizedDataOfLeftSnakeDirectRightLcaW778",
      "productEvidence_of_closedMapLeftSnakeDirectRightLcaRouteW778",
      "productEvidence_of_closedEmbeddingLeftSnakeDirectRightLcaRouteW778",
      "directFiniteShapeStableDataOfClosedMapLeftSnakeDirectRightLcaW778",
      "directFiniteShapeStableDataOfClosedEmbeddingLeftSnakeDirectRightLcaW778",
      "stableBoundaryInputsOfClosedMapLeftSnakeDirectRightLcaW778",
      "stableBoundaryInputsOfClosedEmbeddingLeftSnakeDirectRightLcaW778",
      "acceptedStableOfClosedMapLeftSnakeDirectRightLcaW778",
      "acceptedStableOfClosedEmbeddingLeftSnakeDirectRightLcaW778",
      "boundedDerivedOfClosedMapLeftSnakeDirectRightLcaStableBoundaryW778",
      "boundedDerivedOfClosedEmbeddingLeftSnakeDirectRightLcaStableBoundaryW778",
      "leftSnakeDirectRightLcaProductRouteInputNamesW778",
      "leftSnakeDirectRightLcaProductRouteInputNamesW778_count"]
  limitResult :=
    "proved: direct-right-LCA fields supply the W774 WPP limit-stability field"
  colimitResult :=
    "proved: WPP-op left/Snake fields supply the W774 colimit-stability field"
  stableBoundaryResult :=
    "proved: W778 left/Snake direct-right-LCA normalized closed-range branches\
      pass the W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus direct-right-LCA left/Snake data\
      feed W774"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus direct-right-LCA left/Snake\
      data feed W774"
  replacedInputs :=
    ["opaque WPP exact-acyclic limit-closure field",
      "WPP-op exact-acyclic colimit-closure field",
      "separate W774 normalized direct-source stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct mapping-cone WPP limit comparison",
      "construct WPP limit right-open pure LCA certificate",
      "construct WPP limit right-surjectivity pure LCA certificate",
      "construct WPP-op colimit left closed-embedding certificate",
      "construct WPP-op AddCommGrp SnakeInput cokernel-row certificate",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW778LeftSnakeDirectRightLcaRoute_productSuccess :
    currentMetrizableLeftSnakeDirectRightLcaProductRouteSupportStateW778.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
