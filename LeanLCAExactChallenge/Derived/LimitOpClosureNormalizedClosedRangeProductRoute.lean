import LeanLCAExactChallenge.Derived.OpClosureNormalizedDirectSourceClosedRangeProductRoute

/-!
W776 feeds direct WPP limit comparison and exact-acyclic limit closure into the
W775 WPP-op-closure normalized closed-range route, replacing the abstract WPP
limit-stability field.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W776 closed-map branch data using direct WPP limit closure and WPP-op closure. -/
structure MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W776 closed-embedding branch data using direct WPP limit closure and WPP-op closure. -/
structure MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W776 derives closed-map WPP limit stability from comparison and limit closure. -/
theorem limitStabilityOfClosedMapLimitOpClosureW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
    data.limitComparison
    data.limitClosure

/-- W776 derives closed-embedding WPP limit stability from comparison and limit closure. -/
theorem limitStabilityOfClosedEmbeddingLimitOpClosureW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
    data.limitComparison
    data.limitClosure

/-- W776 closed-map branch converted to W775 data. -/
noncomputable def closedMapOpClosureDataOfLimitClosureW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedMapLimitOpClosureW776 data
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W776 closed-embedding branch converted to W775 data. -/
noncomputable def closedEmbeddingOpClosureDataOfLimitClosureW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedEmbeddingLimitOpClosureW776 data
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W776 closed-map product evidence through direct WPP limit closure and WPP-op closure. -/
noncomputable def productEvidence_of_closedMapLimitOpClosureNormalizedClosedRangeRouteW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapOpClosureNormalizedClosedRangeRouteW775
    (closedMapOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-embedding product evidence through direct WPP limit closure and WPP-op closure. -/
noncomputable def
    productEvidence_of_closedEmbeddingLimitOpClosureNormalizedClosedRangeRouteW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingOpClosureNormalizedClosedRangeRouteW775
    (closedEmbeddingOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def
    acceptedStableOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapLimitOpClosureNormalizedClosedRangeStableBoundaryW776
    (data : MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapOpClosureNormalizedClosedRangeStableBoundaryW775
    (closedMapOpClosureDataOfLimitClosureW776 data)

/-- W776 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeStableBoundaryW776
    (data :
      MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingOpClosureNormalizedClosedRangeStableBoundaryW775
    (closedEmbeddingOpClosureDataOfLimitClosureW776 data)

/-- W776 input names after WPP limit closure supplies WPP limit stability. -/
def limitOpClosureNormalizedClosedRangeProductRouteInputNamesW776 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "mapping-cone WPP limit comparison",
    "WPP exact-acyclic limit closure",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem limitOpClosureNormalizedClosedRangeProductRouteInputNamesW776_count :
    limitOpClosureNormalizedClosedRangeProductRouteInputNamesW776.length = 7 :=
  rfl

/-- Current checked W776 state. -/
structure MetrizableLimitOpClosureNormalizedClosedRangeProductRouteStateW776 :
    Type where
  seed : String
  declarations : List String
  limitClosureResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W776 state for direct-limit/WPP-op closed-range routes. -/
def currentMetrizableLimitOpClosureNormalizedClosedRangeProductRouteSupportStateW776 :
    MetrizableLimitOpClosureNormalizedClosedRangeProductRouteStateW776
    where
  seed := "w776-limit-op-closure-normalized-closed-range-product-route"
  declarations :=
    ["MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776",
      "MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776",
      "limitStabilityOfClosedMapLimitOpClosureW776",
      "limitStabilityOfClosedEmbeddingLimitOpClosureW776",
      "closedMapOpClosureDataOfLimitClosureW776",
      "closedEmbeddingOpClosureDataOfLimitClosureW776",
      "productEvidence_of_closedMapLimitOpClosureNormalizedClosedRangeRouteW776",
      "productEvidence_of_closedEmbeddingLimitOpClosureNormalizedClosedRangeRouteW776",
      "directFiniteShapeStableDataOfClosedMapLimitOpClosureNormalizedClosedRangeW776",
      "directFiniteShapeStableDataOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776",
      "stableBoundaryInputsOfClosedMapLimitOpClosureNormalizedClosedRangeW776",
      "stableBoundaryInputsOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776",
      "acceptedStableOfClosedMapLimitOpClosureNormalizedClosedRangeW776",
      "acceptedStableOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776",
      "boundedDerivedOfClosedMapLimitOpClosureNormalizedClosedRangeStableBoundaryW776",
      "boundedDerivedOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeStableBoundaryW776",
      "limitOpClosureNormalizedClosedRangeProductRouteInputNamesW776",
      "limitOpClosureNormalizedClosedRangeProductRouteInputNamesW776_count"]
  limitClosureResult :=
    "proved: direct WPP limit comparison plus exact-acyclic limit closure\
      supplies the W775 limit-stability field"
  stableBoundaryResult :=
    "proved: W776 limit/op-closure normalized closed-range branches pass the\
      W775/W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus WPP limit/op closure feed W775"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus WPP limit/op closure feed W775"
  replacedInputs :=
    ["abstract WPP limit-stability field for WalkingParallelPair",
      "separate W775 WPP-op-closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct mapping-cone WPP limit comparison",
      "construct WPP exact-acyclic limit closure",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW776LimitOpClosureNormalizedClosedRangeRoute_productSuccess :
    (let state :=
      currentMetrizableLimitOpClosureNormalizedClosedRangeProductRouteSupportStateW776;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
