import LeanLCAExactChallenge.Derived.LimitOpClosureNormalizedClosedRangeProductRoute

/-!
W777 feeds the direct-left/algebraic-right-LCA WPP limit-closure route into
the W776 limit/op-closure normalized closed-range route, replacing the opaque
WPP exact-acyclic limit-closure field.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W777 closed-map branch data using direct-left/algebraic right-LCA limit closure. -/
structure MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777 :
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
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W777 closed-embedding branch data using direct-left/algebraic right-LCA limit closure. -/
structure
    MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777 :
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
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W777 derives closed-map WPP limit closure from direct-left/algebraic right-LCA fields. -/
theorem limitClosureOfClosedMapDirectRightLcaW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_directLeftAlgebraicRightLca
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/-- W777 derives closed-embedding WPP limit closure from direct-left/algebraic right-LCA fields. -/
theorem limitClosureOfClosedEmbeddingDirectRightLcaW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_directLeftAlgebraicRightLca
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/-- W777 closed-map branch converted to W776 data. -/
noncomputable def closedMapLimitOpClosureDataOfDirectRightLcaW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableClosedMapLimitOpClosureNormalizedClosedRangeBranchDataW776 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := data.limitComparison
  limitClosure := limitClosureOfClosedMapDirectRightLcaW777 data
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W777 closed-embedding branch converted to W776 data. -/
noncomputable def closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableClosedEmbeddingLimitOpClosureNormalizedClosedRangeBranchDataW776 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := data.limitComparison
  limitClosure := limitClosureOfClosedEmbeddingDirectRightLcaW777 data
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W777 closed-map product evidence through direct-right-LCA limit/op-closure data. -/
noncomputable def
    productEvidence_of_closedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeRouteW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapLimitOpClosureNormalizedClosedRangeRouteW776
    (closedMapLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-embedding product evidence through direct-right-LCA limit/op-closure data. -/
noncomputable def
    productEvidence_of_closedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeRouteW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingLimitOpClosureNormalizedClosedRangeRouteW776
    (closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapDirectRightLcaW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (closedMapLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingDirectRightLcaW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapDirectRightLcaW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (closedMapLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingDirectRightLcaW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapDirectRightLcaW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapLimitOpClosureNormalizedClosedRangeW776
    (closedMapLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedEmbeddingDirectRightLcaW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeW776
    (closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapDirectRightLcaStableBoundaryW777
    (data :
      MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapLimitOpClosureNormalizedClosedRangeStableBoundaryW776
    (closedMapLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedEmbeddingDirectRightLcaStableBoundaryW777
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingLimitOpClosureNormalizedClosedRangeStableBoundaryW776
    (closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777 data)

/-- W777 input names after direct-left/algebraic right-LCA fields supply WPP limit closure. -/
def directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "mapping-cone WPP limit comparison",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777_count :
    directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777.length =
      8 :=
  rfl

/-- Current checked W777 state. -/
structure MetrizableDirectRightLcaLimitOpClosureNormalizedClosedRangeProductRouteStateW777 :
    Type where
  seed : String
  declarations : List String
  directRightLcaResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W777 state for direct-right-LCA limit/op-closure routes. -/
def currentMetrizableDirectRightLcaLimitOpClosureNormalizedClosedRangeProductRouteSupportStateW777 :
    MetrizableDirectRightLcaLimitOpClosureNormalizedClosedRangeProductRouteStateW777
    where
  seed := "w777-direct-right-lca-limit-op-closure-normalized-closed-range-route"
  declarations :=
    ["MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777",
      "MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777",
      "limitClosureOfClosedMapDirectRightLcaW777",
      "limitClosureOfClosedEmbeddingDirectRightLcaW777",
      "closedMapLimitOpClosureDataOfDirectRightLcaW777",
      "closedEmbeddingLimitOpClosureDataOfDirectRightLcaW777",
      "productEvidence_of_closedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeRouteW777",
      "productEvidence_of_closedEmbeddingDirectRightLcaLimitOpClosureNormalized\
        ClosedRangeRouteW777",
      "directFiniteShapeStableDataOfClosedMapDirectRightLcaW777",
      "directFiniteShapeStableDataOfClosedEmbeddingDirectRightLcaW777",
      "stableBoundaryInputsOfClosedMapDirectRightLcaW777",
      "stableBoundaryInputsOfClosedEmbeddingDirectRightLcaW777",
      "acceptedStableOfClosedMapDirectRightLcaW777",
      "acceptedStableOfClosedEmbeddingDirectRightLcaW777",
      "boundedDerivedOfClosedMapDirectRightLcaStableBoundaryW777",
      "boundedDerivedOfClosedEmbeddingDirectRightLcaStableBoundaryW777",
      "directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777",
      "directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777_count"]
  directRightLcaResult :=
    "proved: direct left/algebraic plus pure LCA right-side fields supply the\
      W776 WPP exact-acyclic limit-closure field"
  stableBoundaryResult :=
    "proved: W777 direct-right-LCA limit/op-closure normalized closed-range\
      branches pass the W776/W775/W774/W773/W769 canonical stable-boundary\
      accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus direct-right-LCA limit/op closure\
      feed W776"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus direct-right-LCA limit/op\
      closure feed W776"
  replacedInputs :=
    ["opaque WPP exact-acyclic limit-closure field",
      "separate W776 limit/op-closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct mapping-cone WPP limit comparison",
      "construct WPP limit right-open pure LCA certificate",
      "construct WPP limit right-surjectivity pure LCA certificate",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW777DirectRightLcaLimitOpClosureNormalizedClosedRangeRoute_productSuccess :
    (let state :=
  currentMetrizableDirectRightLcaLimitOpClosureNormalizedClosedRangeProductRouteSupportStateW777;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
