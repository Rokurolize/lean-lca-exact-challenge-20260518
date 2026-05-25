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
      "directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777",
      "directRightLcaLimitOpClosureNormalizedClosedRangeProductRouteInputNamesW777_count"]
  directRightLcaResult :=
    "proved: direct left/algebraic plus pure LCA right-side fields supply the\
      W776 WPP exact-acyclic limit-closure field"
  closedMapResult :=
    "proved: closed-map W735 branch data plus direct-right-LCA limit/op closure\
      feed W776"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus direct-right-LCA limit/op\
      closure feed W776"
  replacedInputs :=
    ["opaque WPP exact-acyclic limit-closure field"]
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
