import LeanLCAExactChallenge.Derived.DirectRightLcaLimitOpClosureNormalizedClosedRangeProductRoute

/-!
W1600 feeds W777 using the direct WPP limit-comparison theorem, removing the
explicit mapping-cone comparison field from the direct-right-LCA/WPP-op-closure
branch records.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1600 closed-map branch data using direct comparison, direct-right-LCA limit
fields, and WPP-op exact-acyclic colimit closure.
-/
structure MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W1600 closed-embedding branch data using direct comparison, direct-right-LCA
limit fields, and WPP-op exact-acyclic colimit closure.
-/
structure
    MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W1600 records that W551 supplies the WPP limit comparison input directly. -/
theorem limitComparisonOfDirectComparisonRightLcaOpClosureW1600 :
    MetrizableWppLimitComparisonInput :=
  metrizableWppLimitComparisonInput_direct

/-- W1600 closed-map branch converted to W777 data. -/
noncomputable def closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableClosedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := limitComparisonOfDirectComparisonRightLcaOpClosureW1600
  rightOpenLca := data.rightOpenLca
  rightSurjectiveLca := data.rightSurjectiveLca
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1600 closed-embedding branch converted to W777 data. -/
noncomputable def closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableClosedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeBranchDataW777
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := limitComparisonOfDirectComparisonRightLcaOpClosureW1600
  rightOpenLca := data.rightOpenLca
  rightSurjectiveLca := data.rightSurjectiveLca
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1600 closed-map product evidence through direct-comparison WPP-op data. -/
noncomputable def productEvidence_of_closedMapDirectComparisonRightLcaOpClosureRouteW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapDirectRightLcaLimitOpClosureNormalizedClosedRangeRouteW777
    (closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/--
W1600 closed-embedding product evidence through direct-comparison WPP-op data.
-/
noncomputable def
    productEvidence_of_closedEmbeddingDirectComparisonRightLcaOpClosureRouteW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingDirectRightLcaLimitOpClosureNormalizedClosedRangeRouteW777
    (closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapDirectRightLcaW777
    (closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/--
W1600 closed-embedding branch converted to the W769 stable-data surface.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingDirectRightLcaW777
    (closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapDirectRightLcaW777
    (closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingDirectRightLcaW777
    (closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapDirectRightLcaW777
    (closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/--
W1600 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingDirectRightLcaW777
    (closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapDirectComparisonRightLcaOpClosureStableBoundaryW1600
    (data : MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapDirectRightLcaStableBoundaryW777
    (closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/--
W1600 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingDirectComparisonRightLcaOpClosureStableBoundaryW1600
    (data :
      MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingDirectRightLcaStableBoundaryW777
    (closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600 data)

/-- W1600 input names after W551 supplies the WPP limit comparison input. -/
def directComparisonRightLcaOpClosureProductRouteInputNamesW1600 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem directComparisonRightLcaOpClosureProductRouteInputNamesW1600_count :
    directComparisonRightLcaOpClosureProductRouteInputNamesW1600.length = 7 :=
  rfl

/-- Current checked W1600 state for direct-comparison WPP-op routes. -/
structure MetrizableDirectComparisonRightLcaOpClosureProductRouteStateW1600 :
    Type where
  seed : String
  declarations : List String
  directComparisonResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W1600 state. -/
def currentMetrizableDirectComparisonRightLcaOpClosureProductRouteSupportStateW1600 :
    MetrizableDirectComparisonRightLcaOpClosureProductRouteStateW1600
    where
  seed := "w1600-direct-comparison-right-lca-op-closure-normalized-closed-range-route"
  declarations :=
    ["MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600",
      "MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600",
      "limitComparisonOfDirectComparisonRightLcaOpClosureW1600",
      "closedMapDirectRightLcaOpClosureDataOfDirectComparisonW1600",
      "closedEmbeddingDirectRightLcaOpClosureDataOfDirectComparisonW1600",
      "productEvidence_of_closedMapDirectComparisonRightLcaOpClosureRouteW1600",
      "productEvidence_of_closedEmbeddingDirectComparisonRightLcaOpClosureRouteW1600",
      "directFiniteShapeStableDataOfClosedMapDirectComparisonRightLcaOpClosureW1600",
      "directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600",
      "stableBoundaryInputsOfClosedMapDirectComparisonRightLcaOpClosureW1600",
      "stableBoundaryInputsOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600",
      "acceptedStableOfClosedMapDirectComparisonRightLcaOpClosureW1600",
      "acceptedStableOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600",
      "boundedDerivedOfClosedMapDirectComparisonRightLcaOpClosureStableBoundaryW1600",
      "boundedDerivedOfClosedEmbeddingDirectComparisonRightLcaOpClosureStableBoundaryW1600",
      "directComparisonRightLcaOpClosureProductRouteInputNamesW1600",
      "directComparisonRightLcaOpClosureProductRouteInputNamesW1600_count"]
  directComparisonResult :=
    "proved: W551 supplies the W777 WPP limit-comparison field directly"
  stableBoundaryResult :=
    "proved: W1600 direct-comparison right-LCA/WPP-op-closure branches pass the\
      W777/W776/W775/W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus direct-comparison right-LCA\
      WPP-op closure feed W777 without a mapping-cone comparison field"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus direct-comparison right-LCA\
      WPP-op closure feed W777 without a mapping-cone comparison field"
  replacedInputs :=
    ["mapping-cone WPP limit comparison field",
      "separate W777 direct-right-LCA WPP-op-closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP limit right-open pure LCA certificate",
      "construct WPP limit right-surjectivity pure LCA certificate",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1600DirectComparisonRightLcaOpClosureRoute_productSuccess :
    (let state :=
      currentMetrizableDirectComparisonRightLcaOpClosureProductRouteSupportStateW1600;
    state.productSuccessClaimed) =
        false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
