import LeanLCAExactChallenge.Derived.LeftSnakeDirectRightLcaNormalizedClosedRangeProductRoute

/-!
W779 feeds W778 using the direct WPP limit-comparison theorem, removing the
explicit mapping-cone comparison field from the branch records.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W779 closed-map branch data using direct comparison, right-LCA limits, and
left/Snake colimits.
-/
structure MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779 :
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
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W779 closed-embedding branch data using direct comparison, right-LCA limits,
and left/Snake colimits.
-/
structure MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779 :
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
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W779 records that W551 supplies the WPP limit comparison input directly. -/
theorem limitComparisonOfDirectComparisonW779 :
    MetrizableWppLimitComparisonInput :=
  metrizableWppLimitComparisonInput_direct

/-- W779 closed-map branch converted to W778 data. -/
noncomputable def closedMapLeftSnakeDataOfDirectComparisonW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableClosedMapLeftSnakeDirectRightLcaBranchDataW778 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := limitComparisonOfDirectComparisonW779
  rightOpenLca := data.rightOpenLca
  rightSurjectiveLca := data.rightSurjectiveLca
  opLeftClosed := data.opLeftClosed
  opSnake := data.opSnake
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W779 closed-embedding branch converted to W778 data. -/
noncomputable def closedEmbeddingLeftSnakeDataOfDirectComparisonW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableClosedEmbeddingLeftSnakeDirectRightLcaBranchDataW778 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitComparison := limitComparisonOfDirectComparisonW779
  rightOpenLca := data.rightOpenLca
  rightSurjectiveLca := data.rightSurjectiveLca
  opLeftClosed := data.opLeftClosed
  opSnake := data.opSnake
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W779 closed-map product evidence through direct-comparison left/Snake data. -/
noncomputable def productEvidence_of_closedMapDirectComparisonLeftSnakeRouteW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapLeftSnakeDirectRightLcaRouteW778
    (closedMapLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-embedding product evidence through direct-comparison left/Snake data. -/
noncomputable def productEvidence_of_closedEmbeddingDirectComparisonLeftSnakeRouteW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingLeftSnakeDirectRightLcaRouteW778
    (closedEmbeddingLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapDirectComparisonLeftSnakeW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapLeftSnakeDirectRightLcaW778
    (closedMapLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (closedEmbeddingLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapDirectComparisonLeftSnakeW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapLeftSnakeDirectRightLcaW778
    (closedMapLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (closedEmbeddingLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapDirectComparisonLeftSnakeW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapLeftSnakeDirectRightLcaW778
    (closedMapLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingLeftSnakeDirectRightLcaW778
    (closedEmbeddingLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapDirectComparisonLeftSnakeStableBoundaryW779
    (data : MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapLeftSnakeDirectRightLcaStableBoundaryW778
    (closedMapLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedEmbeddingDirectComparisonLeftSnakeStableBoundaryW779
    (data : MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingLeftSnakeDirectRightLcaStableBoundaryW778
    (closedEmbeddingLeftSnakeDataOfDirectComparisonW779 data)

/-- W779 input names after W551 supplies the WPP limit comparison input. -/
def directComparisonLeftSnakeProductRouteInputNamesW779 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "W696 closed-range endpoint topology data"]

theorem directComparisonLeftSnakeProductRouteInputNamesW779_count :
    directComparisonLeftSnakeProductRouteInputNamesW779.length = 8 :=
  rfl

/-- Current checked W779 state. -/
structure MetrizableDirectComparisonLeftSnakeProductRouteStateW779 :
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

/-- Current checked W779 state for direct-comparison left/Snake routes. -/
def currentMetrizableDirectComparisonLeftSnakeProductRouteSupportStateW779 :
    MetrizableDirectComparisonLeftSnakeProductRouteStateW779
    where
  seed := "w779-direct-comparison-left-snake-normalized-closed-range-route"
  declarations :=
    ["MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779",
      "MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779",
      "limitComparisonOfDirectComparisonW779",
      "closedMapLeftSnakeDataOfDirectComparisonW779",
      "closedEmbeddingLeftSnakeDataOfDirectComparisonW779",
      "productEvidence_of_closedMapDirectComparisonLeftSnakeRouteW779",
      "productEvidence_of_closedEmbeddingDirectComparisonLeftSnakeRouteW779",
      "directFiniteShapeStableDataOfClosedMapDirectComparisonLeftSnakeW779",
      "directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonLeftSnakeW779",
      "stableBoundaryInputsOfClosedMapDirectComparisonLeftSnakeW779",
      "stableBoundaryInputsOfClosedEmbeddingDirectComparisonLeftSnakeW779",
      "acceptedStableOfClosedMapDirectComparisonLeftSnakeW779",
      "acceptedStableOfClosedEmbeddingDirectComparisonLeftSnakeW779",
      "boundedDerivedOfClosedMapDirectComparisonLeftSnakeStableBoundaryW779",
      "boundedDerivedOfClosedEmbeddingDirectComparisonLeftSnakeStableBoundaryW779",
      "directComparisonLeftSnakeProductRouteInputNamesW779",
      "directComparisonLeftSnakeProductRouteInputNamesW779_count"]
  directComparisonResult :=
    "proved: W551 supplies the W778 WPP limit-comparison field directly"
  stableBoundaryResult :=
    "proved: W779 direct-comparison left/Snake branches pass the\
      W778/W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus direct-comparison left/Snake data\
      feed W778"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus direct-comparison left/Snake\
      data feed W778"
  replacedInputs :=
    ["mapping-cone WPP limit comparison field",
      "separate W778 left/Snake direct-right-LCA stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP limit right-open pure LCA certificate",
      "construct WPP limit right-surjectivity pure LCA certificate",
      "construct WPP-op colimit left closed-embedding certificate",
      "construct WPP-op AddCommGrp SnakeInput cokernel-row certificate",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW779DirectComparisonLeftSnakeRoute_productSuccess :
    currentMetrizableDirectComparisonLeftSnakeProductRouteSupportStateW779.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
