import LeanLCAExactChallenge.Derived.DirectComparisonLeftSnakeProductRoute

/-!
W780 feeds W779 by replacing the pure right-LCA limit fields with existing
closed quotient-cover and Epi boundary adapters.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W780 names the direct Epi boundary for pure WPP limit right-surjectivity. -/
abbrev MetrizableWppLimitRightSurjectiveEpiBoundaryW780 : Prop :=
  DirectWppLimitFiniteShapeTransfer.WppLimitLcaRightSurjectiveEpiBoundary

/--
W780 closed-map branch data using closed quotient-cover right-open data,
Epi right-surjectivity data, direct comparison, and left/Snake colimits.
-/
structure MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W780 closed-embedding branch data using closed quotient-cover right-open data,
Epi right-surjectivity data, direct comparison, and left/Snake colimits.
-/
structure
    MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W780 closed quotient-cover data supplies W779's pure right-open field. -/
theorem rightOpenLcaOfClosedQuotientW780
    (hboundary : MetrizableWppLimitRightOpenClosedQuotientCoverBoundary) :
    MetrizableWppLimitRightOpenLcaInput :=
  metrizableWppLimitRightOpenLcaInput_of_closedQuotientCoverBoundary hboundary

/-- W780 Epi data supplies W779's pure right-surjectivity field. -/
theorem rightSurjectiveLcaOfEpiBoundaryW780
    (hboundary : MetrizableWppLimitRightSurjectiveEpiBoundaryW780) :
    MetrizableWppLimitRightSurjectiveLcaInput :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitMap_preserves_surjective_of_epiBoundary
    hboundary

/-- W780 closed-map branch converted to W779 direct-comparison data. -/
noncomputable def closedMapDirectComparisonDataOfClosedQuotientEpiW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableClosedMapDirectComparisonLeftSnakeBranchDataW779 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenLca := rightOpenLcaOfClosedQuotientW780 data.rightOpenBoundary
  rightSurjectiveLca :=
    rightSurjectiveLcaOfEpiBoundaryW780 data.rightSurjectiveBoundary
  opLeftClosed := data.opLeftClosed
  opSnake := data.opSnake
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W780 closed-embedding branch converted to W779 direct-comparison data. -/
noncomputable def closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableClosedEmbeddingDirectComparisonLeftSnakeBranchDataW779 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenLca := rightOpenLcaOfClosedQuotientW780 data.rightOpenBoundary
  rightSurjectiveLca :=
    rightSurjectiveLcaOfEpiBoundaryW780 data.rightSurjectiveBoundary
  opLeftClosed := data.opLeftClosed
  opSnake := data.opSnake
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W780 closed-map product evidence through closed-quotient/Epi data. -/
noncomputable def productEvidence_of_closedMapClosedQuotientEpiRouteW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapDirectComparisonLeftSnakeRouteW779
    (closedMapDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-embedding product evidence through closed-quotient/Epi data. -/
noncomputable def productEvidence_of_closedEmbeddingClosedQuotientEpiRouteW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingDirectComparisonLeftSnakeRouteW779
    (closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapClosedQuotientEpiW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapDirectComparisonLeftSnakeW779
    (closedMapDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingClosedQuotientEpiW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapClosedQuotientEpiW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapDirectComparisonLeftSnakeW779
    (closedMapDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingClosedQuotientEpiW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapClosedQuotientEpiW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapDirectComparisonLeftSnakeW779
    (closedMapDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedEmbeddingClosedQuotientEpiW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingDirectComparisonLeftSnakeW779
    (closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapClosedQuotientEpiStableBoundaryW780
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapDirectComparisonLeftSnakeStableBoundaryW779
    (closedMapDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedEmbeddingClosedQuotientEpiStableBoundaryW780
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingDirectComparisonLeftSnakeStableBoundaryW779
    (closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780 data)

/-- W780 input names after boundary adapters supply both pure right-LCA fields. -/
def closedQuotientEpiDirectComparisonLeftSnakeInputNamesW780 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "W696 closed-range endpoint topology data"]

theorem closedQuotientEpiDirectComparisonLeftSnakeInputNamesW780_count :
    closedQuotientEpiDirectComparisonLeftSnakeInputNamesW780.length = 8 :=
  rfl

/-- Current checked W780 state. -/
structure MetrizableClosedQuotientEpiDirectComparisonLeftSnakeRouteStateW780 :
    Type where
  seed : String
  declarations : List String
  rightOpenBoundaryResult : String
  rightSurjectiveBoundaryResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W780 state for closed quotient-cover/Epi boundary routes. -/
def currentMetrizableClosedQuotientEpiDirectComparisonLeftSnakeRouteStateW780 :
    MetrizableClosedQuotientEpiDirectComparisonLeftSnakeRouteStateW780
    where
  seed := "w780-closed-quotient-epi-direct-comparison-left-snake-route"
  declarations :=
    ["MetrizableWppLimitRightSurjectiveEpiBoundaryW780",
      "MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780",
      "MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780",
      "rightOpenLcaOfClosedQuotientW780",
      "rightSurjectiveLcaOfEpiBoundaryW780",
      "closedMapDirectComparisonDataOfClosedQuotientEpiW780",
      "closedEmbeddingDirectComparisonDataOfClosedQuotientEpiW780",
      "productEvidence_of_closedMapClosedQuotientEpiRouteW780",
      "productEvidence_of_closedEmbeddingClosedQuotientEpiRouteW780",
      "directFiniteShapeStableDataOfClosedMapClosedQuotientEpiW780",
      "directFiniteShapeStableDataOfClosedEmbeddingClosedQuotientEpiW780",
      "stableBoundaryInputsOfClosedMapClosedQuotientEpiW780",
      "stableBoundaryInputsOfClosedEmbeddingClosedQuotientEpiW780",
      "acceptedStableOfClosedMapClosedQuotientEpiW780",
      "acceptedStableOfClosedEmbeddingClosedQuotientEpiW780",
      "boundedDerivedOfClosedMapClosedQuotientEpiStableBoundaryW780",
      "boundedDerivedOfClosedEmbeddingClosedQuotientEpiStableBoundaryW780",
      "closedQuotientEpiDirectComparisonLeftSnakeInputNamesW780",
      "closedQuotientEpiDirectComparisonLeftSnakeInputNamesW780_count"]
  rightOpenBoundaryResult :=
    "proved: closed quotient-cover data supplies W779's pure right-open field"
  rightSurjectiveBoundaryResult :=
    "proved: Epi data supplies W779's pure right-surjectivity field"
  stableBoundaryResult :=
    "proved: W780 closed-quotient/Epi direct-comparison left/Snake branches\
      pass the W779/W778/W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map boundary-adapted branch data feeds W779"
  closedEmbeddingResult :=
    "proved: closed-embedding boundary-adapted branch data feeds W779"
  replacedInputs :=
    ["pure WPP limit right-open LCA field",
      "pure WPP limit right-surjectivity LCA field",
      "separate W779 direct-comparison left/Snake stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct WPP-op colimit left closed-embedding certificate",
      "construct WPP-op AddCommGrp SnakeInput cokernel-row certificate",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW780ClosedQuotientEpiDirectComparisonLeftSnakeRoute_productSuccess :
    (have state :=
      currentMetrizableClosedQuotientEpiDirectComparisonLeftSnakeRouteStateW780;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
