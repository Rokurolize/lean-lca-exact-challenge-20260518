import LeanLCAExactChallenge.Derived.DirectComparisonRightLcaOpClosureProductRoute

/-!
W1601 feeds W1600 by replacing the pure right-LCA fields with closed
quotient-cover and Epi boundary adapters.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1601 names the direct Epi boundary for pure WPP limit right-surjectivity.
-/
abbrev MetrizableWppLimitRightSurjectiveEpiBoundaryW1601 : Prop :=
  DirectWppLimitFiniteShapeTransfer.WppLimitLcaRightSurjectiveEpiBoundary

/--
W1601 closed-map branch data using closed quotient-cover right-open data,
Epi right-surjectivity data, direct comparison, and WPP-op exact-acyclic
colimit closure.
-/
structure
    MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601 :
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
    MetrizableWppLimitRightSurjectiveEpiBoundaryW1601
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W1601 closed-embedding branch data using closed quotient-cover right-open data,
Epi right-surjectivity data, direct comparison, and WPP-op exact-acyclic
colimit closure.
-/
structure
    MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601 :
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
    MetrizableWppLimitRightSurjectiveEpiBoundaryW1601
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W1601 closed quotient-cover data supplies W1600's pure right-open field. -/
theorem rightOpenLcaOfClosedQuotientRightLcaOpClosureW1601
    (hboundary : MetrizableWppLimitRightOpenClosedQuotientCoverBoundary) :
    MetrizableWppLimitRightOpenLcaInput :=
  metrizableWppLimitRightOpenLcaInput_of_closedQuotientCoverBoundary hboundary

/-- W1601 Epi data supplies W1600's pure right-surjectivity field. -/
theorem rightSurjectiveLcaOfEpiBoundaryRightLcaOpClosureW1601
    (hboundary : MetrizableWppLimitRightSurjectiveEpiBoundaryW1601) :
    MetrizableWppLimitRightSurjectiveLcaInput :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitMap_preserves_surjective_of_epiBoundary
    hboundary

/-- W1601 closed-map branch converted to W1600 direct-comparison data. -/
noncomputable def closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableClosedMapDirectComparisonRightLcaOpClosureBranchDataW1600 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenLca :=
    rightOpenLcaOfClosedQuotientRightLcaOpClosureW1601 data.rightOpenBoundary
  rightSurjectiveLca :=
    rightSurjectiveLcaOfEpiBoundaryRightLcaOpClosureW1601
      data.rightSurjectiveBoundary
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1601 closed-embedding branch converted to W1600 direct-comparison data. -/
noncomputable def
    closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableClosedEmbeddingDirectComparisonRightLcaOpClosureBranchDataW1600
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenLca :=
    rightOpenLcaOfClosedQuotientRightLcaOpClosureW1601 data.rightOpenBoundary
  rightSurjectiveLca :=
    rightSurjectiveLcaOfEpiBoundaryRightLcaOpClosureW1601
      data.rightSurjectiveBoundary
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1601 closed-map product evidence through closed-quotient/Epi data. -/
noncomputable def productEvidence_of_closedMapClosedQuotientEpiRightLcaOpClosureRouteW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapDirectComparisonRightLcaOpClosureRouteW1600
    (closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-embedding product evidence through closed-quotient/Epi data. -/
noncomputable def
    productEvidence_of_closedEmbeddingClosedQuotientEpiRightLcaOpClosureRouteW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingDirectComparisonRightLcaOpClosureRouteW1600
    (closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapDirectComparisonRightLcaOpClosureW1600
    (closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/--
W1601 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingDirectComparisonRightLcaOpClosureW1600
    (closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601
    (data :
      MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapDirectComparisonRightLcaOpClosureStableBoundaryW1600
    (closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/--
W1601 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601
    (data :
      MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingDirectComparisonRightLcaOpClosureStableBoundaryW1600
    (closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601 data)

/-- W1601 input names after boundary adapters supply both pure right-LCA fields. -/
def closedQuotientEpiDirectComparisonRightLcaOpClosureInputNamesW1601 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem closedQuotientEpiDirectComparisonRightLcaOpClosureInputNamesW1601_count :
    closedQuotientEpiDirectComparisonRightLcaOpClosureInputNamesW1601.length =
      7 :=
  rfl

/-- Current checked W1601 state. -/
structure MetrizableClosedQuotientEpiDirectComparisonRightLcaOpClosureRouteStateW1601 :
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

/-- Current checked W1601 state for closed quotient-cover/Epi boundary routes. -/
def currentMetrizableClosedQuotientEpiDirectComparisonRightLcaOpClosureRouteStateW1601 :
    MetrizableClosedQuotientEpiDirectComparisonRightLcaOpClosureRouteStateW1601
    where
  seed := "w1601-closed-quotient-epi-direct-comparison-right-lca-op-closure-route"
  declarations :=
    ["MetrizableWppLimitRightSurjectiveEpiBoundaryW1601",
      "MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601",
      "MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601",
      "rightOpenLcaOfClosedQuotientRightLcaOpClosureW1601",
      "rightSurjectiveLcaOfEpiBoundaryRightLcaOpClosureW1601",
      "closedMapDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601",
      "closedEmbeddingDirectComparisonRightLcaOpClosureDataOfClosedQuotientEpiW1601",
      "productEvidence_of_closedMapClosedQuotientEpiRightLcaOpClosureRouteW1601",
      "productEvidence_of_closedEmbeddingClosedQuotientEpiRightLcaOpClosureRouteW1601",
      "directFiniteShapeStableDataOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601",
      "directFiniteShapeStableDataOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601",
      "stableBoundaryInputsOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601",
      "stableBoundaryInputsOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601",
      "acceptedStableOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601",
      "acceptedStableOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601",
      "boundedDerivedOfClosedMapClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601",
      "boundedDerivedOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601",
      "closedQuotientEpiDirectComparisonRightLcaOpClosureInputNamesW1601",
      "closedQuotientEpiDirectComparisonRightLcaOpClosureInputNamesW1601_count"]
  rightOpenBoundaryResult :=
    "proved: closed quotient-cover data supplies W1600's pure right-open field"
  rightSurjectiveBoundaryResult :=
    "proved: Epi data supplies W1600's pure right-surjectivity field"
  stableBoundaryResult :=
    "proved: W1601 closed-quotient/Epi direct-comparison right-LCA/WPP-op\
      closure branches pass the W1600/W777/W776/W775/W774/W773/W769 canonical\
      stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map boundary-adapted branch data feeds W1600"
  closedEmbeddingResult :=
    "proved: closed-embedding boundary-adapted branch data feeds W1600"
  replacedInputs :=
    ["pure WPP limit right-open LCA field",
      "pure WPP limit right-surjectivity LCA field",
      "separate W1600 direct-comparison right-LCA/WPP-op-closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1601ClosedQuotientEpiDirectComparisonRightLcaOpClosureRoute_productSuccess :
    (have state :=
      currentMetrizableClosedQuotientEpiDirectComparisonRightLcaOpClosureRouteStateW1601;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
