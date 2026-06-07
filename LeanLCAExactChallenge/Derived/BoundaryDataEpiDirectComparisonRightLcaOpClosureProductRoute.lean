import LeanLCAExactChallenge.Derived.ClosedQuotientEpiDirectComparisonRightLcaOpClosureProductRoute

/-!
W1602 feeds W1601 by deriving the right-open closed quotient-cover boundary
from the W716 boundary data already carried by the W735 exact inputs.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1602 closed-map branch data without a separate right-open boundary; W735
`exactInputs.boundaryData` supplies it.
-/
structure MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW1601
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W1602 closed-embedding branch data without a separate right-open boundary; W735
`exactInputs.boundaryData` supplies it.
-/
structure
    MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW1601
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W1602 projects W1601's right-open boundary from bundled W716 data. -/
theorem rightOpenBoundaryOfBoundaryDataRightLcaOpClosureW1602
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary :=
  rightOpenBoundary_of_boundaryDataW716 boundaryData

/-- W1602 closed-map branch converted to W1601 closed-quotient/Epi data. -/
noncomputable def closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableClosedMapClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary :=
    rightOpenBoundaryOfBoundaryDataRightLcaOpClosureW1602
      data.exactInputs.boundaryData
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1602 closed-embedding branch converted to W1601 closed-quotient/Epi data. -/
noncomputable def
    closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonRightLcaOpClosureBranchDataW1601
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary :=
    rightOpenBoundaryOfBoundaryDataRightLcaOpClosureW1602
      data.exactInputs.boundaryData
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1602 closed-map product evidence after deriving the right-open boundary. -/
noncomputable def productEvidence_of_closedMapBoundaryDataEpiRightLcaOpClosureRouteW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapClosedQuotientEpiRightLcaOpClosureRouteW1601
    (closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/--
W1602 closed-embedding product evidence after deriving the right-open boundary.
-/
noncomputable def
    productEvidence_of_closedEmbeddingBoundaryDataEpiRightLcaOpClosureRouteW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingClosedQuotientEpiRightLcaOpClosureRouteW1601
    (closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapClosedQuotientEpiRightLcaOpClosureW1601
    (closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/--
W1602 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureW1601
    (closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapBoundaryDataEpiRightLcaOpClosureStableBoundaryW1602
    (data :
      MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601
    (closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/--
W1602 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureStableBoundaryW1602
    (data :
      MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingClosedQuotientEpiRightLcaOpClosureStableBoundaryW1601
    (closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602 data)

/-- W1602 input names after deriving right-open data from W735 boundary data. -/
def boundaryDataEpiDirectComparisonRightLcaOpClosureInputNamesW1602 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data and W735 exact-input fields",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "Epi boundary for WPP limit right-surjectivity",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem boundaryDataEpiDirectComparisonRightLcaOpClosureInputNamesW1602_count :
    boundaryDataEpiDirectComparisonRightLcaOpClosureInputNamesW1602.length =
      6 :=
  rfl

/-- Current checked W1602 state. -/
structure MetrizableBoundaryDataEpiDirectComparisonRightLcaOpClosureRouteStateW1602 :
    Type where
  seed : String
  declarations : List String
  rightOpenProjectionResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W1602 state for the W716 boundary-data route. -/
def currentMetrizableBoundaryDataEpiDirectComparisonRightLcaOpClosureRouteStateW1602 :
    MetrizableBoundaryDataEpiDirectComparisonRightLcaOpClosureRouteStateW1602
    where
  seed := "w1602-boundary-data-epi-direct-comparison-right-lca-op-closure-route"
  declarations :=
    ["MetrizableClosedMapBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602",
      "MetrizableClosedEmbeddingBoundaryDataEpiDirectComparisonRightLcaOpClosureBranchDataW1602",
      "rightOpenBoundaryOfBoundaryDataRightLcaOpClosureW1602",
      "closedMapClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602",
      "closedEmbeddingClosedQuotientEpiRightLcaOpClosureDataOfBoundaryDataW1602",
      "productEvidence_of_closedMapBoundaryDataEpiRightLcaOpClosureRouteW1602",
      "productEvidence_of_closedEmbeddingBoundaryDataEpiRightLcaOpClosureRouteW1602",
      "directFiniteShapeStableDataOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602",
      "directFiniteShapeStableDataOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602",
      "stableBoundaryInputsOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602",
      "stableBoundaryInputsOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602",
      "acceptedStableOfClosedMapBoundaryDataEpiRightLcaOpClosureW1602",
      "acceptedStableOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureW1602",
      "boundedDerivedOfClosedMapBoundaryDataEpiRightLcaOpClosureStableBoundaryW1602",
      "boundedDerivedOfClosedEmbeddingBoundaryDataEpiRightLcaOpClosureStableBoundaryW1602",
      "boundaryDataEpiDirectComparisonRightLcaOpClosureInputNamesW1602",
      "boundaryDataEpiDirectComparisonRightLcaOpClosureInputNamesW1602_count"]
  rightOpenProjectionResult :=
    "proved: W735 exactInputs.boundaryData supplies W1601's right-open closed\
      quotient-cover boundary via W716"
  stableBoundaryResult :=
    "proved: W1602 boundary-data/Epi direct-comparison right-LCA/WPP-op\
      closure branches pass the W1601/W1600/W777/W776/W775/W774/W773/W769\
      canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus Epi right-surjectivity data feed\
      W1601 without a separate right-open boundary field"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus Epi right-surjectivity data\
      feed W1601 without a separate right-open boundary field"
  replacedInputs :=
    ["separate MetrizableWppLimitRightOpenClosedQuotientCoverBoundary field",
      "separate W1601 closed-quotient/Epi direct-comparison right-LCA/WPP-op\
        closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch, including W716 boundary\
        data",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1602BoundaryDataEpiDirectComparisonRightLcaOpClosureRoute_productSuccess :
    (have state :=
      currentMetrizableBoundaryDataEpiDirectComparisonRightLcaOpClosureRouteStateW1602;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
