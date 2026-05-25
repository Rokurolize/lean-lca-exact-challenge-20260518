import LeanLCAExactChallenge.Derived.TargetHomologyZeroExactInputsClosedRangeProductRoute

/-!
W791 derives the target homology-zero route's right-open boundary from W735
`exactInputs.boundaryData` through W716.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W791 closed-map branch data without a separate right-open boundary; W735
`exactInputs.boundaryData` supplies it.
-/
structure MetrizableClosedMapTargetHomologyZeroBoundaryDataBranchDataW791 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      hasHomology
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781

/--
W791 closed-embedding branch data without a separate right-open boundary; W735
`exactInputs.boundaryData` supplies it.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroBoundaryDataBranchDataW791 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      hasHomology
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/-- W791 closed-map branch converted to W790 branch data. -/
noncomputable def closedMapExactInputsDataOfBoundaryDataW791
    (data : MetrizableClosedMapTargetHomologyZeroBoundaryDataBranchDataW791) :
    MetrizableClosedMapTargetHomologyZeroExactInputsClosedRangeBranchDataW790
    where
  comparisonIso := data.comparisonIso
  hasHomology := data.hasHomology
  targetHomologyZeroPayload := data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary :=
    rightOpenBoundary_of_boundaryDataW716 data.exactInputs.boundaryData
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows

/-- W791 closed-embedding branch converted to W790 branch data. -/
noncomputable def closedEmbeddingExactInputsDataOfBoundaryDataW791
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundaryDataBranchDataW791) :
    MetrizableClosedEmbeddingTargetHomologyZeroExactInputsClosedRangeBranchDataW790
    where
  comparisonIso := data.comparisonIso
  hasHomology := data.hasHomology
  targetHomologyZeroPayload := data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary :=
    rightOpenBoundary_of_boundaryDataW716 data.exactInputs.boundaryData
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows

/-- W791 closed-map product evidence after deriving the right-open boundary. -/
noncomputable def productEvidence_of_closedMapTargetHomologyZeroBoundaryDataRouteW791
    (data : MetrizableClosedMapTargetHomologyZeroBoundaryDataBranchDataW791) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetHomologyZeroExactInputsClosedRangeRouteW790
    (closedMapExactInputsDataOfBoundaryDataW791 data)

/-!
W791 closed-embedding product evidence after deriving the right-open boundary.
-/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroBoundaryDataRouteW791
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundaryDataBranchDataW791) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetHomologyZeroExactInputsClosedRangeRouteW790
    (closedEmbeddingExactInputsDataOfBoundaryDataW791 data)

/-- W791 input names after deriving right-open data from W735 boundary data. -/
def targetHomologyZeroBoundaryDataProductRouteInputNamesW791 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data and W735 exact-input fields",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput"]

theorem targetHomologyZeroBoundaryDataProductRouteInputNamesW791_count :
    targetHomologyZeroBoundaryDataProductRouteInputNamesW791.length = 7 :=
  rfl

/-- Current checked W791 state. -/
structure MetrizableTargetHomologyZeroBoundaryDataRouteStateW791 :
    Type where
  seed : String
  declarations : List String
  rightOpenProjectionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W791 state for the W716 boundary-data route. -/
def currentMetrizableTargetHomologyZeroBoundaryDataRouteStateW791 :
    MetrizableTargetHomologyZeroBoundaryDataRouteStateW791
    where
  seed := "w791-target-homology-zero-boundary-data-route"
  declarations :=
    ["MetrizableClosedMapTargetHomologyZeroBoundaryDataBranchDataW791",
      "MetrizableClosedEmbeddingTargetHomologyZeroBoundaryDataBranchDataW791",
      "closedMapExactInputsDataOfBoundaryDataW791",
      "closedEmbeddingExactInputsDataOfBoundaryDataW791",
      "productEvidence_of_closedMapTargetHomologyZeroBoundaryDataRouteW791",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroBoundaryDataRouteW791",
      "targetHomologyZeroBoundaryDataProductRouteInputNamesW791",
      "targetHomologyZeroBoundaryDataProductRouteInputNamesW791_count"]
  rightOpenProjectionResult :=
    "proved: W735 exactInputs.boundaryData supplies right-open boundary via W716"
  closedMapResult :=
    "proved: closed-map target homology-zero boundary-data route feeds W790"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero boundary-data route feeds\
      W790"
  replacedInputs :=
    ["separate MetrizableWppLimitRightOpenClosedQuotientCoverBoundary field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput"]
  productSuccessClaimed := false

theorem currentW791TargetHomologyZeroBoundaryDataRoute_productSuccess :
    (have state := currentMetrizableTargetHomologyZeroBoundaryDataRouteStateW791;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
