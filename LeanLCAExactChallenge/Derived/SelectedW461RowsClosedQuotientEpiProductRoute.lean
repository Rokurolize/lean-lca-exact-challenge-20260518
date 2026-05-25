import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields
import LeanLCAExactChallenge.Derived.ClosedQuotientEpiDirectComparisonLeftSnakeProductRoute

/-!
W781 feeds W780 by replacing the WPP-op left/Snake fields with existing W483
selected-W461 and W527 row-aware closed-map/closed-embedding adapters.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpRowAwareClosedMapClosedRangeOnlyProjectionV370SupportW527

/-- W781 selected-W461 provider input for the WPP-op left field. -/
abbrev WppOpSelectedW461ProviderW781 : Type 1 :=
  SelectedW461PromotionInputsProviderW483

/-- W781 row-aware closed-map provider input for the WPP-op Snake field. -/
abbrev WppOpClosedMapRowsProviderW781 : Type 1 :=
  ComponentwiseClosedMapRowsProviderW527

/-- W781 row-aware closed-embedding provider input for the WPP-op Snake field. -/
abbrev WppOpClosedEmbeddingRowsProviderW781 : Type 1 :=
  ComponentwiseClosedEmbeddingRowsProviderW527

/--
W781 closed-map branch data using selected-W461 left data and row-aware
closed-map Snake data.
-/
structure MetrizableClosedMapSelectedW461RowsClosedQuotientEpiBranchDataW781 :
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
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W781 closed-embedding branch data using selected-W461 left data and row-aware
closed-embedding Snake data.
-/
structure
    MetrizableClosedEmbeddingSelectedW461RowsClosedQuotientEpiBranchDataW781 :
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
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W781 selected-W461 data supplies W780's WPP-op left closed field. -/
theorem opLeftClosedOfSelectedW461W781
  (hselected : WppOpSelectedW461ProviderW781) :
    MetrizableWppOpLeftClosedInput :=
  wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483
    hselected

/-- W781 row-aware closed-map data supplies W780's WPP-op Snake field. -/
theorem opSnakeOfClosedMapRowsW781
  (hrows : WppOpClosedMapRowsProviderW781) :
    MetrizableWppOpSnakeInput :=
  addCommGrpStrictSnakeCokernelBoundary_of_closedMapRows_w527 hrows

/-- W781 row-aware closed-embedding data supplies W780's WPP-op Snake field. -/
theorem opSnakeOfClosedEmbeddingRowsW781
  (hrows : WppOpClosedEmbeddingRowsProviderW781) :
    MetrizableWppOpSnakeInput :=
  addCommGrpStrictSnakeCokernelBoundary_of_closedEmbeddingRows_w527 hrows

/-- W781 closed-map branch converted to W780 data. -/
noncomputable def closedMapClosedQuotientEpiDataOfSelectedW461RowsW781
    (data : MetrizableClosedMapSelectedW461RowsClosedQuotientEpiBranchDataW781) :
    MetrizableClosedMapClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  opLeftClosed := opLeftClosedOfSelectedW461W781 data.selectedW461
  opSnake := opSnakeOfClosedMapRowsW781 data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W781 closed-embedding branch converted to W780 data. -/
noncomputable def closedEmbeddingClosedQuotientEpiDataOfSelectedW461RowsW781
    (data :
      MetrizableClosedEmbeddingSelectedW461RowsClosedQuotientEpiBranchDataW781) :
    MetrizableClosedEmbeddingClosedQuotientEpiDirectComparisonLeftSnakeBranchDataW780
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  opLeftClosed := opLeftClosedOfSelectedW461W781 data.selectedW461
  opSnake := opSnakeOfClosedEmbeddingRowsW781 data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W781 closed-map product evidence through selected-W461/rows data. -/
noncomputable def productEvidence_of_closedMapSelectedW461RowsRouteW781
    (data : MetrizableClosedMapSelectedW461RowsClosedQuotientEpiBranchDataW781) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapClosedQuotientEpiRouteW780
    (closedMapClosedQuotientEpiDataOfSelectedW461RowsW781 data)

/-- W781 closed-embedding product evidence through selected-W461/rows data. -/
noncomputable def productEvidence_of_closedEmbeddingSelectedW461RowsRouteW781
    (data :
      MetrizableClosedEmbeddingSelectedW461RowsClosedQuotientEpiBranchDataW781) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingClosedQuotientEpiRouteW780
    (closedEmbeddingClosedQuotientEpiDataOfSelectedW461RowsW781 data)

/-- W781 input names after W483/W527 adapters supply WPP-op left/Snake fields. -/
def selectedW461RowsClosedQuotientEpiProductRouteInputNamesW781 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem selectedW461RowsClosedQuotientEpiProductRouteInputNamesW781_count :
    selectedW461RowsClosedQuotientEpiProductRouteInputNamesW781.length = 8 :=
  rfl

/-- Current checked W781 state. -/
structure MetrizableSelectedW461RowsClosedQuotientEpiRouteStateW781 :
    Type where
  seed : String
  declarations : List String
  selectedW461Result : String
  closedMapRowsResult : String
  closedEmbeddingRowsResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W781 state for selected-W461/row-aware WPP-op routes. -/
def currentMetrizableSelectedW461RowsClosedQuotientEpiRouteStateW781 :
    MetrizableSelectedW461RowsClosedQuotientEpiRouteStateW781
    where
  seed := "w781-selected-w461-rows-closed-quotient-epi-route"
  declarations :=
    ["WppOpSelectedW461ProviderW781",
      "WppOpClosedMapRowsProviderW781",
      "WppOpClosedEmbeddingRowsProviderW781",
      "MetrizableClosedMapSelectedW461RowsClosedQuotientEpiBranchDataW781",
      "MetrizableClosedEmbeddingSelectedW461RowsClosedQuotientEpiBranchDataW781",
      "opLeftClosedOfSelectedW461W781",
      "opSnakeOfClosedMapRowsW781",
      "opSnakeOfClosedEmbeddingRowsW781",
      "closedMapClosedQuotientEpiDataOfSelectedW461RowsW781",
      "closedEmbeddingClosedQuotientEpiDataOfSelectedW461RowsW781",
      "productEvidence_of_closedMapSelectedW461RowsRouteW781",
      "productEvidence_of_closedEmbeddingSelectedW461RowsRouteW781",
      "selectedW461RowsClosedQuotientEpiProductRouteInputNamesW781",
      "selectedW461RowsClosedQuotientEpiProductRouteInputNamesW781_count"]
  selectedW461Result :=
    "proved: selected W461 provider supplies W780's WPP-op left field"
  closedMapRowsResult :=
    "proved: row-aware closed-map provider supplies W780's Snake field"
  closedEmbeddingRowsResult :=
    "proved: row-aware closed-embedding provider supplies W780's Snake field"
  closedMapResult :=
    "proved: closed-map selected-W461/rows branch data feeds W780"
  closedEmbeddingResult :=
    "proved: closed-embedding selected-W461/rows branch data feeds W780"
  replacedInputs :=
    ["WPP-op colimit left closed-embedding certificate",
      "WPP-op AddCommGrp SnakeInput cokernel-row certificate"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW781SelectedW461RowsClosedQuotientEpiRoute_productSuccess :
    (have state :=
      currentMetrizableSelectedW461RowsClosedQuotientEpiRouteStateW781;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
