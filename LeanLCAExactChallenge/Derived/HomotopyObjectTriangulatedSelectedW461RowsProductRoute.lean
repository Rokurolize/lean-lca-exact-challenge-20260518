import LeanLCAExactChallenge.Derived.SelectedW461RowsClosedQuotientEpiProductRoute

/-!
W782 feeds W781 by replacing the isomorphism-closure `Closed₂` premise with
the corresponding exact-acyclic homotopy-object `Closed₂` premise, using the
existing transport theorem from `Bounded.lean`.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W782 lower-level `Closed₂` input before isomorphism closure. -/
abbrev MetrizableExactAcyclicHomotopyObjectClosed2InputW782 : Prop :=
  (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂

/--
W782 transports the exact-acyclic homotopy-object `Closed₂` input to W781's
isomorphism-closure `Closed₂` input.
-/
theorem exactClosed2OfHomotopyObjectW782
    (hclosed : MetrizableExactAcyclicHomotopyObjectClosed2InputW782) :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ := by
  letI : (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    hclosed
  exact
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
      MetrizableLCA.{0}

/--
W782 closed-map branch data using exact-acyclic homotopy-object `Closed₂`
instead of W781's isomorphism-closure `Closed₂` input.
-/
structure
    MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  homotopyObjectClosed2 : MetrizableExactAcyclicHomotopyObjectClosed2InputW782
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
W782 closed-embedding branch data using exact-acyclic homotopy-object `Closed₂`
instead of W781's isomorphism-closure `Closed₂` input.
-/
structure
    MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  homotopyObjectClosed2 : MetrizableExactAcyclicHomotopyObjectClosed2InputW782
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

/-- W782 closed-map branch converted to W781 branch data. -/
noncomputable def closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableClosedMapSelectedW461RowsClosedQuotientEpiBranchDataW781 where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfHomotopyObjectW782 data.homotopyObjectClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W782 closed-embedding branch converted to W781 branch data. -/
noncomputable def
    closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableClosedEmbeddingSelectedW461RowsClosedQuotientEpiBranchDataW781
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfHomotopyObjectW782 data.homotopyObjectClosed2
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W782 closed-map product evidence through the homotopy-object `Closed₂` route. -/
noncomputable def productEvidence_of_closedMapHomotopyObjectTriangulatedRouteW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapSelectedW461RowsRouteW781
    (closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/--
W782 closed-embedding product evidence through the homotopy-object `Closed₂`
route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingHomotopyObjectTriangulatedRouteW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingSelectedW461RowsRouteW781
    (closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapHomotopyObjectW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapSelectedW461RowsW781
    (closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingHomotopyObjectW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingSelectedW461RowsW781
    (closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapHomotopyObjectW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapSelectedW461RowsW781
    (closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingHomotopyObjectW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingSelectedW461RowsW781
    (closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapHomotopyObjectW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapSelectedW461RowsW781
    (closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-embedding branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedEmbeddingHomotopyObjectW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingSelectedW461RowsW781
    (closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapHomotopyObjectStableBoundaryW782
    (data :
      MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapSelectedW461RowsStableBoundaryW781
    (closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedEmbeddingHomotopyObjectStableBoundaryW782
    (data :
      MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingSelectedW461RowsStableBoundaryW781
    (closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782 data)

/-- W782 input names after replacing W781's isomorphism-closure `Closed₂` premise. -/
def homotopyObjectTriangulatedSelectedW461RowsProductRouteInputNamesW782 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyObject MetrizableLCA is triangulated closed",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem homotopyObjectTriangulatedSelectedW461RowsProductRouteInputNamesW782_count :
    homotopyObjectTriangulatedSelectedW461RowsProductRouteInputNamesW782.length = 8 :=
  rfl

/-- Current checked W782 state. -/
structure MetrizableHomotopyObjectTriangulatedSelectedW461RowsRouteStateW782 :
    Type where
  seed : String
  declarations : List String
  transportResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W782 state for the homotopy-object `Closed₂` route. -/
def currentMetrizableHomotopyObjectTriangulatedSelectedW461RowsRouteStateW782 :
    MetrizableHomotopyObjectTriangulatedSelectedW461RowsRouteStateW782
    where
  seed := "w782-homotopy-object-triangulated-selected-w461-rows-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectClosed2InputW782",
      "exactClosed2OfHomotopyObjectW782",
      "MetrizableClosedMapHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782",
      "MetrizableClosedEmbeddingHomotopyObjectTriangulatedSelectedW461RowsBranchDataW782",
      "closedMapSelectedW461RowsDataOfHomotopyObjectTriangulatedW782",
      "closedEmbeddingSelectedW461RowsDataOfHomotopyObjectTriangulatedW782",
      "productEvidence_of_closedMapHomotopyObjectTriangulatedRouteW782",
      "productEvidence_of_closedEmbeddingHomotopyObjectTriangulatedRouteW782",
      "directFiniteShapeStableDataOfClosedMapHomotopyObjectW782",
      "directFiniteShapeStableDataOfClosedEmbeddingHomotopyObjectW782",
      "stableBoundaryInputsOfClosedMapHomotopyObjectW782",
      "stableBoundaryInputsOfClosedEmbeddingHomotopyObjectW782",
      "acceptedStableOfClosedMapHomotopyObjectW782",
      "acceptedStableOfClosedEmbeddingHomotopyObjectW782",
      "boundedDerivedOfClosedMapHomotopyObjectStableBoundaryW782",
      "boundedDerivedOfClosedEmbeddingHomotopyObjectStableBoundaryW782",
      "homotopyObjectTriangulatedSelectedW461RowsProductRouteInputNamesW782",
      "homotopyObjectTriangulatedSelectedW461RowsProductRouteInputNamesW782_count"]
  transportResult :=
    "proved: exact-acyclic homotopy-object Closed2 supplies W781's closure Closed2"
  stableBoundaryResult :=
    "proved: W782 homotopy-object triangulated selected-W461/rows branches pass\
      the W781/W780/W779/W778/W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map homotopy-object Closed2 branch data feeds W781"
  closedEmbeddingResult :=
    "proved: closed-embedding homotopy-object Closed2 branch data feeds W781"
  replacedInputs :=
    ["exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "separate W781 selected-W461/rows stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyObject MetrizableLCA is triangulated closed",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW782HomotopyObjectTriangulatedRoute_productSuccess :
    (have state :=
      currentMetrizableHomotopyObjectTriangulatedSelectedW461RowsRouteStateW782;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
