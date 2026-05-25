import LeanLCAExactChallenge.Derived.TargetExactAtEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W786 feeds W784 by replacing the target `ExactAt` realization payload with
W664 target homology-zero realization data plus global homology existence and
endpoint-strict topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W786 target homology-zero payload for exact-acyclic homotopy objects. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i) :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTrianglehIso13TargetHomologyZeroPayloadW664
    hasHomology

/--
W786 turns target homology-zero realization data plus endpoint topology into
W784's target-isomorphism realization input.
-/
theorem targetIsoRealizationOfTargetHomologyZeroEndpointW786
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (endpointTopology : MetrizableExactAtEndpointStrictTopologyInputs)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
        hasHomology) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm, hZero⟩
  let H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
    Dbounded.homologyDetection_of_endpointTopology_w603
      hasHomology endpointTopology
  exact
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm,
      H.exactAcyclic_of_isZero_homology Lzero hZero⟩

/--
W786 closed-map branch data using target homology-zero realization data instead
of W785's target `ExactAt` realization payload.
-/
structure MetrizableClosedMapTargetHomologyZeroEndpointTargetIsoBranchDataW786 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
      hasHomology
  endpointStrictTopology : MetrizableExactAtEndpointStrictTopologyInputs
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
W786 closed-embedding branch data using target homology-zero realization data
instead of W785's target `ExactAt` realization payload.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroEndpointTargetIsoBranchDataW786 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
      hasHomology
  endpointStrictTopology : MetrizableExactAtEndpointStrictTopologyInputs
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

/-- W786 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetHomologyZeroEndpointW786
    (data :
      MetrizableClosedMapTargetHomologyZeroEndpointTargetIsoBranchDataW786) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroEndpointW786
      data.hasHomology data.endpointStrictTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W786 closed-embedding branch converted to W784 branch data. -/
noncomputable def closedEmbeddingTargetIsoDataOfTargetHomologyZeroEndpointW786
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroEndpointTargetIsoBranchDataW786) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroEndpointW786
      data.hasHomology data.endpointStrictTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W786 closed-map product evidence through target homology-zero endpoint data. -/
noncomputable def productEvidence_of_closedMapTargetHomologyZeroEndpointRouteW786
    (data :
      MetrizableClosedMapTargetHomologyZeroEndpointTargetIsoBranchDataW786) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetHomologyZeroEndpointW786 data)

/-- W786 closed-embedding product evidence through target homology-zero endpoint data. -/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroEndpointRouteW786
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroEndpointTargetIsoBranchDataW786) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroEndpointW786 data)

/-- W786 input names after replacing W785's target `ExactAt` payload. -/
def targetHomologyZeroEndpointTargetIsoProductRouteInputNamesW786 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "Metrizable exact-at endpoint-strict topology data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetHomologyZeroEndpointTargetIsoProductRouteInputNamesW786_count :
    targetHomologyZeroEndpointTargetIsoProductRouteInputNamesW786.length = 10 :=
  rfl

/-- Current checked W786 state. -/
structure MetrizableTargetHomologyZeroEndpointTargetIsoRouteStateW786 :
    Type where
  seed : String
  declarations : List String
  transportResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W786 state for the target homology-zero endpoint route. -/
def currentMetrizableTargetHomologyZeroEndpointTargetIsoRouteStateW786 :
    MetrizableTargetHomologyZeroEndpointTargetIsoRouteStateW786
    where
  seed := "w786-target-homology-zero-endpoint-target-iso-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786",
      "targetIsoRealizationOfTargetHomologyZeroEndpointW786",
      "MetrizableClosedMapTargetHomologyZeroEndpointTargetIsoBranchDataW786",
      "MetrizableClosedEmbeddingTargetHomologyZeroEndpointTargetIsoBranchDataW786",
      "closedMapTargetIsoDataOfTargetHomologyZeroEndpointW786",
      "closedEmbeddingTargetIsoDataOfTargetHomologyZeroEndpointW786",
      "productEvidence_of_closedMapTargetHomologyZeroEndpointRouteW786",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroEndpointRouteW786",
      "targetHomologyZeroEndpointTargetIsoProductRouteInputNamesW786",
      "targetHomologyZeroEndpointTargetIsoProductRouteInputNamesW786_count"]
  transportResult :=
    "proved: target homology-zero realization, homology existence, and endpoint\
      topology supply W784's target-isomorphism input"
  closedMapResult :=
    "proved: closed-map target homology-zero endpoint branch data feeds W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero endpoint branch data feeds\
      W784"
  replacedInputs :=
    ["exact-acyclic homotopy-object target ExactAt realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct Metrizable exact-at endpoint-strict topology data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW786TargetHomologyZeroEndpointRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroEndpointTargetIsoRouteStateW786;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
