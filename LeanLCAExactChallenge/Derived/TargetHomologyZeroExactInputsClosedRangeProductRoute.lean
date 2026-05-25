import LeanLCAExactChallenge.Derived.TargetHomologyZeroEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W790 derives W789's closed-range endpoint topology from W735 exact-input
fields, then feeds the W784 target-isomorphism route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

/-- W790 target homology-zero payload, reusing the W786 payload shape. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i) :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
    hasHomology

/--
W790 uses W668 homology detection after W735 exact inputs have supplied W696
closed-range endpoint topology.
-/
theorem targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (closedRangeEndpointTopology :
      MetrizableExactAtClosedRangeEndpointTopologyInputsW696)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
        hasHomology) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm, hZero⟩
  let H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
    Dbounded.homologyDetection_of_kernelCokernelConditionedTopology_w668
      hasHomology
      (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
        closedRangeEndpointTopology)
  exact
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm,
      H.exactAcyclic_of_isZero_homology Lzero hZero⟩

/-- W790 derives W696 topology from closed-map W735 exact inputs. -/
def closedRangeEndpointTopologyOfClosedMapExactInputsW790
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696
    where
  closedRangeProvider :=
    closedRangeProvider_of_closedMapProvider_w519
      exactInputs.mappedCokernelClosedMapProvider
  closedEmbedding_of_exactAt :=
    fun K i _ =>
      endpointClosedEmbedding_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData K i
  openMap_of_exactAt :=
    fun K i _ =>
      endpointOpenMap_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData K i
  epi_of_exactAt :=
    endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
      exactInputs.endpointStrictTopologyData

/-- W790 derives W696 topology from closed-embedding W735 exact inputs. -/
def closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696
    where
  closedRangeProvider :=
    closedRangeProvider_of_closedEmbeddingProvider_w519
      exactInputs.mappedCokernelClosedEmbeddingProvider
  closedEmbedding_of_exactAt :=
    fun K i _ =>
      endpointClosedEmbedding_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData K i
  openMap_of_exactAt :=
    fun K i _ =>
      endpointOpenMap_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData K i
  epi_of_exactAt :=
    endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
      exactInputs.endpointStrictTopologyData

/--
W790 closed-map branch data without a separate W696 field; W735 exact inputs
carry the W519 and W720 data needed to assemble it.
-/
structure MetrizableClosedMapTargetHomologyZeroExactInputsClosedRangeBranchDataW790 :
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
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781

/--
W790 closed-embedding branch data without a separate W696 field; W735 exact
inputs carry the W519 and W720 data needed to assemble it.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroExactInputsClosedRangeBranchDataW790 :
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
  rightOpenBoundary :
    MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  rightSurjectiveBoundary :
    MetrizableWppLimitRightSurjectiveEpiBoundaryW780
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/-- W790 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790
    (data :
      MetrizableClosedMapTargetHomologyZeroExactInputsClosedRangeBranchDataW790) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
      data.hasHomology
      (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W790 closed-embedding branch converted to W784 branch data. -/
noncomputable def
    closedEmbeddingTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroExactInputsClosedRangeBranchDataW790) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
      data.hasHomology
      (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
        data.exactInputs)
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/-- W790 closed-map product evidence through W784 using W735-derived W696 data. -/
noncomputable def
    productEvidence_of_closedMapTargetHomologyZeroExactInputsClosedRangeRouteW790
    (data :
      MetrizableClosedMapTargetHomologyZeroExactInputsClosedRangeBranchDataW790) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790 data)

/-!
W790 closed-embedding product evidence through W784 using W735-derived W696
data.
-/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroExactInputsClosedRangeRouteW790
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroExactInputsClosedRangeBranchDataW790) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790
      data)

/-- W790 input names after deriving W696 from W735 exact inputs. -/
def targetHomologyZeroExactInputsClosedRangeProductRouteInputNamesW790 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W519 mapped\
      cokernel closedness and W720 endpoint topology data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput"]

theorem targetHomologyZeroExactInputsClosedRangeProductRouteInputNamesW790_count :
    targetHomologyZeroExactInputsClosedRangeProductRouteInputNamesW790.length =
      8 :=
  rfl

/-- Current checked W790 state. -/
structure MetrizableTargetHomologyZeroExactInputsClosedRangeRouteStateW790 :
    Type where
  seed : String
  declarations : List String
  topologyProjectionResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W790 state for the exact-inputs closed-range route. -/
def currentMetrizableTargetHomologyZeroExactInputsClosedRangeRouteStateW790 :
    MetrizableTargetHomologyZeroExactInputsClosedRangeRouteStateW790
    where
  seed := "w790-target-homology-zero-exact-inputs-closed-range-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790",
      "targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790",
      "closedRangeEndpointTopologyOfClosedMapExactInputsW790",
      "closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790",
      "MetrizableClosedMapTargetHomologyZeroExactInputsClosedRangeBranchDataW790",
      "MetrizableClosedEmbeddingTargetHomologyZeroExactInputsClosedRangeBranchDataW790",
      "closedMapTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790",
      "closedEmbeddingTargetIsoDataOfTargetHomologyZeroExactInputsClosedRangeW790",
      "productEvidence_of_closedMapTargetHomologyZeroExactInputsClosedRangeRouteW790",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroExactInputsClosedRangeRouteW790",
      "targetHomologyZeroExactInputsClosedRangeProductRouteInputNamesW790",
      "targetHomologyZeroExactInputsClosedRangeProductRouteInputNamesW790_count"]
  topologyProjectionResult :=
    "proved: W735 exactInputs supply W696 closed-range endpoint topology via\
      W519 mapped cokernel closedness and W720 endpoint topology data"
  closedMapResult :=
    "proved: closed-map target homology-zero exactInputs data feed W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero exactInputs data feed W784"
  replacedInputs :=
    ["separate W696 closed-range endpoint topology field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput"]
  productSuccessClaimed := false

theorem currentW790TargetHomologyZeroExactInputsClosedRangeRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroExactInputsClosedRangeRouteStateW790;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
