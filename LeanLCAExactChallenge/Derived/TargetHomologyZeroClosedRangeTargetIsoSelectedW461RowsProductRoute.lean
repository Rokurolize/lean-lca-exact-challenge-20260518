import LeanLCAExactChallenge.Derived.TargetHomologyZeroEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W789 feeds W784's target-isomorphism route through W668 kernel/cokernel
homology detection derived from the W696 closed-range endpoint topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W789 target homology-zero payload, reusing the W786 payload shape. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW789
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i) :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
    hasHomology

/--
W789 derives the W668 kernel/cokernel-conditioned topology input from W696
closed-range endpoint topology.
-/
theorem targetIsoRealizationOfTargetHomologyZeroClosedRangeW789
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (closedRangeEndpointTopology :
      MetrizableExactAtClosedRangeEndpointTopologyInputsW696)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW789
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

/--
W789 closed-map branch data: W696 closed-range endpoint topology now supplies
the kernel/cokernel topology input.
-/
structure MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW789
      hasHomology
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
W789 closed-embedding branch data: W696 closed-range endpoint topology now
supplies the kernel/cokernel topology input.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW789
      hasHomology
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

/-- W789 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroClosedRangeW789
      data.hasHomology data.closedRangeEndpointTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W789 closed-embedding branch converted to W784 branch data. -/
noncomputable def
    closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroClosedRangeW789
      data.hasHomology data.closedRangeEndpointTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W789 closed-map product evidence through W784 using only W696 topology. -/
noncomputable def productEvidence_of_closedMapTargetHomologyZeroClosedRangeRouteW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-embedding product evidence through W784 using only W696 topology. -/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroClosedRangeRouteW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetHomologyZeroClosedRangeW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroClosedRangeW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetHomologyZeroClosedRangeW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroClosedRangeW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroClosedRangeW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/--
W789 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetHomologyZeroClosedRangeW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroClosedRangeStableBoundaryW789
    (data : MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetIsoRealizationStableBoundaryW784
    (closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroClosedRangeStableBoundaryW789
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetIsoRealizationStableBoundaryW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789 data)

/-- W789 input names after W696 supplies the kernel/cokernel topology input. -/
def targetHomologyZeroClosedRangeProductRouteInputNamesW789 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetHomologyZeroClosedRangeProductRouteInputNamesW789_count :
    targetHomologyZeroClosedRangeProductRouteInputNamesW789.length = 9 :=
  rfl

/-- Current checked W789 state. -/
structure MetrizableTargetHomologyZeroClosedRangeRouteStateW789 :
    Type where
  seed : String
  declarations : List String
  topologyProjectionResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W789 state for the closed-range target homology-zero route. -/
def currentMetrizableTargetHomologyZeroClosedRangeRouteStateW789 :
    MetrizableTargetHomologyZeroClosedRangeRouteStateW789
    where
  seed := "w789-target-homology-zero-closed-range-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW789",
      "targetIsoRealizationOfTargetHomologyZeroClosedRangeW789",
      "MetrizableClosedMapTargetHomologyZeroClosedRangeBranchDataW789",
      "MetrizableClosedEmbeddingTargetHomologyZeroClosedRangeBranchDataW789",
      "closedMapTargetIsoDataOfTargetHomologyZeroClosedRangeW789",
      "closedEmbeddingTargetIsoDataOfTargetHomologyZeroClosedRangeW789",
      "productEvidence_of_closedMapTargetHomologyZeroClosedRangeRouteW789",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroClosedRangeRouteW789",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroClosedRangeW789",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroClosedRangeW789",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroClosedRangeW789",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroClosedRangeW789",
      "acceptedStableOfClosedMapTargetHomologyZeroClosedRangeW789",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroClosedRangeW789",
      "boundedDerivedOfClosedMapTargetHomologyZeroClosedRangeStableBoundaryW789",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroClosedRangeStableBoundaryW789",
      "targetHomologyZeroClosedRangeProductRouteInputNamesW789",
      "targetHomologyZeroClosedRangeProductRouteInputNamesW789_count"]
  topologyProjectionResult :=
    "proved: W696 closed-range endpoint topology supplies W668's\
      kernel/cokernel-conditioned topology input"
  stableBoundaryResult :=
    "proved: W789 target homology-zero closed-range branches pass the\
      W784/W783/W782/W781/W780/W779/W778/W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map target homology-zero data plus W696 topology feed W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero data plus W696 topology feed\
      W784"
  replacedInputs :=
    ["direct MetrizableExactAtKernelCokernelConditionedTopologyInputs field",
      "separate W784 target-isomorphism stable-boundary branch input"]
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
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW789TargetHomologyZeroClosedRangeRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroClosedRangeRouteStateW789;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
