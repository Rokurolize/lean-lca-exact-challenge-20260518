import LeanLCAExactChallenge.Derived.TargetHomologyZeroEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W788 feeds W784 by replacing W787's `ExactAt`-conditioned endpoint topology
premise with W668 kernel/cokernel-conditioned topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W788 target homology-zero payload for exact-acyclic homotopy objects. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW788
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i) :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
    hasHomology

/--
W788 turns target homology-zero realization data plus kernel/cokernel
conditioned topology into W784's target-isomorphism realization input.
-/
theorem targetIsoRealizationOfTargetHomologyZeroKernelCokernelW788
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW788
        hasHomology) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm, hZero⟩
  let H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
    Dbounded.homologyDetection_of_kernelCokernelConditionedTopology_w668
      hasHomology kernelCokernelTopology
  exact
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm,
      H.exactAcyclic_of_isZero_homology Lzero hZero⟩

/--
W788 closed-map branch data using kernel/cokernel-conditioned topology instead
of W787's conditioned endpoint topology input.
-/
structure MetrizableClosedMapTargetHomologyZeroKernelCokernelBranchDataW788 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW788
      hasHomology
  kernelCokernelTopology :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
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
W788 closed-embedding branch data using kernel/cokernel-conditioned topology
instead of W787's conditioned endpoint topology input.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroKernelCokernelBranchDataW788 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW788
      hasHomology
  kernelCokernelTopology :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
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

/-- W788 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetHomologyZeroKernelCokernelW788
    (data :
      MetrizableClosedMapTargetHomologyZeroKernelCokernelBranchDataW788) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroKernelCokernelW788
      data.hasHomology data.kernelCokernelTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W788 closed-embedding branch converted to W784 branch data. -/
noncomputable def
    closedEmbeddingTargetIsoDataOfTargetHomologyZeroKernelCokernelW788
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroKernelCokernelBranchDataW788) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroKernelCokernelW788
      data.hasHomology data.kernelCokernelTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W788 closed-map product evidence through target homology-zero kernel data. -/
noncomputable def productEvidence_of_closedMapTargetHomologyZeroKernelRouteW788
    (data :
      MetrizableClosedMapTargetHomologyZeroKernelCokernelBranchDataW788) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetHomologyZeroKernelCokernelW788 data)

/-- W788 closed-embedding product evidence through target homology-zero kernel data. -/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroKernelRouteW788
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroKernelCokernelBranchDataW788) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroKernelCokernelW788 data)

/-- W788 input names after replacing W787's conditioned endpoint topology. -/
def targetHomologyZeroKernelCokernelProductRouteInputNamesW788 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "kernel/cokernel-conditioned ExactAt topology data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetHomologyZeroKernelCokernelProductRouteInputNamesW788_count :
    targetHomologyZeroKernelCokernelProductRouteInputNamesW788.length = 10 :=
  rfl

/-- Current checked W788 state. -/
structure MetrizableTargetHomologyZeroKernelCokernelRouteStateW788 :
    Type where
  seed : String
  declarations : List String
  transportResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W788 state for the kernel/cokernel conditioned route. -/
def currentMetrizableTargetHomologyZeroKernelCokernelRouteStateW788 :
    MetrizableTargetHomologyZeroKernelCokernelRouteStateW788
    where
  seed := "w788-target-homology-zero-kernel-cokernel-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW788",
      "targetIsoRealizationOfTargetHomologyZeroKernelCokernelW788",
      "MetrizableClosedMapTargetHomologyZeroKernelCokernelBranchDataW788",
      "MetrizableClosedEmbeddingTargetHomologyZeroKernelCokernelBranchDataW788",
      "closedMapTargetIsoDataOfTargetHomologyZeroKernelCokernelW788",
      "closedEmbeddingTargetIsoDataOfTargetHomologyZeroKernelCokernelW788",
      "productEvidence_of_closedMapTargetHomologyZeroKernelRouteW788",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroKernelRouteW788",
      "targetHomologyZeroKernelCokernelProductRouteInputNamesW788",
      "targetHomologyZeroKernelCokernelProductRouteInputNamesW788_count"]
  transportResult :=
    "proved: W668 kernel/cokernel conditioned topology supplies W784's\
      target-isomorphism input from target homology-zero data"
  closedMapResult :=
    "proved: closed-map target homology-zero kernel/cokernel data feeds W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero kernel/cokernel data feeds\
      W784"
  replacedInputs :=
    ["ExactAt-conditioned endpoint topology data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct kernel/cokernel-conditioned ExactAt topology data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW788TargetHomologyZeroKernelRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroKernelCokernelRouteStateW788;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
