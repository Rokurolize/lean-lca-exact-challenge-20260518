import LeanLCAExactChallenge.Derived.TargetHomologyZeroEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W787 feeds W784 by replacing W786's endpoint-strict topology premise with
W667 `ExactAt`-conditioned endpoint topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W787 target homology-zero payload for exact-acyclic homotopy objects. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW787
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i) :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW786
    hasHomology

/--
W787 turns target homology-zero realization data plus conditioned endpoint
topology into W784's target-isomorphism realization input.
-/
theorem targetIsoRealizationOfTargetHomologyZeroConditionedEndpointW787
    (hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i)
    (conditionedEndpointTopology :
      MetrizableExactAtEndpointConditionedTopologyInputs)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW787
        hasHomology) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm, hZero⟩
  let H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
    Dbounded.homologyDetection_of_endpointConditionedTopology_w667
      hasHomology conditionedEndpointTopology
  exact
    ⟨K, L, Lzero, f, e₁, e₃, eL, comm,
      H.exactAcyclic_of_isZero_homology Lzero hZero⟩

/--
W787 closed-map branch data using conditioned endpoint topology instead of
W786's unconditional endpoint-strict topology input.
-/
structure
    MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW787
      hasHomology
  conditionedEndpointTopology :
    MetrizableExactAtEndpointConditionedTopologyInputs
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
W787 closed-embedding branch data using conditioned endpoint topology instead
of W786's unconditional endpoint-strict topology input.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  hasHomology :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW787
      hasHomology
  conditionedEndpointTopology :
    MetrizableExactAtEndpointConditionedTopologyInputs
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

/-- W787 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroConditionedEndpointW787
      data.hasHomology data.conditionedEndpointTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W787 closed-embedding branch converted to W784 branch data. -/
noncomputable def
    closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetHomologyZeroConditionedEndpointW787
      data.hasHomology data.conditionedEndpointTopology
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W787 closed-map product evidence through target homology-zero conditioned data. -/
noncomputable def productEvidence_of_closedMapTargetHomologyZeroConditionedRouteW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787 data)

/-- W787 closed-embedding product evidence through conditioned endpoint data. -/
noncomputable def
    productEvidence_of_closedEmbeddingTargetHomologyZeroConditionedRouteW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
      data)

/-- W787 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787 data)

/-- W787 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
      data)

/-- W787 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787 data)

/-- W787 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
      data)

/-- W787 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787 data)

/--
W787 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetHomologyZeroConditionedW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
      data)

/-- W787 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroConditionedStableBoundaryW787
    (data :
      MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetIsoRealizationStableBoundaryW784
    (closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787 data)

/-- W787 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroConditionedStableBoundaryW787
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetIsoRealizationStableBoundaryW784
    (closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787
      data)

/-- W787 input names after replacing W786's unconditional endpoint topology. -/
def targetHomologyZeroConditionedEndpointProductRouteInputNamesW787 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "ExactAt-conditioned endpoint topology data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetHomologyZeroConditionedEndpointProductRouteInputNamesW787_count :
    targetHomologyZeroConditionedEndpointProductRouteInputNamesW787.length =
      10 :=
  rfl

/-- Current checked W787 state. -/
structure MetrizableTargetHomologyZeroConditionedEndpointRouteStateW787 :
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

/-- Current checked W787 state for the conditioned endpoint route. -/
def currentMetrizableTargetHomologyZeroConditionedEndpointRouteStateW787 :
    MetrizableTargetHomologyZeroConditionedEndpointRouteStateW787
    where
  seed := "w787-target-homology-zero-conditioned-endpoint-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW787",
      "targetIsoRealizationOfTargetHomologyZeroConditionedEndpointW787",
      "MetrizableClosedMapTargetHomologyZeroConditionedEndpointBranchDataW787",
      "MetrizableClosedEmbeddingTargetHomologyZeroConditionedEndpointBranchDataW787",
      "closedMapTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787",
      "closedEmbeddingTargetIsoDataOfTargetHomologyZeroConditionedEndpointW787",
      "productEvidence_of_closedMapTargetHomologyZeroConditionedRouteW787",
      "productEvidence_of_closedEmbeddingTargetHomologyZeroConditionedRouteW787",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroConditionedW787",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroConditionedW787",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroConditionedW787",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroConditionedW787",
      "acceptedStableOfClosedMapTargetHomologyZeroConditionedW787",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroConditionedW787",
      "boundedDerivedOfClosedMapTargetHomologyZeroConditionedStableBoundaryW787",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroConditionedStableBoundaryW787",
      "targetHomologyZeroConditionedEndpointProductRouteInputNamesW787",
      "targetHomologyZeroConditionedEndpointProductRouteInputNamesW787_count"]
  transportResult :=
    "proved: W667 conditioned endpoint topology supplies W784's\
      target-isomorphism input from target homology-zero data"
  stableBoundaryResult :=
    "proved: W787 target homology-zero conditioned endpoint branches pass the\
      W784/W783/W782/W781/W780/W779/W778/W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map target homology-zero conditioned endpoint data feeds W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target homology-zero conditioned endpoint data\
      feeds W784"
  replacedInputs :=
    ["unconditional endpoint-strict topology data for all complex degrees",
      "separate W784 target-isomorphism stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct ExactAt-conditioned endpoint topology data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW787TargetHomologyZeroConditionedRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroConditionedEndpointRouteStateW787;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
