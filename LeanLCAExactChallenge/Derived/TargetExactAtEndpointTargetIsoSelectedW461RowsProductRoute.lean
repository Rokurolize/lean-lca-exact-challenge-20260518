import LeanLCAExactChallenge.Derived.TargetIsoRealizationTrianglehSelectedW461RowsProductRoute

/-!
W785 feeds W784 by replacing the target-isomorphism realization premise with
W663 target ExactAt realization data plus endpoint-strict topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W785 target ExactAt payload for exact-acyclic homotopy objects. -/
abbrev MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :
    Prop :=
  MetrizableExactAcyclicHomotopyObjectTrianglehIso13TargetExactAtPayloadW663

/--
W785 turns target ExactAt realization data plus endpoint-strict topology into
W784's target-isomorphism realization input.
-/
theorem targetIsoRealizationOfTargetExactAtEndpointW785
    (endpointTopology : MetrizableExactAtEndpointStrictTopologyInputs)
    (payload : MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :=
  metrizableExactAcyclicHomotopyObjectTrianglehIso13TargetIsoPayload_of_targetExactAtEndpointW663
    endpointTopology payload

/--
W785 closed-map branch data using target ExactAt realization data and
endpoint-strict topology instead of W784's target-isomorphism realization input.
-/
structure MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
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
W785 closed-embedding branch data using target ExactAt realization data and
endpoint-strict topology instead of W784's target-isomorphism realization input.
-/
structure MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
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

/-- W785 closed-map branch converted to W784 branch data. -/
noncomputable def closedMapTargetIsoDataOfTargetExactAtEndpointW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableClosedMapTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetExactAtEndpointW785
      data.endpointStrictTopology data.targetExactAtPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedMapRows := data.closedMapRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W785 closed-embedding branch converted to W784 branch data. -/
noncomputable def closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableClosedEmbeddingTargetIsoRealizationTrianglehBranchDataW784
    where
  comparisonIso := data.comparisonIso
  targetIsoRealization :=
    targetIsoRealizationOfTargetExactAtEndpointW785
      data.endpointStrictTopology data.targetExactAtPayload
  exactInputs := data.exactInputs
  rightOpenBoundary := data.rightOpenBoundary
  rightSurjectiveBoundary := data.rightSurjectiveBoundary
  selectedW461 := data.selectedW461
  closedEmbeddingRows := data.closedEmbeddingRows
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W785 closed-map product evidence through target ExactAt endpoint data. -/
noncomputable def productEvidence_of_closedMapTargetExactAtEndpointRouteW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetIsoRealizationRouteW784
    (closedMapTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-embedding product evidence through target ExactAt endpoint data. -/
noncomputable def
    productEvidence_of_closedEmbeddingTargetExactAtEndpointRouteW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetIsoRealizationRouteW784
    (closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetExactAtEndpointW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtEndpointW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetExactAtEndpointW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingTargetExactAtEndpointW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapTargetExactAtEndpointW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetIsoRealizationW784
    (closedMapTargetIsoDataOfTargetExactAtEndpointW785 data)

/--
W785 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetExactAtEndpointW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetIsoRealizationW784
    (closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapTargetExactAtEndpointStableBoundaryW785
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetIsoRealizationStableBoundaryW784
    (closedMapTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 closed-embedding branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetExactAtEndpointStableBoundaryW785
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetIsoRealizationStableBoundaryW784
    (closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785 data)

/-- W785 input names after replacing W784's target-isomorphism premise. -/
def targetExactAtEndpointTargetIsoProductRouteInputNamesW785 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exact-acyclic homotopy-object target ExactAt realization data",
    "Metrizable exact-at endpoint-strict topology data",
    "closed quotient-cover boundary for WPP limit right-open maps",
    "Epi boundary for WPP limit right-surjectivity",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput",
    "W696 closed-range endpoint topology data"]

theorem targetExactAtEndpointTargetIsoProductRouteInputNamesW785_count :
    targetExactAtEndpointTargetIsoProductRouteInputNamesW785.length = 9 :=
  rfl

/-- Current checked W785 state. -/
structure MetrizableTargetExactAtEndpointTargetIsoRouteStateW785 :
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

/-- Current checked W785 state for the target ExactAt endpoint route. -/
def currentMetrizableTargetExactAtEndpointTargetIsoRouteStateW785 :
    MetrizableTargetExactAtEndpointTargetIsoRouteStateW785
    where
  seed := "w785-target-exact-at-endpoint-target-iso-route"
  declarations :=
    ["MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785",
      "targetIsoRealizationOfTargetExactAtEndpointW785",
      "MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785",
      "MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785",
      "closedMapTargetIsoDataOfTargetExactAtEndpointW785",
      "closedEmbeddingTargetIsoDataOfTargetExactAtEndpointW785",
      "productEvidence_of_closedMapTargetExactAtEndpointRouteW785",
      "productEvidence_of_closedEmbeddingTargetExactAtEndpointRouteW785",
      "directFiniteShapeStableDataOfClosedMapTargetExactAtEndpointW785",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtEndpointW785",
      "stableBoundaryInputsOfClosedMapTargetExactAtEndpointW785",
      "stableBoundaryInputsOfClosedEmbeddingTargetExactAtEndpointW785",
      "acceptedStableOfClosedMapTargetExactAtEndpointW785",
      "acceptedStableOfClosedEmbeddingTargetExactAtEndpointW785",
      "boundedDerivedOfClosedMapTargetExactAtEndpointStableBoundaryW785",
      "boundedDerivedOfClosedEmbeddingTargetExactAtEndpointStableBoundaryW785",
      "targetExactAtEndpointTargetIsoProductRouteInputNamesW785",
      "targetExactAtEndpointTargetIsoProductRouteInputNamesW785_count"]
  transportResult :=
    "proved: target ExactAt realization plus endpoint topology supplies W784's\
      target-isomorphism input"
  stableBoundaryResult :=
    "proved: W785 target ExactAt endpoint branches pass the\
      W784/W783/W782/W781/W780/W779/W778/W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map target ExactAt endpoint branch data feeds W784"
  closedEmbeddingResult :=
    "proved: closed-embedding target ExactAt endpoint branch data feeds W784"
  replacedInputs :=
    ["exact-acyclic homotopy-object target-isomorphism realization data",
      "separate W784 target-isomorphism stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target ExactAt realization data",
      "construct Metrizable exact-at endpoint-strict topology data",
      "construct closed quotient-cover boundary data for WPP limit right-open maps",
      "construct Epi boundary data for WPP limit right-surjectivity",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW785TargetExactAtEndpointRoute_productSuccess :
    (have state :=
      currentMetrizableTargetExactAtEndpointTargetIsoRouteStateW785;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
