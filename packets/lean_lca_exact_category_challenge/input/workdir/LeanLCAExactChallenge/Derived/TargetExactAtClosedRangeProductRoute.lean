import LeanLCAExactChallenge.Derived.TargetIsoClosed2ProductRoute

/-!
W796 removes the W795 target-isomorphism realization premise when the target
ExactAt payload is paired with W735-derived closed-range endpoint topology.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W796 turns target ExactAt realization data plus closed-range endpoint topology
into W784's target-isomorphism realization input.
-/
theorem targetIsoRealizationOfTargetExactAtClosedRangeW796
    (closedRangeEndpointTopology :
      MetrizableExactAtClosedRangeEndpointTopologyInputsW696)
    (payload : MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 := by
  intro T hT h₁ h₃
  rcases payload hT h₁ h₃ with
    ⟨K, L, Lexact, f, e₁, e₃, eL, comm, hExactAt⟩
  exact
    ⟨K, L, Lexact, f, e₁, e₃, eL, comm,
      exactAcyclic_of_exactAt_metrizableLCA_of_kernelCokernelConditionedTopology
        (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
          closedRangeEndpointTopology)
        Lexact hExactAt⟩

/-- W796 derives W774's `Closed₂` input from target ExactAt closed-range data. -/
theorem exactClosed2OfTargetExactAtClosedRangeW796
    (closedRangeEndpointTopology :
      MetrizableExactAtClosedRangeEndpointTopologyInputsW696)
    (payload : MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785) :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  exactClosed2OfTargetIsoRealizationW795
    (targetIsoRealizationOfTargetExactAtClosedRangeW796
      closedRangeEndpointTopology payload)

/-- W796 closed-map branch data with target ExactAt closed-range realization. -/
structure MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W796 closed-embedding branch data with target ExactAt closed-range realization.
-/
structure MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W796 closed-map branch converted directly to W774 normalized data. -/
noncomputable def closedMapNormalizedDataOfTargetExactAtClosedRangeW796
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetExactAtClosedRangeW796
      (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
      data.targetExactAtPayload
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedMapConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W796 closed-embedding branch converted directly to W774 normalized data. -/
noncomputable def closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetExactAtClosedRangeW796
      (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
        data.exactInputs)
      data.targetExactAtPayload
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedEmbeddingConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/-- W796 closed-map product evidence through target ExactAt closed-range data. -/
noncomputable def productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796
    (data : MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfTargetExactAtClosedRangeW796 data)

/-!
W796 closed-embedding product evidence through target ExactAt closed-range data.
-/
noncomputable def
    productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796
    (data : MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796 data)

/-- W796 input names after replacing W795's target-isomorphism premise. -/
def targetExactAtClosedRangeProductRouteInputNamesW796 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object target ExactAt realization data"]

theorem targetExactAtClosedRangeProductRouteInputNamesW796_count :
    targetExactAtClosedRangeProductRouteInputNamesW796.length = 3 :=
  rfl

/-- Current checked W796 state. -/
structure MetrizableTargetExactAtClosedRangeRouteStateW796 : Type where
  seed : String
  declarations : List String
  targetIsoResult : String
  exactClosed2Result : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W796 state for the target ExactAt closed-range route. -/
def currentMetrizableTargetExactAtClosedRangeRouteStateW796 :
    MetrizableTargetExactAtClosedRangeRouteStateW796
    where
  seed := "w796-target-exact-at-closed-range-route"
  declarations :=
    ["targetIsoRealizationOfTargetExactAtClosedRangeW796",
      "exactClosed2OfTargetExactAtClosedRangeW796",
      "MetrizableClosedMapTargetExactAtClosedRangeBranchDataW796",
      "MetrizableClosedEmbeddingTargetExactAtClosedRangeBranchDataW796",
      "closedMapNormalizedDataOfTargetExactAtClosedRangeW796",
      "closedEmbeddingNormalizedDataOfTargetExactAtClosedRangeW796",
      "productEvidence_of_closedMapTargetExactAtClosedRangeRouteW796",
      "productEvidence_of_closedEmbeddingTargetExactAtClosedRangeRouteW796",
      "targetExactAtClosedRangeProductRouteInputNamesW796",
      "targetExactAtClosedRangeProductRouteInputNamesW796_count"]
  targetIsoResult :=
    "proved: W663/W785 target ExactAt payload plus W735-derived closed-range\
      endpoint topology supplies W784 target-isomorphism realization"
  exactClosed2Result :=
    "proved: target ExactAt closed-range data supplies W774 Closed2 through W795"
  closedMapResult :=
    "proved: closed-map target ExactAt closed-range route feeds W774"
  closedEmbeddingResult :=
    "proved: closed-embedding target ExactAt closed-range route feeds W774"
  replacedInputs :=
    ["exact-acyclic homotopy-object target-isomorphism realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target ExactAt realization data",
      "construct remaining Dbounded stable-infinity inputs"]
  productSuccessClaimed := false

theorem currentW796TargetExactAtClosedRangeRoute_productSuccess :
    (have state := currentMetrizableTargetExactAtClosedRangeRouteStateW796;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
