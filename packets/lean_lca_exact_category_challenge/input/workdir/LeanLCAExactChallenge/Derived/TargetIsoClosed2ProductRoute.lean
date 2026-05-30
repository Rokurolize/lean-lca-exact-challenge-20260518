import LeanLCAExactChallenge.Derived.TargetHomologyZeroComparisonHomologyProductRoute

/-!
W795 removes the target homology-zero realization premise from the current
normalized route when the already-normalized W784 target-isomorphism
realization is available.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W795 derives W774's `Closed₂` input directly from the W784 target-isomorphism
realization, bypassing W664/W790 target homology-zero data.
-/
theorem exactClosed2OfTargetIsoRealizationW795
    (targetIsoRealization :
      MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784) :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  exactClosed2OfHomotopyObjectW782
    (homotopyObjectClosed2OfTrianglehRealizationW783
      (trianglehRealizationOfTargetIsoRealizationW784 targetIsoRealization))

/-- W795 closed-map branch data with W784 target-isomorphism realization. -/
structure MetrizableClosedMapTargetIsoClosed2BranchDataW795 : Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/-- W795 closed-embedding branch data with W784 target-isomorphism realization. -/
structure MetrizableClosedEmbeddingTargetIsoClosed2BranchDataW795 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W795 closed-map branch converted directly to W774 normalized data. -/
noncomputable def closedMapNormalizedDataOfTargetIsoClosed2W795
    (data : MetrizableClosedMapTargetIsoClosed2BranchDataW795) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetIsoRealizationW795 data.targetIsoRealization
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedMapConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W795 closed-embedding branch converted directly to W774 normalized data. -/
noncomputable def closedEmbeddingNormalizedDataOfTargetIsoClosed2W795
    (data : MetrizableClosedEmbeddingTargetIsoClosed2BranchDataW795) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetIsoRealizationW795 data.targetIsoRealization
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedEmbeddingConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/-- W795 closed-map product evidence through target-isomorphism `Closed₂`. -/
noncomputable def productEvidence_of_closedMapTargetIsoClosed2RouteW795
    (data : MetrizableClosedMapTargetIsoClosed2BranchDataW795) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfTargetIsoClosed2W795 data)

/-- W795 closed-embedding product evidence through target-isomorphism `Closed₂`. -/
noncomputable def productEvidence_of_closedEmbeddingTargetIsoClosed2RouteW795
    (data : MetrizableClosedEmbeddingTargetIsoClosed2BranchDataW795) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfTargetIsoClosed2W795 data)

/-- W795 input names after replacing target homology-zero realization data. -/
def targetIsoClosed2ProductRouteInputNamesW795 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object target-isomorphism realization data"]

theorem targetIsoClosed2ProductRouteInputNamesW795_count :
    targetIsoClosed2ProductRouteInputNamesW795.length = 3 :=
  rfl

/-- Current checked W795 state. -/
structure MetrizableTargetIsoClosed2RouteStateW795 : Type where
  seed : String
  declarations : List String
  exactClosed2Result : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W795 state for the target-isomorphism `Closed₂` route. -/
def currentMetrizableTargetIsoClosed2RouteStateW795 :
    MetrizableTargetIsoClosed2RouteStateW795
    where
  seed := "w795-target-iso-closed2-route"
  declarations :=
    ["exactClosed2OfTargetIsoRealizationW795",
      "MetrizableClosedMapTargetIsoClosed2BranchDataW795",
      "MetrizableClosedEmbeddingTargetIsoClosed2BranchDataW795",
      "closedMapNormalizedDataOfTargetIsoClosed2W795",
      "closedEmbeddingNormalizedDataOfTargetIsoClosed2W795",
      "productEvidence_of_closedMapTargetIsoClosed2RouteW795",
      "productEvidence_of_closedEmbeddingTargetIsoClosed2RouteW795",
      "targetIsoClosed2ProductRouteInputNamesW795",
      "targetIsoClosed2ProductRouteInputNamesW795_count"]
  exactClosed2Result :=
    "proved: W784 target-isomorphism realization supplies W774 Closed2 through\
      W783 and W782"
  closedMapResult :=
    "proved: closed-map target-isomorphism Closed2 route feeds W774"
  closedEmbeddingResult :=
    "proved: closed-embedding target-isomorphism Closed2 route feeds W774"
  replacedInputs :=
    ["target homology-zero realization data indexed by W768-derived homology\
      existence"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object target-isomorphism realization\
        data"]
  productSuccessClaimed := false

theorem currentW795TargetIsoClosed2Route_productSuccess :
    (have state := currentMetrizableTargetIsoClosed2RouteStateW795;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
