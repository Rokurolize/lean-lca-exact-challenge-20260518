import LeanLCAExactChallenge.Derived.TargetHomologyZeroConcreteLeafColimitProductRoute

/-!
W794 derives the target homology-zero route's global homology-existence input
from the universal left-right comparison isomorphism through W768.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W794 closed-map branch data without a separate global homology-existence field;
W768 derives homology existence from `comparisonIso`.
-/
structure MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W794 closed-embedding branch data without a separate global homology-existence
field; W768 derives homology existence from `comparisonIso`.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W794 closed-map branch converted directly to W774 normalized data. -/
noncomputable def closedMapNormalizedDataOfComparisonHomologyW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetHomologyZeroClosedRangeW792
      (hasHomology :=
        cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedMapConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W794 closed-embedding branch converted directly to W774 normalized data. -/
noncomputable def closedEmbeddingNormalizedDataOfComparisonHomologyW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetHomologyZeroClosedRangeW792
      (hasHomology :=
        cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
        data.exactInputs)
      data.targetHomologyZeroPayload
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData
  colimitStability :=
    colimitStabilityOfClosedEmbeddingConcreteLeafInputsW793 data.comparisonIso
      data.exactInputs
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/-- W794 closed-map product evidence through comparison-derived homology. -/
noncomputable def productEvidence_of_closedMapComparisonHomologyRouteW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-embedding product evidence through comparison-derived homology. -/
noncomputable def productEvidence_of_closedEmbeddingComparisonHomologyRouteW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfComparisonHomologyW794 data)

/--
W794 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfComparisonHomologyW794 data)

/-- W794 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroComparisonHomologyStableBoundaryW794
    (data :
      MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedMapNormalizedDataOfComparisonHomologyW794 data)

/--
W794 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroComparisonHomologyStableBoundaryW794
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedEmbeddingNormalizedDataOfComparisonHomologyW794 data)

/-- W794 input names after deriving global homology existence from comparison. -/
def targetHomologyZeroComparisonHomologyProductRouteInputNamesW794 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "target homology-zero realization data for exact-acyclic homotopy objects,\
      indexed by W768-derived homology existence"]

theorem targetHomologyZeroComparisonHomologyProductRouteInputNamesW794_count :
    targetHomologyZeroComparisonHomologyProductRouteInputNamesW794.length = 3 :=
  rfl

/-- Current checked W794 state. -/
structure MetrizableTargetHomologyZeroComparisonHomologyRouteStateW794 :
    Type where
  seed : String
  declarations : List String
  homologyResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W794 state for comparison-derived homology. -/
def currentMetrizableTargetHomologyZeroComparisonHomologyRouteStateW794 :
    MetrizableTargetHomologyZeroComparisonHomologyRouteStateW794
    where
  seed := "w794-target-homology-zero-comparison-homology-route"
  declarations :=
    ["MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794",
      "MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794",
      "closedMapNormalizedDataOfComparisonHomologyW794",
      "closedEmbeddingNormalizedDataOfComparisonHomologyW794",
      "productEvidence_of_closedMapComparisonHomologyRouteW794",
      "productEvidence_of_closedEmbeddingComparisonHomologyRouteW794",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroComparisonHomologyW794",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonHomologyW794",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794",
      "acceptedStableOfClosedMapTargetHomologyZeroComparisonHomologyW794",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroComparisonHomologyW794",
      "boundedDerivedOfClosedMapTargetHomologyZeroComparisonHomologyStableBoundaryW794",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroComparisonHomologyStableBoundaryW794",
      "targetHomologyZeroComparisonHomologyProductRouteInputNamesW794",
      "targetHomologyZeroComparisonHomologyProductRouteInputNamesW794_count"]
  homologyResult :=
    "proved: W768 derives global HasHomology from the universal comparison"
  stableBoundaryResult :=
    "proved: W794 target homology-zero comparison-homology branches pass the\
      W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map comparison-derived homology route feeds W774"
  closedEmbeddingResult :=
    "proved: closed-embedding comparison-derived homology route feeds W774"
  replacedInputs :=
    ["separate homology existence for all MetrizableLCA cochain complexes in\
      every degree",
      "separate W774 normalized direct-source stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data indexed by the\
        comparison-derived homology existence"]
  productSuccessClaimed := false

theorem currentW794TargetHomologyZeroComparisonHomologyRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroComparisonHomologyRouteStateW794;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
