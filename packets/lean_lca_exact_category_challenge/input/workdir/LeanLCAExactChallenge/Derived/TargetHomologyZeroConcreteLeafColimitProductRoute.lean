import LeanLCAExactChallenge.Derived.TargetHomologyZeroBoundarySourcePiZeroProductRoute

/-!
W793 derives the target homology-zero route's WPP colimit stability directly
from W735 concrete leaf data through W757, replacing the selected-W461 and
row-aware provider inputs used by W792.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open DirectWppOpColimitFiniteShapeTransfer

namespace Dbounded

/-- W793 closed-map W735 leaf data supply WPP colimit stability through W757. -/
theorem colimitStabilityOfClosedMapConcreteLeafInputsW793
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_exactAcyclicClosure
    (exactStableEvidence_of_closedMapLeftRightComparisonConcreteLeafInputsW758
      comparisonIso exactInputs).exactAcyclic

/--
W793 closed-embedding W735 leaf data supply WPP colimit stability through W757.
-/
theorem colimitStabilityOfClosedEmbeddingConcreteLeafInputsW793
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_exactAcyclicClosure
    (exactStableEvidence_of_closedEmbeddingLeftRightComparisonConcreteLeafInputsW758
      comparisonIso exactInputs).exactAcyclic

/--
W793 closed-map branch data with no separate selected-W461 or row-aware
provider fields; W735 leaf data supply both limit and colimit stability.
-/
structure MetrizableClosedMapTargetHomologyZeroConcreteLeafColimitBranchDataW793 :
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

/--
W793 closed-embedding branch data with no separate selected-W461 or row-aware
provider fields; W735 leaf data supply both limit and colimit stability.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroConcreteLeafColimitBranchDataW793 :
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

/-- W793 closed-map branch converted directly to W774 normalized data. -/
noncomputable def closedMapNormalizedDataOfConcreteLeafColimitW793
    (data :
      MetrizableClosedMapTargetHomologyZeroConcreteLeafColimitBranchDataW793) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetHomologyZeroClosedRangeW792
      (hasHomology := data.hasHomology)
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

/-- W793 closed-embedding branch converted directly to W774 normalized data. -/
noncomputable def closedEmbeddingNormalizedDataOfConcreteLeafColimitW793
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConcreteLeafColimitBranchDataW793) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetHomologyZeroClosedRangeW792
      (hasHomology := data.hasHomology)
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

/-- W793 closed-map product evidence through W735/W757 colimit stability. -/
noncomputable def productEvidence_of_closedMapConcreteLeafColimitRouteW793
    (data :
      MetrizableClosedMapTargetHomologyZeroConcreteLeafColimitBranchDataW793) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfConcreteLeafColimitW793 data)

/-- W793 closed-embedding product evidence through W735/W757 colimit stability. -/
noncomputable def productEvidence_of_closedEmbeddingConcreteLeafColimitRouteW793
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroConcreteLeafColimitBranchDataW793) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfConcreteLeafColimitW793 data)

/-- W793 input names after deriving colimit stability from W735 leaf data. -/
def targetHomologyZeroConcreteLeafColimitProductRouteInputNamesW793 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W717 relation data, W718 component provider, W519 closedness,\
      W720 endpoint topology, and W719 normalized data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree"]

theorem targetHomologyZeroConcreteLeafColimitProductRouteInputNamesW793_count :
    targetHomologyZeroConcreteLeafColimitProductRouteInputNamesW793.length = 4 :=
  rfl

/-- Current checked W793 state. -/
structure MetrizableTargetHomologyZeroConcreteLeafColimitRouteStateW793 :
    Type where
  seed : String
  declarations : List String
  colimitStabilityResult : String
  limitStabilityResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W793 state for the W735/W757 colimit route. -/
def currentMetrizableTargetHomologyZeroConcreteLeafColimitRouteStateW793 :
    MetrizableTargetHomologyZeroConcreteLeafColimitRouteStateW793
    where
  seed := "w793-target-homology-zero-concrete-leaf-colimit-route"
  declarations :=
    ["colimitStabilityOfClosedMapConcreteLeafInputsW793",
      "colimitStabilityOfClosedEmbeddingConcreteLeafInputsW793",
      "MetrizableClosedMapTargetHomologyZeroConcreteLeafColimitBranchDataW793",
      "MetrizableClosedEmbeddingTargetHomologyZeroConcreteLeafColimitBranchDataW793",
      "closedMapNormalizedDataOfConcreteLeafColimitW793",
      "closedEmbeddingNormalizedDataOfConcreteLeafColimitW793",
      "productEvidence_of_closedMapConcreteLeafColimitRouteW793",
      "productEvidence_of_closedEmbeddingConcreteLeafColimitRouteW793",
      "targetHomologyZeroConcreteLeafColimitProductRouteInputNamesW793",
      "targetHomologyZeroConcreteLeafColimitProductRouteInputNamesW793_count"]
  colimitStabilityResult :=
    "proved: W735 concrete leaf data supplies WPP colimit stability through\
      W757 exact-acyclic WPP-op colimit closure"
  limitStabilityResult :=
    "reused: W792 W716 boundary data supplies WPP limit stability"
  closedMapResult :=
    "proved: closed-map concrete-leaf colimit route feeds W774"
  closedEmbeddingResult :=
    "proved: closed-embedding concrete-leaf colimit route feeds W774"
  replacedInputs :=
    ["separate selected W461 provider field",
      "separate row-aware closed-map or closed-embedding provider field"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree"]
  productSuccessClaimed := false

theorem currentW793TargetHomologyZeroConcreteLeafColimitRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroConcreteLeafColimitRouteStateW793;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
