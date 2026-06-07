import LeanLCAExactChallenge.Derived.TargetHomologyZeroBoundaryDataExactInputsProductRoute

/-!
W792 derives the target homology-zero route's WPP limit stability directly
from W735/W716 boundary data, replacing the separate W780 Epi right-surjective
boundary input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open DirectWppOpColimitFiniteShapeTransfer

namespace Dbounded

/-- W792 W716 boundary data supply WPP limit stability through source-pi-zero. -/
theorem limitStabilityOfBoundaryDataW792
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_rightOpenClosedQuotientSourceBoundary
    Dbounded.metrizableWppLimitSourceDifferenceLcaInput_of_cokernelPiZeroBoundary
    (rightOpenBoundary_of_boundaryDataW716 boundaryData)
    (sourcePiZeroBoundary_of_boundaryDataW716 boundaryData)

/-- W792 closed-map selected-W461/row data supply WPP colimit stability. -/
theorem colimitStabilityOfClosedMapSelectedRowsW792
    (selectedW461 : WppOpSelectedW461ProviderW781)
    (closedMapRows : WppOpClosedMapRowsProviderW781) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    (opLeftClosedOfSelectedW461W781 selectedW461)
    (opSnakeOfClosedMapRowsW781 closedMapRows)

/-- W792 closed-embedding selected-W461/row data supply WPP colimit stability. -/
theorem colimitStabilityOfClosedEmbeddingSelectedRowsW792
    (selectedW461 : WppOpSelectedW461ProviderW781)
    (closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    (opLeftClosedOfSelectedW461W781 selectedW461)
    (opSnakeOfClosedEmbeddingRowsW781 closedEmbeddingRows)

/--
W792 turns target homology-zero realization data into the exact-acyclic
isomorphism-closure `Closed₂` input consumed by W774.
-/
theorem exactClosed2OfTargetHomologyZeroClosedRangeW792
    {hasHomology :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i}
    (closedRangeEndpointTopology :
      MetrizableExactAtClosedRangeEndpointTopologyInputsW696)
    (payload :
      MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
        hasHomology) :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  exactClosed2OfHomotopyObjectW782
    (homotopyObjectClosed2OfTrianglehRealizationW783
      (trianglehRealizationOfTargetIsoRealizationW784
        (targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
          hasHomology closedRangeEndpointTopology payload)))

/--
W792 closed-map branch data without separate right-open or Epi
right-surjectivity fields; W735/W716 boundary data supply limit stability.
-/
structure MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792 :
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
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781

/--
W792 closed-embedding branch data without separate right-open or Epi
right-surjectivity fields; W735/W716 boundary data supply limit stability.
-/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792 :
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
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/-- W792 closed-map branch converted directly to W774 normalized data. -/
noncomputable def closedMapNormalizedDataOfBoundarySourcePiZeroW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
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
    colimitStabilityOfClosedMapSelectedRowsW792 data.selectedW461
      data.closedMapRows
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W792 closed-embedding branch converted directly to W774 normalized data. -/
noncomputable def closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
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
    colimitStabilityOfClosedEmbeddingSelectedRowsW792 data.selectedW461
      data.closedEmbeddingRows
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/-- W792 closed-map product evidence through W716 source-pi-zero data. -/
noncomputable def productEvidence_of_closedMapBoundarySourcePiZeroRouteW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-embedding product evidence through W716 source-pi-zero data. -/
noncomputable def productEvidence_of_closedEmbeddingBoundarySourcePiZeroRouteW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def
    acceptedStableOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapNormalizedDirectSourceClosedRangeW774
    (closedMapNormalizedDataOfBoundarySourcePiZeroW792 data)

/--
W792 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingNormalizedDirectSourceClosedRangeW774
    (closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroBoundarySourcePiZeroStableBoundaryW792
    (data :
      MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedMapNormalizedDataOfBoundarySourcePiZeroW792 data)

/--
W792 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroStableBoundaryW792
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingNormalizedDirectSourceClosedRangeStableBoundaryW774
    (closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792 data)

/-- W792 input names after deriving limit stability from W716 boundary data. -/
def targetHomologyZeroBoundarySourcePiZeroProductRouteInputNamesW792 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 closedness, W720 endpoint topology, and W719 normalized data",
    "target homology-zero realization data for exact-acyclic homotopy objects",
    "homology exists for all MetrizableLCA cochain complexes in every degree",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput"]

theorem targetHomologyZeroBoundarySourcePiZeroProductRouteInputNamesW792_count :
    targetHomologyZeroBoundarySourcePiZeroProductRouteInputNamesW792.length = 6 :=
  rfl

/-- Current checked W792 state. -/
structure MetrizableTargetHomologyZeroBoundarySourcePiZeroRouteStateW792 :
    Type where
  seed : String
  declarations : List String
  limitStabilityResult : String
  exactClosed2Result : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W792 state for the W716 source-pi-zero boundary route. -/
def currentMetrizableTargetHomologyZeroBoundarySourcePiZeroRouteStateW792 :
    MetrizableTargetHomologyZeroBoundarySourcePiZeroRouteStateW792
    where
  seed := "w792-target-homology-zero-boundary-source-pi-zero-route"
  declarations :=
    ["limitStabilityOfBoundaryDataW792",
      "colimitStabilityOfClosedMapSelectedRowsW792",
      "colimitStabilityOfClosedEmbeddingSelectedRowsW792",
      "exactClosed2OfTargetHomologyZeroClosedRangeW792",
      "MetrizableClosedMapTargetHomologyZeroBoundarySourcePiZeroBranchDataW792",
      "MetrizableClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroBranchDataW792",
      "closedMapNormalizedDataOfBoundarySourcePiZeroW792",
      "closedEmbeddingNormalizedDataOfBoundarySourcePiZeroW792",
      "productEvidence_of_closedMapBoundarySourcePiZeroRouteW792",
      "productEvidence_of_closedEmbeddingBoundarySourcePiZeroRouteW792",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792",
      "acceptedStableOfClosedMapTargetHomologyZeroBoundarySourcePiZeroW792",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroW792",
      "boundedDerivedOfClosedMapTargetHomologyZeroBoundarySourcePiZeroStableBoundaryW792",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroBoundarySourcePiZeroStableBoundaryW792",
      "targetHomologyZeroBoundarySourcePiZeroProductRouteInputNamesW792",
      "targetHomologyZeroBoundarySourcePiZeroProductRouteInputNamesW792_count"]
  limitStabilityResult :=
    "proved: W716 boundary data supplies WPP limit stability through\
      right-open and source-pi-zero projections"
  exactClosed2Result :=
    "proved: target homology-zero realization data supplies W774 Closed2 input\
      through W790, W784, W783, and W782"
  stableBoundaryResult :=
    "proved: W792 target homology-zero boundary source-pi-zero branches pass\
      the W774/W773/W769 canonical stable-boundary gate"
  closedMapResult :=
    "proved: closed-map boundary source-pi-zero route feeds W774"
  closedEmbeddingResult :=
    "proved: closed-embedding boundary source-pi-zero route feeds W774"
  replacedInputs :=
    ["separate MetrizableWppLimitRightOpenClosedQuotientCoverBoundary field",
      "separate MetrizableWppLimitRightSurjectiveEpiBoundaryW780 field",
      "separate W774 normalized direct-source stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target homology-zero realization data",
      "construct homology existence for all MetrizableLCA cochain complexes in\
        every degree",
      "construct selected W461 provider data for WPP-op left closed-embedding",
      "construct row-aware closed-map or closed-embedding provider data for\
        WPP-op SnakeInput"]
  productSuccessClaimed := false

theorem currentW792TargetHomologyZeroBoundarySourcePiZeroRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroBoundarySourcePiZeroRouteStateW792;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
