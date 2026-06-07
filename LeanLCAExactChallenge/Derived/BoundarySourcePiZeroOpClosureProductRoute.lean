import LeanLCAExactChallenge.Derived.BoundaryDataEpiDirectComparisonRightLcaOpClosureProductRoute

/-!
W1603 feeds W775 by deriving WPP limit stability from the W716 boundary data
already carried by the W735 exact inputs.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1603 closed-map branch data without separate right-open or Epi
right-surjectivity fields; W735 `exactInputs.boundaryData` supplies WPP limit
stability through W716 source-pi-zero data.
-/
structure MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/--
W1603 closed-embedding branch data without separate right-open or Epi
right-surjectivity fields; W735 `exactInputs.boundaryData` supplies WPP limit
stability through W716 source-pi-zero data.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W1603 derives WPP limit stability from bundled W716 boundary data. -/
theorem limitStabilityOfBoundarySourcePiZeroOpClosureW1603
    (boundaryData : MetrizableWppLimitBoundaryDataW716) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_lcaRightSourceDifferenceCokernelPiZeroBoundary
    (Dbounded.metrizableWppLimitRightOpenLcaInput_of_closedQuotientCoverBoundary
      (rightOpenBoundary_of_boundaryDataW716 boundaryData))
    (sourcePiZeroBoundary_of_boundaryDataW716 boundaryData)

/-- W1603 closed-map branch converted to W775 WPP-op closure data. -/
noncomputable def closedMapOpClosureDataOfBoundarySourcePiZeroW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundarySourcePiZeroOpClosureW1603
      data.exactInputs.boundaryData
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1603 closed-embedding branch converted to W775 WPP-op closure data. -/
noncomputable def closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775 where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfBoundarySourcePiZeroOpClosureW1603
      data.exactInputs.boundaryData
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W1603 closed-map product evidence after deriving WPP limit stability. -/
noncomputable def productEvidence_of_closedMapBoundarySourcePiZeroOpClosureRouteW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapOpClosureNormalizedClosedRangeRouteW775
    (closedMapOpClosureDataOfBoundarySourcePiZeroW1603 data)

/--
W1603 closed-embedding product evidence after deriving WPP limit stability.
-/
noncomputable def
    productEvidence_of_closedEmbeddingBoundarySourcePiZeroOpClosureRouteW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingOpClosureNormalizedClosedRangeRouteW775
    (closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapOpClosureNormalizedClosedRangeW775
    (closedMapOpClosureDataOfBoundarySourcePiZeroW1603 data)

/--
W1603 closed-embedding branch passes the canonical accepted stable boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingOpClosureNormalizedClosedRangeW775
    (closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def boundedDerivedOfClosedMapBoundarySourcePiZeroOpClosureStableBoundaryW1603
    (data : MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapOpClosureNormalizedClosedRangeStableBoundaryW775
    (closedMapOpClosureDataOfBoundarySourcePiZeroW1603 data)

/--
W1603 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroOpClosureStableBoundaryW1603
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingOpClosureNormalizedClosedRangeStableBoundaryW775
    (closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603 data)

/-- W1603 input names after deriving WPP limit stability from W735 boundary data. -/
def boundarySourcePiZeroOpClosureProductRouteInputNamesW1603 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data and W735 exact-input fields",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem boundarySourcePiZeroOpClosureProductRouteInputNamesW1603_count :
    boundarySourcePiZeroOpClosureProductRouteInputNamesW1603.length = 5 :=
  rfl

/-- Current checked W1603 state. -/
structure MetrizableBoundarySourcePiZeroOpClosureRouteStateW1603 :
    Type where
  seed : String
  declarations : List String
  limitStabilityResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W1603 state for the W716 boundary/source-pi-zero route. -/
def currentMetrizableBoundarySourcePiZeroOpClosureRouteStateW1603 :
    MetrizableBoundarySourcePiZeroOpClosureRouteStateW1603
    where
  seed := "w1603-boundary-source-pi-zero-op-closure-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603",
      "limitStabilityOfBoundarySourcePiZeroOpClosureW1603",
      "closedMapOpClosureDataOfBoundarySourcePiZeroW1603",
      "closedEmbeddingOpClosureDataOfBoundarySourcePiZeroW1603",
      "productEvidence_of_closedMapBoundarySourcePiZeroOpClosureRouteW1603",
      "productEvidence_of_closedEmbeddingBoundarySourcePiZeroOpClosureRouteW1603",
      "directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroOpClosureW1603",
      "directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603",
      "stableBoundaryInputsOfClosedMapBoundarySourcePiZeroOpClosureW1603",
      "stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603",
      "acceptedStableOfClosedMapBoundarySourcePiZeroOpClosureW1603",
      "acceptedStableOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroOpClosureStableBoundaryW1603",
      "boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroOpClosureStableBoundaryW1603",
      "boundarySourcePiZeroOpClosureProductRouteInputNamesW1603",
      "boundarySourcePiZeroOpClosureProductRouteInputNamesW1603_count"]
  limitStabilityResult :=
    "proved: W716 right-open boundary plus source-pi-zero boundary supply WPP\
      limit stability without a separate Epi right-surjectivity field"
  stableBoundaryResult :=
    "proved: W1603 boundary/source-pi-zero WPP-op-closure branches pass the\
      W775/W774/W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data plus WPP-op closure feed W775 without\
      separate right-open or Epi right-surjectivity fields"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus WPP-op closure feed W775\
      without separate right-open or Epi right-surjectivity fields"
  replacedInputs :=
    ["separate MetrizableWppLimitRightOpenClosedQuotientCoverBoundary field",
      "separate Epi boundary for WPP limit right-surjectivity",
      "separate abstract WPP limit-stability field",
      "separate W1602 boundary-data/Epi direct-comparison right-LCA/WPP-op\
        closure stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch, including W716 boundary\
        data",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1603BoundarySourcePiZeroOpClosureRoute_productSuccess :
    (have state := currentMetrizableBoundarySourcePiZeroOpClosureRouteStateW1603;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
