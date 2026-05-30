import LeanLCAExactChallenge.Derived.NormalizedDirectSourceClosedRangeProductRoute

/-!
W775 feeds WPP-op exact-acyclic closure into the W774 normalized direct-source
closed-range route, replacing the abstract WPP colimit-stability field.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W775 closed-map branch data using WPP-op exact-acyclic closure. -/
structure MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  opExactAcyclicClosure :
    MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W775 closed-embedding branch data using WPP-op exact-acyclic closure. -/
structure MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  opExactAcyclicClosure :
    MetrizableWppOpExactAcyclicClosureInput
  closedRangeEndpointTopology :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696

/-- W775 derives closed-map WPP colimit stability from WPP-op closure. -/
theorem colimitStabilityOfClosedMapOpClosureW775
    (data : MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
    data.opExactAcyclicClosure

/-- W775 derives closed-embedding WPP colimit stability from WPP-op closure. -/
theorem colimitStabilityOfClosedEmbeddingOpClosureW775
    (data :
      MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
    data.opExactAcyclicClosure

/-- W775 closed-map branch converted to W774 data. -/
noncomputable def closedMapNormalizedDataOfOpClosureW775
    (data : MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775) :
    MetrizableClosedMapNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := data.limitStability
  colimitStability := colimitStabilityOfClosedMapOpClosureW775 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W775 closed-embedding branch converted to W774 data. -/
noncomputable def closedEmbeddingNormalizedDataOfOpClosureW775
    (data :
      MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775) :
    MetrizableClosedEmbeddingNormalizedDirectSourceClosedRangeBranchDataW774
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  limitStability := data.limitStability
  colimitStability := colimitStabilityOfClosedEmbeddingOpClosureW775 data
  closedRangeEndpointTopology := data.closedRangeEndpointTopology

/-- W775 closed-map product evidence through WPP-op closure data. -/
noncomputable def productEvidence_of_closedMapOpClosureNormalizedClosedRangeRouteW775
    (data : MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapNormalizedDirectSourceClosedRangeRouteW774
    (closedMapNormalizedDataOfOpClosureW775 data)

/-- W775 closed-embedding product evidence through WPP-op closure data. -/
noncomputable def
    productEvidence_of_closedEmbeddingOpClosureNormalizedClosedRangeRouteW775
    (data :
      MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingNormalizedDirectSourceClosedRangeRouteW774
    (closedEmbeddingNormalizedDataOfOpClosureW775 data)

/-- W775 input names after WPP-op closure supplies WPP colimit stability. -/
def opClosureNormalizedClosedRangeProductRouteInputNamesW775 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP limit stability for WalkingParallelPair",
    "WPP-op exact-acyclic colimit closure",
    "W696 closed-range endpoint topology data"]

theorem opClosureNormalizedClosedRangeProductRouteInputNamesW775_count :
    opClosureNormalizedClosedRangeProductRouteInputNamesW775.length = 6 :=
  rfl

/-- Current checked W775 state. -/
structure MetrizableOpClosureNormalizedClosedRangeProductRouteStateW775 :
    Type where
  seed : String
  declarations : List String
  opClosureResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W775 state for WPP-op-closure closed-range routes. -/
def currentMetrizableOpClosureNormalizedClosedRangeProductRouteSupportStateW775 :
    MetrizableOpClosureNormalizedClosedRangeProductRouteStateW775
    where
  seed := "w775-op-closure-normalized-closed-range-product-route"
  declarations :=
    ["MetrizableClosedMapOpClosureNormalizedClosedRangeBranchDataW775",
      "MetrizableClosedEmbeddingOpClosureNormalizedClosedRangeBranchDataW775",
      "colimitStabilityOfClosedMapOpClosureW775",
      "colimitStabilityOfClosedEmbeddingOpClosureW775",
      "closedMapNormalizedDataOfOpClosureW775",
      "closedEmbeddingNormalizedDataOfOpClosureW775",
      "productEvidence_of_closedMapOpClosureNormalizedClosedRangeRouteW775",
      "productEvidence_of_closedEmbeddingOpClosureNormalizedClosedRangeRouteW775",
      "opClosureNormalizedClosedRangeProductRouteInputNamesW775",
      "opClosureNormalizedClosedRangeProductRouteInputNamesW775_count"]
  opClosureResult :=
    "proved: WPP-op exact-acyclic closure supplies the W774 colimit-stability\
      field"
  closedMapResult :=
    "proved: closed-map W735 branch data plus WPP-op closure feed the W774 route"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data plus WPP-op closure feed the W774\
      route"
  replacedInputs :=
    ["abstract WPP colimit-stability field for WalkingParallelPair"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP limit stability for WalkingParallelPair",
      "construct WPP-op exact-acyclic colimit closure",
      "construct W696 closed-range endpoint topology data"]
  productSuccessClaimed := false

theorem currentW775OpClosureNormalizedClosedRangeRoute_productSuccess :
    (let state :=
      currentMetrizableOpClosureNormalizedClosedRangeProductRouteSupportStateW775;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
