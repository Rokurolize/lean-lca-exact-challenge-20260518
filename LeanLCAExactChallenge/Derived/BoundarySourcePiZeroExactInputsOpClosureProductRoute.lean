import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroOpClosureProductRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroExactInputsClosedRangeProductRoute

/-!
W1604 feeds W1603 after deriving the W696 closed-range endpoint topology from
the W735 exact inputs.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1604 closed-map branch data without a separate W696 closed-range endpoint
topology field; W735 exact inputs supply W519 mapped-cokernel closedness and
W720 endpoint topology data.
-/
structure MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput

/--
W1604 closed-embedding branch data without a separate W696 closed-range
endpoint topology field; W735 exact inputs supply W519 mapped-cokernel
closedness and W720 endpoint topology data.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput

/-- W1604 closed-map branch converted to W1603 branch data. -/
noncomputable def closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableClosedMapBoundarySourcePiZeroOpClosureBranchDataW1603
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs

/-- W1604 closed-embedding branch converted to W1603 branch data. -/
noncomputable def
    closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroOpClosureBranchDataW1603
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  opExactAcyclicClosure := data.opExactAcyclicClosure
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 data.exactInputs

/--
W1604 closed-map product evidence after deriving both WPP limit stability and
closed-range endpoint topology from W735 exact inputs.
-/
noncomputable def
    productEvidence_of_closedMapBoundarySourcePiZeroExactInputsOpClosureRouteW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapBoundarySourcePiZeroOpClosureRouteW1603
    (closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/--
W1604 closed-embedding product evidence after deriving both WPP limit stability
and closed-range endpoint topology from W735 exact inputs.
-/
noncomputable def
    productEvidence_of_closedEmbeddingBoundarySourcePiZeroExactInputsOpClosureRouteW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingBoundarySourcePiZeroOpClosureRouteW1603
    (closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-map branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-embedding branch converted to the W769 stable-data surface. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-map branch as canonical stable-instance boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-embedding branch as canonical stable-instance boundary inputs. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-map branch passes the canonical accepted stable boundary gate. -/
noncomputable def acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroOpClosureW1603
    (closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/--
W1604 closed-embedding branch passes the canonical accepted stable boundary
gate.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingBoundarySourcePiZeroOpClosureW1603
    (closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/-- W1604 closed-map branch produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604
    (data :
      MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroOpClosureStableBoundaryW1603
    (closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

/--
W1604 closed-embedding branch produces the canonical stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroOpClosureStableBoundaryW1603
    (closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604 data)

def boundarySourcePiZeroExactInputsOpClosureProductRouteInputNamesW1604 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "WPP-op exact-acyclic colimit closure"]

theorem boundarySourcePiZeroExactInputsOpClosureProductRouteInputNamesW1604_count :
    boundarySourcePiZeroExactInputsOpClosureProductRouteInputNamesW1604.length =
      4 :=
  rfl

/-- Current checked W1604 state. -/
structure MetrizableBoundarySourcePiZeroExactInputsOpClosureRouteStateW1604 :
    Type where
  seed : String
  declarations : List String
  closedRangeTopologyResult : String
  stableBoundaryResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1604 state for the W735 exact-input closed-range endpoint
topology route.
-/
def currentMetrizableBoundarySourcePiZeroExactInputsOpClosureRouteStateW1604 :
    MetrizableBoundarySourcePiZeroExactInputsOpClosureRouteStateW1604
    where
  seed := "w1604-boundary-source-pi-zero-exact-inputs-op-closure-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604",
      "closedMapBoundarySourcePiZeroOpClosureDataOfExactInputsW1604",
      "closedEmbeddingBoundarySourcePiZeroOpClosureDataOfExactInputsW1604",
      "productEvidence_of_closedMapBoundarySourcePiZeroExactInputsOpClosureRouteW1604",
      "productEvidence_of_closedEmbeddingBoundarySourcePiZeroExactInputsOpClosureRouteW1604",
      "directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604",
      "directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604",
      "stableBoundaryInputsOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604",
      "stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604",
      "acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604",
      "acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604",
      "boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604",
      "boundarySourcePiZeroExactInputsOpClosureProductRouteInputNamesW1604",
      "boundarySourcePiZeroExactInputsOpClosureProductRouteInputNamesW1604_count"]
  closedRangeTopologyResult :=
    "proved: W735 exactInputs supply W696 closed-range endpoint topology via\
      W519 mapped-cokernel closedness and W720 endpoint topology data"
  stableBoundaryResult :=
    "proved: W1604 exact-input WPP-op-closure branches pass the W1603/W775/W774\
      /W773/W769 canonical stable-boundary accepted gate"
  closedMapResult :=
    "proved: closed-map W735 branch data feeds W1603 without a separate W696\
      closed-range endpoint topology field"
  closedEmbeddingResult :=
    "proved: closed-embedding W735 branch data feeds W1603 without a separate\
      W696 closed-range endpoint topology field"
  replacedInputs :=
    ["separate W696 closed-range endpoint topology data",
      "separate W1603 boundary/source-pi-zero WPP-op-closure stable-boundary\
        branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP-op exact-acyclic colimit closure"]
  productSuccessClaimed := false

theorem currentW1604BoundarySourcePiZeroExactInputsOpClosureRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroExactInputsOpClosureRouteStateW1604;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
