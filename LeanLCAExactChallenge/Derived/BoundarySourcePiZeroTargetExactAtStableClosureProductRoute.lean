import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStableClosureProductRoute
import LeanLCAExactChallenge.Derived.TargetExactAtClosedRangeProductRoute

/-!
W1607 feeds W1606 after deriving its closed-two input from the W796 target
ExactAt closed-range route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1607 closed-map branch data: W796 supplies the closed-two input consumed by
W1606, so this surface keeps comparison data, target ExactAt payload, and W735
exact inputs.
-/
structure MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W1607 closed-embedding branch data: W796 supplies the closed-two input
consumed by W1606, so this surface keeps comparison data, target ExactAt
payload, and W735 exact inputs.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W1607 closed-map branch converted to W1606 stable-closure data. -/
noncomputable def closedMapStableClosureDataOfTargetExactAtW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetExactAtClosedRangeW796
      (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
      data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1607 closed-embedding branch converted to W1606 stable-closure data. -/
noncomputable def closedEmbeddingStableClosureDataOfTargetExactAtW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606
    where
  comparisonIso := data.comparisonIso
  exactClosed2 :=
    exactClosed2OfTargetExactAtClosedRangeW796
      (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
        data.exactInputs)
      data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1607 closed-map product evidence through W1606. -/
noncomputable def productEvidenceOfClosedMapTargetExactAtStableClosureW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapStableClosureW1606
    (closedMapStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-embedding product evidence through W1606. -/
noncomputable def
    productEvidenceOfClosedEmbeddingTargetExactAtStableClosureW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingStableClosureW1606
    (closedEmbeddingStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-map direct finite-shape stable data through W1606. -/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetExactAtW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapStableClosureW1606
    (closedMapStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-embedding direct finite-shape stable data through W1606. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingStableClosureW1606
    (closedEmbeddingStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-map stable-boundary inputs through W1606. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetExactAtW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapStableClosureW1606
    (closedMapStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-embedding stable-boundary inputs through W1606. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingTargetExactAtW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingStableClosureW1606
    (closedEmbeddingStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-map accepted stable evidence through W1606. -/
noncomputable def acceptedStableOfClosedMapTargetExactAtW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapStableClosureW1606
    (closedMapStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-embedding accepted stable evidence through W1606. -/
noncomputable def acceptedStableOfClosedEmbeddingTargetExactAtW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingStableClosureW1606
    (closedEmbeddingStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-map bounded derived package through W1606. -/
noncomputable def boundedDerivedOfClosedMapTargetExactAtW1607
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapStableClosureW1606
    (closedMapStableClosureDataOfTargetExactAtW1607 data)

/-- W1607 closed-embedding bounded derived package through W1606. -/
noncomputable def boundedDerivedOfClosedEmbeddingTargetExactAtW1607
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingStableClosureW1606
    (closedEmbeddingStableClosureDataOfTargetExactAtW1607 data)

/-- Top-level input names for the W1607 target-ExactAt stable-closure route. -/
def boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "exact-acyclic homotopy-object target ExactAt realization data",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607_count :
    boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607.length =
      3 :=
  rfl

/-- Current checked W1607 target-ExactAt stable-closure route state. -/
structure MetrizableBoundarySourcePiZeroTargetExactAtRouteStateW1607 : Type where
  seed : String
  declarations : List String
  closedTwoResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1607 state: W796 target ExactAt closed-range data supplies
the closed-two input consumed by W1606.
-/
def currentMetrizableBoundarySourcePiZeroTargetExactAtRouteStateW1607 :
    MetrizableBoundarySourcePiZeroTargetExactAtRouteStateW1607
    where
  seed := "w1607-boundary-source-pi-zero-target-exact-at-stable-closure-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607",
      "closedMapStableClosureDataOfTargetExactAtW1607",
      "closedEmbeddingStableClosureDataOfTargetExactAtW1607",
      "productEvidenceOfClosedMapTargetExactAtStableClosureW1607",
      "productEvidenceOfClosedEmbeddingTargetExactAtStableClosureW1607",
      "directFiniteShapeStableDataOfClosedMapTargetExactAtW1607",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW1607",
      "stableBoundaryInputsOfClosedMapTargetExactAtW1607",
      "stableBoundaryInputsOfClosedEmbeddingTargetExactAtW1607",
      "acceptedStableOfClosedMapTargetExactAtW1607",
      "acceptedStableOfClosedEmbeddingTargetExactAtW1607",
      "boundedDerivedOfClosedMapTargetExactAtW1607",
      "boundedDerivedOfClosedEmbeddingTargetExactAtW1607",
      "boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607",
      "boundarySourcePiZeroTargetExactAtStableClosureInputNamesW1607_count"]
  closedTwoResult :=
    "proved: W796 target ExactAt closed-range data supplies the closed-two\
      input needed by W1606"
  closedMapResult :=
    "proved: closed-map W1607 data feeds W1606 without a separate closed-two\
      field"
  closedEmbeddingResult :=
    "proved: closed-embedding W1607 data feeds W1606 without a separate\
      closed-two field"
  replacedInputs :=
    ["separate exactAcyclicHomotopyIsoClosure MetrizableLCA closed-two input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct exact-acyclic homotopy-object target ExactAt realization data",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1607BoundarySourcePiZeroTargetExactAtRoute_productSuccess :
    (have state := currentMetrizableBoundarySourcePiZeroTargetExactAtRouteStateW1607;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
