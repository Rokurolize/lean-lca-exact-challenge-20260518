import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsExactStableEvidenceRoute

/-!
W1606 feeds W1604 after deriving the WPP-op exact-acyclic closure input from
the W1605 exact/stable evidence route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W1606 closed-map branch data: W1605 supplies the WPP-op exact-acyclic closure,
so this surface keeps only the comparison, closed-two, and W735 exact inputs.
-/
structure MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W1606 closed-embedding branch data: W1605 supplies the WPP-op exact-acyclic
closure, so this surface keeps only the comparison, closed-two, and W735 exact
inputs.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W1606 closed-map data at the W1605 exact/stable surface. -/
noncomputable def closedMapExactStableDataW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableClosedMapBoundarySourcePiZeroExactInputsExactStableBranchDataW1605
    where
  comparisonIso := data.comparisonIso
  exactInputs := data.exactInputs

/-- W1606 closed-embedding data at the W1605 exact/stable surface. -/
noncomputable def closedEmbeddingExactStableDataW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsExactStableBranchDataW1605
    where
  comparisonIso := data.comparisonIso
  exactInputs := data.exactInputs

/-- W1606 closed-map branch converted to W1604 branch data. -/
noncomputable def closedMapOpClosureDataOfStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableClosedMapBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  opExactAcyclicClosure :=
    wppOpExactAcyclicClosureOfClosedMapBoundarySourcePiZeroExactInputsW1605
      (closedMapExactStableDataW1606 data)

/-- W1606 closed-embedding branch converted to W1604 branch data. -/
noncomputable def closedEmbeddingOpClosureDataOfStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureBranchDataW1604
    where
  comparisonIso := data.comparisonIso
  exactClosed2 := data.exactClosed2
  exactInputs := data.exactInputs
  opExactAcyclicClosure :=
    wppOpExactAcyclicClosureOfClosedEmbeddingBoundarySourcePiZeroExactInputsW1605
      (closedEmbeddingExactStableDataW1606 data)

/-- W1606 closed-map product evidence through W1604. -/
noncomputable def productEvidenceOfClosedMapStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapBoundarySourcePiZeroExactInputsOpClosureRouteW1604
    (closedMapOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-embedding product evidence through W1604. -/
noncomputable def productEvidenceOfClosedEmbeddingStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingBoundarySourcePiZeroExactInputsOpClosureRouteW1604
    (closedEmbeddingOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-map direct finite-shape stable data through W1604. -/
noncomputable def directFiniteShapeStableDataOfClosedMapStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedMapOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-embedding direct finite-shape stable data through W1604. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedEmbeddingOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-map stable-boundary inputs through W1604. -/
noncomputable def stableBoundaryInputsOfClosedMapStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedMapOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-embedding stable-boundary inputs through W1604. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedEmbeddingOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-map accepted stable evidence through W1604. -/
noncomputable def acceptedStableOfClosedMapStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedMapOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-embedding accepted stable evidence through W1604. -/
noncomputable def acceptedStableOfClosedEmbeddingStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureW1604
    (closedEmbeddingOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-map bounded derived package through W1604. -/
noncomputable def boundedDerivedOfClosedMapStableClosureW1606
    (data : MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604
    (closedMapOpClosureDataOfStableClosureW1606 data)

/-- W1606 closed-embedding bounded derived package through W1604. -/
noncomputable def boundedDerivedOfClosedEmbeddingStableClosureW1606
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroExactInputsOpClosureStableBoundaryW1604
    (closedEmbeddingOpClosureDataOfStableClosureW1606 data)

/-- Top-level input names for the W1606 stable-closure product route. -/
def boundarySourcePiZeroStableClosureProductRouteInputNamesW1606 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroStableClosureProductRouteInputNamesW1606_count :
    boundarySourcePiZeroStableClosureProductRouteInputNamesW1606.length =
      3 :=
  rfl

/-- Current checked W1606 stable-closure product-route state. -/
structure MetrizableBoundarySourcePiZeroStableClosureRouteStateW1606 : Type where
  seed : String
  declarations : List String
  stableClosureResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1606 state: W1605 supplies the WPP-op exact-acyclic closure
input for the W1604 stable-boundary route.
-/
def currentMetrizableBoundarySourcePiZeroStableClosureRouteStateW1606 :
    MetrizableBoundarySourcePiZeroStableClosureRouteStateW1606
    where
  seed := "w1606-boundary-source-pi-zero-stable-closure-product-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroStableClosureBranchDataW1606",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroStableClosureBranchDataW1606",
      "closedMapExactStableDataW1606",
      "closedEmbeddingExactStableDataW1606",
      "closedMapOpClosureDataOfStableClosureW1606",
      "closedEmbeddingOpClosureDataOfStableClosureW1606",
      "productEvidenceOfClosedMapStableClosureW1606",
      "productEvidenceOfClosedEmbeddingStableClosureW1606",
      "directFiniteShapeStableDataOfClosedMapStableClosureW1606",
      "directFiniteShapeStableDataOfClosedEmbeddingStableClosureW1606",
      "stableBoundaryInputsOfClosedMapStableClosureW1606",
      "stableBoundaryInputsOfClosedEmbeddingStableClosureW1606",
      "acceptedStableOfClosedMapStableClosureW1606",
      "acceptedStableOfClosedEmbeddingStableClosureW1606",
      "boundedDerivedOfClosedMapStableClosureW1606",
      "boundedDerivedOfClosedEmbeddingStableClosureW1606",
      "boundarySourcePiZeroStableClosureProductRouteInputNamesW1606",
      "boundarySourcePiZeroStableClosureProductRouteInputNamesW1606_count"]
  stableClosureResult :=
    "proved: W1605 exact/stable evidence supplies the WPP-op exact-acyclic\
      closure input needed by W1604"
  closedMapResult :=
    "proved: closed-map W1606 data feeds W1604 without a separate WPP-op\
      exact-acyclic closure field"
  closedEmbeddingResult :=
    "proved: closed-embedding W1606 data feeds W1604 without a separate WPP-op\
      exact-acyclic closure field"
  replacedInputs :=
    ["separate WPP-op exact-acyclic colimit closure input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1606BoundarySourcePiZeroStableClosureRoute_productSuccess :
    (have state := currentMetrizableBoundarySourcePiZeroStableClosureRouteStateW1606;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
