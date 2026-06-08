import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroTargetIsoComparisonProductRoute
import LeanLCAExactChallenge.Derived.IsoClosureDirectSourceStableRoute

/-!
W1611 feeds W1610 after deriving its target-isomorphism data from the W845
iso-closure route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-!
W1611 closed-map iso-closure data converted to the W1610 target-isomorphism
comparison surface.
-/
noncomputable def closedMapTargetIsoComparisonDataOfIsoClosureW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 :=
  closedMapTargetIsoDataOfIsoClosureW845 data

/-!
W1611 closed-embedding iso-closure data converted to the W1610
target-isomorphism comparison surface.
-/
noncomputable def
    closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 :=
  closedEmbeddingTargetIsoDataOfIsoClosureW845 data

/-!
W1611 closed-map product evidence after W845 derives W844 data from the
iso-closure route.
-/
noncomputable def productEvidenceOfClosedMapIsoClosureComparisonW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapTargetIsoComparisonW1610
    (closedMapTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-embedding product evidence after W845 derives W844 data from the
iso-closure route.
-/
noncomputable def productEvidenceOfClosedEmbeddingIsoClosureComparisonW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingTargetIsoComparisonW1610
    (closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-map direct finite-shape stable data through W1610.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedMapIsoClosureComparisonW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetIsoComparisonW1610
    (closedMapTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-embedding direct finite-shape stable data through W1610.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingIsoClosureComparisonW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetIsoComparisonW1610
    (closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-map stable-boundary inputs through W1610.
-/
noncomputable def stableBoundaryInputsOfClosedMapIsoClosureComparisonW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetIsoComparisonW1610
    (closedMapTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-embedding stable-boundary inputs through W1610.
-/
noncomputable def stableBoundaryInputsOfClosedEmbeddingIsoClosureComparisonW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetIsoComparisonW1610
    (closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-map accepted stable evidence through W1610.
-/
noncomputable def acceptedStableOfClosedMapIsoClosureComparisonW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetIsoComparisonW1610
    (closedMapTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-embedding accepted stable evidence through W1610.
-/
noncomputable def acceptedStableOfClosedEmbeddingIsoClosureComparisonW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetIsoComparisonW1610
    (closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-map bounded derived package through W1610.
-/
noncomputable def boundedDerivedOfClosedMapIsoClosureComparisonW1611
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetIsoComparisonW1610
    (closedMapTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
W1611 closed-embedding bounded derived package through W1610.
-/
noncomputable def boundedDerivedOfClosedEmbeddingIsoClosureComparisonW1611
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetIsoComparisonW1610
    (closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611 data)

/-!
Top-level input names for the W1611 iso-closure comparison route.
-/
def boundarySourcePiZeroIsoClosureComparisonInputNamesW1611 :
    List String :=
  ["W651 exact-acyclic iso-closure strict realization data",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroIsoClosureComparisonInputNamesW1611_count :
    boundarySourcePiZeroIsoClosureComparisonInputNamesW1611.length =
      2 :=
  rfl

/-!
Current checked W1611 iso-closure comparison route state.
-/
structure MetrizableBoundarySourcePiZeroIsoClosureComparisonRouteStateW1611 :
    Type where
  seed : String
  declarations : List String
  targetIsoResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1611 state: W845 supplies the target-isomorphism data consumed
by W1610.
-/
def currentMetrizableBoundarySourcePiZeroIsoClosureComparisonRouteStateW1611 :
    MetrizableBoundarySourcePiZeroIsoClosureComparisonRouteStateW1611
    where
  seed := "w1611-boundary-source-pi-zero-iso-closure-comparison-route"
  declarations :=
    ["closedMapTargetIsoComparisonDataOfIsoClosureW1611",
      "closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611",
      "productEvidenceOfClosedMapIsoClosureComparisonW1611",
      "productEvidenceOfClosedEmbeddingIsoClosureComparisonW1611",
      "directFiniteShapeStableDataOfClosedMapIsoClosureComparisonW1611",
      "directFiniteShapeStableDataOfClosedEmbeddingIsoClosureComparisonW1611",
      "stableBoundaryInputsOfClosedMapIsoClosureComparisonW1611",
      "stableBoundaryInputsOfClosedEmbeddingIsoClosureComparisonW1611",
      "acceptedStableOfClosedMapIsoClosureComparisonW1611",
      "acceptedStableOfClosedEmbeddingIsoClosureComparisonW1611",
      "boundedDerivedOfClosedMapIsoClosureComparisonW1611",
      "boundedDerivedOfClosedEmbeddingIsoClosureComparisonW1611",
      "boundarySourcePiZeroIsoClosureComparisonInputNamesW1611",
      "boundarySourcePiZeroIsoClosureComparisonInputNamesW1611_count"]
  targetIsoResult :=
    "proved: W845 iso-closure data supplies the W1610 target-isomorphism\
      branch data"
  closedMapResult :=
    "proved: closed-map W845 data feeds W1610 without a separate W784\
      target-isomorphism realization field"
  closedEmbeddingResult :=
    "proved: closed-embedding W845 data feeds W1610 without a separate W784\
      target-isomorphism realization field"
  replacedInputs :=
    ["separate W784 exact-acyclic homotopy-object target-isomorphism\
        realization data"]
  remainingInputs :=
    ["construct W651 exact-acyclic iso-closure strict realization data",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1611BoundarySourcePiZeroIsoClosureComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroIsoClosureComparisonRouteStateW1611;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
