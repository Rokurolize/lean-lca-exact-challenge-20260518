import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStrictRealizationComparisonProductRoute
import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainStrictificationRoute

/-!
W1613 feeds W1612 after deriving its strict-realization data from the W847
selected-cochain route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-!
W1613 closed-map selected-cochain data converted to the W1612
strict-realization comparison surface.
-/
noncomputable def
    closedMapStrictRealizationComparisonDataOfSelectedCochainW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846 :=
  closedMapStrictRealizationDataOfSelectedCochainW847 data

/-!
W1613 closed-embedding selected-cochain data converted to the W1612
strict-realization comparison surface.
-/
noncomputable def
    closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846 :=
  closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data

/-!
W1613 closed-map product evidence after W847 derives W846 data from
selected-cochain strictification data.
-/
noncomputable def productEvidenceOfClosedMapSelectedCochainComparisonW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapStrictRealizationComparisonW1612
    (closedMapStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-embedding product evidence after W847 derives W846 data from
selected-cochain strictification data.
-/
noncomputable def
    productEvidenceOfClosedEmbeddingSelectedCochainComparisonW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingStrictRealizationComparisonW1612
    (closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-map direct finite-shape stable data through W1612.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedMapSelectedCochainComparisonW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapStrictRealizationComparisonW1612
    (closedMapStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-embedding direct finite-shape stable data through W1612.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingSelectedCochainComparisonW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingStrictRealizationComparisonW1612
    (closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-map stable-boundary inputs through W1612.
-/
noncomputable def
    stableBoundaryInputsOfClosedMapSelectedCochainComparisonW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapStrictRealizationComparisonW1612
    (closedMapStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-embedding stable-boundary inputs through W1612.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingSelectedCochainComparisonW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingStrictRealizationComparisonW1612
    (closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-map accepted stable evidence through W1612.
-/
noncomputable def acceptedStableOfClosedMapSelectedCochainComparisonW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapStrictRealizationComparisonW1612
    (closedMapStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-embedding accepted stable evidence through W1612.
-/
noncomputable def acceptedStableOfClosedEmbeddingSelectedCochainComparisonW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingStrictRealizationComparisonW1612
    (closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-map bounded derived package through W1612.
-/
noncomputable def boundedDerivedOfClosedMapSelectedCochainComparisonW1613
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapStrictRealizationComparisonW1612
    (closedMapStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
W1613 closed-embedding bounded derived package through W1612.
-/
noncomputable def boundedDerivedOfClosedEmbeddingSelectedCochainComparisonW1613
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingStrictRealizationComparisonW1612
    (closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613 data)

/-!
Top-level input names for the W1613 selected-cochain comparison route.
-/
def boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613 :
    List String :=
  ["W847 exact-acyclic selected-cochain strictification theorem",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613_count :
    boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613.length =
      2 :=
  rfl

/-!
Current checked W1613 selected-cochain comparison route state.
-/
structure MetrizableBoundarySourcePiZeroSelectedCochainComparisonRouteStateW1613 :
    Type where
  seed : String
  declarations : List String
  strictRealizationResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1613 state: W847 supplies the strict-realization data consumed
by W1612.
-/
def currentMetrizableBoundarySourcePiZeroSelectedCochainComparisonRouteStateW1613 :
    MetrizableBoundarySourcePiZeroSelectedCochainComparisonRouteStateW1613
    where
  seed := "w1613-boundary-source-pi-zero-selected-cochain-comparison-route"
  declarations :=
    ["closedMapStrictRealizationComparisonDataOfSelectedCochainW1613",
      "closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613",
      "productEvidenceOfClosedMapSelectedCochainComparisonW1613",
      "productEvidenceOfClosedEmbeddingSelectedCochainComparisonW1613",
      "directFiniteShapeStableDataOfClosedMapSelectedCochainComparisonW1613",
      "directFiniteShapeStableDataOfClosedEmbeddingSelectedCochainComparisonW1613",
      "stableBoundaryInputsOfClosedMapSelectedCochainComparisonW1613",
      "stableBoundaryInputsOfClosedEmbeddingSelectedCochainComparisonW1613",
      "acceptedStableOfClosedMapSelectedCochainComparisonW1613",
      "acceptedStableOfClosedEmbeddingSelectedCochainComparisonW1613",
      "boundedDerivedOfClosedMapSelectedCochainComparisonW1613",
      "boundedDerivedOfClosedEmbeddingSelectedCochainComparisonW1613",
      "boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613",
      "boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613_count"]
  strictRealizationResult :=
    "proved: W847 selected-cochain data supplies the W1612 strict-realization\
      branch data"
  closedMapResult :=
    "proved: closed-map W847 data feeds W1612 without a separate W783 strict\
      triangleh realization field"
  closedEmbeddingResult :=
    "proved: closed-embedding W847 data feeds W1612 without a separate W783\
      strict triangleh realization field"
  replacedInputs :=
    ["separate W783 exact-acyclic homotopy-object strict triangleh realization\
        data"]
  remainingInputs :=
    ["prove W847 exact-acyclic selected-cochain strictification for\
        MetrizableLCA",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1613BoundarySourcePiZeroSelectedCochainComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroSelectedCochainComparisonRouteStateW1613;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
