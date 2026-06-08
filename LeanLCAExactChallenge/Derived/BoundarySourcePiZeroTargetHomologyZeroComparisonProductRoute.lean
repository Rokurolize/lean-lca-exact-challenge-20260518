import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroComparisonBijectivityTargetExactAtProductRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroStrictRealizationLeftCalculusRoute

/-!
W1609 feeds W1608 after deriving its target ExactAt payload from the W839
target-homology-zero route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W1609 closed-map target-homology-zero data converted to W1608 data. -/
noncomputable def closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608
    where
  targetExactAtPayload := targetExactAtPayloadOfClosedMapTargetHomologyZeroW839
    data
  exactInputs := data.exactInputs

/-!
W1609 closed-embedding target-homology-zero data converted to W1608 data.
-/
noncomputable def
    closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608
    where
  targetExactAtPayload :=
    targetExactAtPayloadOfClosedEmbeddingTargetHomologyZeroW839 data
  exactInputs := data.exactInputs

/-!
W1609 closed-map product evidence after W839 derives the W1608 ExactAt
payload.
-/
noncomputable def productEvidenceOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapComparisonTargetExactAtW1608
    (closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-!
W1609 closed-embedding product evidence after W839 derives the W1608 ExactAt
payload.
-/
noncomputable def
    productEvidenceOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingComparisonTargetExactAtW1608
    (closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-map direct finite-shape stable data through W1608. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapComparisonW1608
    (closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-embedding direct finite-shape stable data through W1608. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingComparisonW1608
    (closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-map stable-boundary inputs through W1608. -/
noncomputable def
    stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapComparisonW1608
    (closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-embedding stable-boundary inputs through W1608. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingComparisonW1608
    (closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-map accepted stable evidence through W1608. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapComparisonTargetExactAtW1608
    (closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-embedding accepted stable evidence through W1608. -/
noncomputable def
    acceptedStableOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingComparisonTargetExactAtW1608
    (closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-map bounded derived package through W1608. -/
noncomputable def boundedDerivedOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapComparisonTargetExactAtW1608
    (closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- W1609 closed-embedding bounded derived package through W1608. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingComparisonTargetExactAtW1608
    (closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609 data)

/-- Top-level input names for the W1609 target-homology-zero route. -/
def boundarySourcePiZeroTargetHomologyZeroComparisonInputNamesW1609 :
    List String :=
  ["W790 target homology-zero payload for the W839 comparison-bijectivity\
      homology provider",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroTargetHomologyZeroComparisonInputNamesW1609_count :
    boundarySourcePiZeroTargetHomologyZeroComparisonInputNamesW1609.length =
      2 :=
  rfl

/-!
Current checked W1609 target-homology-zero route state.
-/
structure MetrizableBoundarySourcePiZeroTargetHomologyZeroComparisonRouteStateW1609 :
    Type where
  seed : String
  declarations : List String
  targetExactAtResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1609 state: W839 supplies the target ExactAt payload consumed
by W1608.
-/
def currentMetrizableBoundarySourcePiZeroTargetHomologyZeroComparisonRouteStateW1609 :
    MetrizableBoundarySourcePiZeroTargetHomologyZeroComparisonRouteStateW1609
    where
  seed := "w1609-boundary-source-pi-zero-target-homology-zero-comparison-route"
  declarations :=
    ["closedMapComparisonTargetExactAtDataOfTargetHomologyZeroW1609",
      "closedEmbeddingComparisonTargetExactAtDataOfTargetHomologyZeroW1609",
      "productEvidenceOfClosedMapTargetHomologyZeroComparisonW1609",
      "productEvidenceOfClosedEmbeddingTargetHomologyZeroComparisonW1609",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroComparisonW1609",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonW1609",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonW1609",
      "acceptedStableOfClosedMapTargetHomologyZeroComparisonW1609",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroComparisonW1609",
      "boundedDerivedOfClosedMapTargetHomologyZeroComparisonW1609",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroComparisonW1609",
      "boundarySourcePiZeroTargetHomologyZeroComparisonInputNamesW1609",
      "boundarySourcePiZeroTargetHomologyZeroComparisonInputNamesW1609_count"]
  targetExactAtResult :=
    "proved: W839 target homology-zero data supplies the W1608 target ExactAt\
      payload"
  closedMapResult :=
    "proved: closed-map W839 data feeds W1608 without a separate target\
      ExactAt payload field"
  closedEmbeddingResult :=
    "proved: closed-embedding W839 data feeds W1608 without a separate target\
      ExactAt payload field"
  replacedInputs :=
    ["separate exact-acyclic homotopy-object target ExactAt realization data"]
  remainingInputs :=
    ["construct the W790 target homology-zero payload for the W839\
        comparison-bijectivity homology provider",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1609BoundarySourcePiZeroTargetHomologyZeroComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroTargetHomologyZeroComparisonRouteStateW1609;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
