import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroTargetExactAtStableClosureProductRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute
import LeanLCAExactChallenge.Derived.TargetExactAtDirectSourceStableRoute

/-!
W1608 feeds W1607 after deriving its universal comparison-isomorphism input
from the W831 comparison-bijectivity route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W1608 closed-map branch data: W831 supplies the universal comparison
isomorphism consumed by W1607, leaving target ExactAt payload and W735 exact
inputs.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608 :
    Type 2 where
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/--
W1608 closed-embedding branch data: W831 supplies the universal comparison
isomorphism consumed by W1607, leaving target ExactAt payload and W735 exact
inputs.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608 :
    Type 2 where
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W1608 closed-map branch converted to W1607 target-ExactAt data. -/
noncomputable def closedMapTargetExactAtDataOfComparisonBijectivityW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableClosedMapBoundarySourcePiZeroTargetExactAtBranchDataW1607
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1608 closed-embedding branch converted to W1607 target-ExactAt data. -/
noncomputable def closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroTargetExactAtBranchDataW1607
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1608 closed-map branch converted to W843 direct-source data. -/
noncomputable def closedMapTargetExactAtDirectSourceDataOfComparisonW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843 where
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1608 closed-embedding branch converted to W843 direct-source data. -/
noncomputable def closedEmbeddingTargetExactAtDirectSourceDataOfComparisonW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843 where
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W1608 closed-map product evidence through W1607. -/
noncomputable def productEvidenceOfClosedMapComparisonTargetExactAtW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapTargetExactAtStableClosureW1607
    (closedMapTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-embedding product evidence through W1607. -/
noncomputable def productEvidenceOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingTargetExactAtStableClosureW1607
    (closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-map direct finite-shape stable data through W1607. -/
noncomputable def directFiniteShapeStableDataOfClosedMapComparisonW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetExactAtW1607
    (closedMapTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-embedding direct finite-shape stable data through W1607. -/
noncomputable def directFiniteShapeStableDataOfClosedEmbeddingComparisonW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW1607
    (closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-map stable-boundary inputs through W1607. -/
noncomputable def stableBoundaryInputsOfClosedMapComparisonW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetExactAtW1607
    (closedMapTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-embedding stable-boundary inputs through W1607. -/
noncomputable def stableBoundaryInputsOfClosedEmbeddingComparisonW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetExactAtW1607
    (closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608 data)

/--
W1608 closed-map data as canonical direct-localization boundary inputs through
W843/W842.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapComparisonTargetExactAtW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedMapStableInstanceBoundaryDirectLocalizationInputsOfTargetHomologyZeroW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843
      (closedMapTargetExactAtDirectSourceDataOfComparisonW1608 data))

/--
W1608 closed-embedding data as canonical direct-localization boundary inputs
through W843/W842.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfTargetHomologyZeroW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
      (closedEmbeddingTargetExactAtDirectSourceDataOfComparisonW1608 data))

/-- W1608 closed-map accepted stable evidence through W1607. -/
noncomputable def acceptedStableOfClosedMapComparisonTargetExactAtW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetExactAtW1607
    (closedMapTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-embedding accepted stable evidence through W1607. -/
noncomputable def acceptedStableOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetExactAtW1607
    (closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608 data)

/--
W1608 closed-map accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedMapComparisonTargetExactAtDirectLocalizationBoundaryW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapComparisonTargetExactAtW1608
      data)

/--
W1608 closed-embedding accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingComparisonTargetExactAtDirectLocalizationBoundaryW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingComparisonTargetExactAtW1608
      data)

/-- W1608 closed-map bounded derived package through W1607. -/
noncomputable def boundedDerivedOfClosedMapComparisonTargetExactAtW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetExactAtW1607
    (closedMapTargetExactAtDataOfComparisonBijectivityW1608 data)

/-- W1608 closed-embedding bounded derived package through W1607. -/
noncomputable def boundedDerivedOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetExactAtW1607
    (closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608 data)

/--
W1608 closed-map bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedMapComparisonTargetExactAtDirectLocalizationBoundaryW1608
    (data :
      MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapComparisonTargetExactAtW1608
      data)

/--
W1608 closed-embedding bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingComparisonTargetExactAtDirectLocalizationBoundaryW1608
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingComparisonTargetExactAtW1608
      data)

/-- Top-level input names for the W1608 comparison-bijectivity route. -/
def boundarySourcePiZeroComparisonTargetExactAtInputNamesW1608 :
    List String :=
  ["exact-acyclic homotopy-object target ExactAt realization data",
    "W735 closed-map or closed-embedding branch data, including W716 boundary\
      data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]

theorem boundarySourcePiZeroComparisonTargetExactAtInputNamesW1608_count :
    boundarySourcePiZeroComparisonTargetExactAtInputNamesW1608.length =
      2 :=
  rfl

/-- Current checked W1608 comparison-bijectivity target-ExactAt route state. -/
structure MetrizableBoundarySourcePiZeroComparisonRouteStateW1608 : Type where
  seed : String
  declarations : List String
  comparisonResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1608 state: W831 supplies the universal comparison-isomorphism
input consumed by W1607.
-/
def currentMetrizableBoundarySourcePiZeroComparisonRouteStateW1608 :
    MetrizableBoundarySourcePiZeroComparisonRouteStateW1608
    where
  seed := "w1608-boundary-source-pi-zero-comparison-target-exact-at-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608",
      "closedMapTargetExactAtDataOfComparisonBijectivityW1608",
      "closedEmbeddingTargetExactAtDataOfComparisonBijectivityW1608",
      "closedMapTargetExactAtDirectSourceDataOfComparisonW1608",
      "closedEmbeddingTargetExactAtDirectSourceDataOfComparisonW1608",
      "productEvidenceOfClosedMapComparisonTargetExactAtW1608",
      "productEvidenceOfClosedEmbeddingComparisonTargetExactAtW1608",
      "directFiniteShapeStableDataOfClosedMapComparisonW1608",
      "directFiniteShapeStableDataOfClosedEmbeddingComparisonW1608",
      "stableBoundaryInputsOfClosedMapComparisonW1608",
      "stableBoundaryInputsOfClosedEmbeddingComparisonW1608",
      "directLocalizationBoundaryInputsOfClosedMapComparisonTargetExactAtW1608",
      "directLocalizationBoundaryInputsOfClosedEmbeddingComparisonTargetExactAtW1608",
      "acceptedStableOfClosedMapComparisonTargetExactAtW1608",
      "acceptedStableOfClosedEmbeddingComparisonTargetExactAtW1608",
      "acceptedStableOfClosedMapComparisonTargetExactAtDirectLocalizationBoundaryW1608",
      "acceptedStableOfClosedEmbeddingComparisonTargetExactAtDirectLocalizationBoundaryW1608",
      "boundedDerivedOfClosedMapComparisonTargetExactAtW1608",
      "boundedDerivedOfClosedEmbeddingComparisonTargetExactAtW1608",
      "boundedDerivedOfClosedMapComparisonTargetExactAtDirectLocalizationBoundaryW1608",
      "boundedDerivedOfClosedEmbeddingComparisonTargetExactAtDirectLocalizationBoundaryW1608",
      "boundarySourcePiZeroComparisonTargetExactAtInputNamesW1608",
      "boundarySourcePiZeroComparisonTargetExactAtInputNamesW1608_count"]
  comparisonResult :=
    "proved: W831 comparison-bijectivity supplies the universal comparison\
      isomorphism needed by W1607"
  closedMapResult :=
    "proved: closed-map W1608 data feeds W1607 without a separate comparison\
      field and exposes W843/W842 canonical direct-localization boundary inputs"
  closedEmbeddingResult :=
    "proved: closed-embedding W1608 data feeds W1607 without a separate\
      comparison field and exposes W843/W842 canonical direct-localization\
      boundary inputs"
  replacedInputs :=
    ["separate universal left-right comparison isomorphism input"]
  remainingInputs :=
    ["construct exact-acyclic homotopy-object target ExactAt realization data",
      "construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data"]
  productSuccessClaimed := false

theorem currentW1608BoundarySourcePiZeroComparisonRoute_productSuccess :
    (have state := currentMetrizableBoundarySourcePiZeroComparisonRouteStateW1608;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
