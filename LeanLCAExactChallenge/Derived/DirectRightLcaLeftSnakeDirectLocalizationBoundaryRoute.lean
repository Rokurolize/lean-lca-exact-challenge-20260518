import LeanLCAExactChallenge.Derived.W735DirectLocalizationBoundaryRoute
import LeanLCAExactChallenge.Derived.DirectWppLimitFiniteShapeTransfer

/-!
W878 feeds direct-right-LCA WPP limits and WPP-op left/Snake colimits into
the W877 direct-localization boundary.

This is a nonterminal bridge.  It removes the two opaque WPP stability fields
from W877's direct-localization boundary data, without importing the unrelated
closed-range comparison and endpoint-topology fields carried by W778.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open DirectWppOpColimitFiniteShapeTransfer

namespace Dbounded

/--
W878 closed-map branch data for direct localization through direct-right-LCA
limits and WPP-op left/Snake colimits.
-/
structure MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput

/--
W878 closed-embedding branch data for direct localization through
direct-right-LCA limits and WPP-op left/Snake colimits.
-/
structure
    MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  opLeftClosed : MetrizableWppOpLeftClosedInput
  opSnake : MetrizableWppOpSnakeInput

/-- W878 derives closed-map WPP limit stability from direct-right-LCA fields. -/
theorem limitStabilityOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraicRightLca
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/--
W878 derives closed-embedding WPP limit stability from direct-right-LCA fields.
-/
theorem limitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraicRightLca
    { rightOpenLca := data.rightOpenLca
      rightSurjectiveLca := data.rightSurjectiveLca }

/-- W878 derives closed-map WPP colimit stability from WPP-op left/Snake fields. -/
theorem colimitStabilityOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    data.opLeftClosed
    data.opSnake

/--
W878 derives closed-embedding WPP colimit stability from WPP-op left/Snake fields.
-/
theorem colimitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  walkingParallelPairColimitStability_of_left_and_snakeCokernel
    data.opLeftClosed
    data.opSnake

/-- W878 closed-map branch converted to W877 direct-localization boundary data. -/
noncomputable def closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 where
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedMapDirectRightLcaLeftSnakeW878 data
  colimitStability := colimitStabilityOfClosedMapDirectRightLcaLeftSnakeW878 data

/--
W878 closed-embedding branch converted to W877 direct-localization boundary data.
-/
noncomputable def closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877 where
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878 data
  colimitStability :=
    colimitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878 data

/-- W878 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapW735DirectBoundaryW877
    (closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/-- W878 closed-embedding branch as WPP finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedEmbeddingW735DirectBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/--
W878 closed-map branch as canonical direct-localization stable-boundary inputs.
-/
noncomputable def directLocalizationBoundaryInputsOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapW735W877
    (closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/--
W878 closed-embedding branch as canonical direct-localization stable-boundary
inputs.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedEmbeddingW735W877
    (closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/-- W878 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def acceptedStableOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapW735DirectLocalizationBoundaryW877
    (closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/--
W878 closed-embedding branch passes the accepted stable direct-localization gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/-- W878 closed-map branch produces the bounded-derived package. -/
noncomputable def boundedDerivedOfClosedMapDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapW735DirectLocalizationBoundaryW877
    (closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/-- W878 closed-embedding branch produces the bounded-derived package. -/
noncomputable def boundedDerivedOfClosedEmbeddingDirectRightLcaLeftSnakeW878
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/--
W878 closed-map branch produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfClosedMapDirectRightLcaLeftSnakeW878_ready
    (data :
      MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapDirectRightLcaLeftSnakeW878 data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapW735DirectLocalizationBoundaryW877_ready
    (closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/--
W878 closed-embedding branch produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfClosedEmbeddingDirectRightLcaLeftSnakeW878_ready
    (data :
      MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedEmbeddingDirectRightLcaLeftSnakeW878
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedEmbeddingW735DirectLocalizationBoundaryW877_ready
    (closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878 data)

/-- W878 remaining inputs after direct-right-LCA and left/Snake derive WPP stability. -/
def directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878 :
    List String :=
  ["W735 closed-map or closed-embedding branch data, including normalized and\
      source-triangulation data",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate"]

theorem directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878_count :
    directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878.length = 5 :=
  rfl

/-- Current checked W878 state. -/
structure MetrizableDirectRightLcaLeftSnakeDirectLocalizationBoundaryRouteStateW878 :
    Type where
  seed : String
  declarations : List String
  limitResult : String
  colimitResult : String
  directBoundaryResult : String
  stableBoundaryResult : String
  derivedOrEliminatedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W878 state for the direct-right-LCA plus left/Snake
direct-localization boundary route.
-/
def currentMetrizableDirectRightLcaLeftSnakeDirectLocalizationBoundaryRouteStateW878 :
    MetrizableDirectRightLcaLeftSnakeDirectLocalizationBoundaryRouteStateW878
    where
  seed := "w878-direct-right-lca-left-snake-direct-localization-boundary-route"
  declarations :=
    ["MetrizableClosedMapDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878",
      "MetrizableClosedEmbeddingDirectRightLcaLeftSnakeDirectLocalizationBoundaryDataW878",
      "limitStabilityOfClosedMapDirectRightLcaLeftSnakeW878",
      "limitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "colimitStabilityOfClosedMapDirectRightLcaLeftSnakeW878",
      "colimitStabilityOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "closedMapW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878",
      "closedEmbeddingW735DirectBoundaryDataOfDirectRightLcaLeftSnakeW878",
      "transferInputsOfClosedMapDirectRightLcaLeftSnakeW878",
      "transferInputsOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "directLocalizationBoundaryInputsOfClosedMapDirectRightLcaLeftSnakeW878",
      "directLocalizationBoundaryInputsOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "acceptedStableOfClosedMapDirectRightLcaLeftSnakeW878",
      "acceptedStableOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "boundedDerivedOfClosedMapDirectRightLcaLeftSnakeW878",
      "boundedDerivedOfClosedEmbeddingDirectRightLcaLeftSnakeW878",
      "stableCertificateOfClosedMapDirectRightLcaLeftSnakeW878_ready",
      "stableCertificateOfClosedEmbeddingDirectRightLcaLeftSnakeW878_ready",
      "directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878",
      "directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878_count"]
  limitResult :=
    "proved: direct-right-LCA fields supply WPP limit stability via the W551\
      direct comparison"
  colimitResult :=
    "proved: WPP-op left/Snake fields supply WPP colimit stability"
  directBoundaryResult :=
    "proved: the derived WPP stability fields turn W735 data into W877\
      direct-localization boundary data"
  stableBoundaryResult :=
    "proved: the resulting direct-localization boundary passes the accepted\
      stable boundary and bounded-derived gates"
  derivedOrEliminatedInputs :=
    ["abstract WPP limit-stability field for WalkingParallelPair",
      "abstract WPP colimit-stability field for WalkingParallelPair",
      "mapping-cone WPP limit comparison as an external route input",
      "W778 closed-range comparison, exact-closure, and endpoint-topology\
        fields for this direct-localization boundary"]
  remainingInputs := directRightLcaLeftSnakeDirectLocalizationBoundaryInputNamesW878
  productSuccessClaimed := false

theorem currentW878DirectRightLcaLeftSnakeDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableDirectRightLcaLeftSnakeDirectLocalizationBoundaryRouteStateW878;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
