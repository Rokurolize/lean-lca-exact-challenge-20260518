import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRepresentativeImageFiniteShapeTransferBundleFieldSplitGuardW1360
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1361 extends the representative-image W532 transfer-bundle guard to the
normalized and direct-limit variants. These constructors rebuild limit
stability from direct WPP right fields when needed, rebuild colimit stability
through W535, and preserve the explicit or normalized localization field.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpRowAwareClosedMapClosedRangeOnlyProjectionV370SupportW527
open WppOpW535FiniteShapeTransferConcreteRowsV370SupportW535

namespace Dbounded

def canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361 :
    List String :=
  ["direct WPP right fields or WPP limit stability",
    "ClosedNatTransOrdinaryRepresentativeImageProviderW515",
    "ComponentwiseClosedMapRowsProviderW527 or ComponentwiseClosedEmbeddingRowsProviderW527",
    "explicit or normalized WalkingParallelPair localization"]

theorem canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361_count :
    canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361.length =
      4 :=
  rfl

theorem canonicalW532RepresentativeImageDirectLimitTransferBundleExpandsCurrentSurfaceW1361 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361_count]
  norm_num

theorem w532RepImageClosedMapRowsNormalizedKeepsLimitStabilityW1361
    (inputs : MetrizableWppTransferInputsFromRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedMapRowsNormalized
        inputs).limitStability =
      inputs.limitStability :=
  rfl

theorem w532RepImageClosedMapRowsNormalizedUsesW535ColimitStabilityW1361
    (inputs : MetrizableWppTransferInputsFromRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedMapRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedMapRows_w535
        inputs.representativeImageProvider inputs.closedMapRows :=
  rfl

theorem w532RepImageClosedMapRowsNormalizedUsesNormalizedLocalizationW1361
    (inputs : MetrizableWppTransferInputsFromRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedMapRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

theorem w532RepImageClosedEmbeddingRowsNormalizedKeepsLimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedEmbeddingRowsNormalized
        inputs).limitStability =
      inputs.limitStability :=
  rfl

theorem w532RepImageClosedEmbeddingRowsNormalizedUsesW535ColimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedEmbeddingRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedEmbeddingRows_w535
        inputs.representativeImageProvider inputs.closedEmbeddingRows :=
  rfl

theorem w532RepImageClosedEmbeddingRowsNormalizedUsesNormalizedLocalizationW1361
    (inputs :
      MetrizableWppTransferInputsFromRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_repImageClosedEmbeddingRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsUsesDirectRightLimitStabilityW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedMapRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedMapRows
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsUsesW535ColimitStabilityW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedMapRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedMapRows
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedMapRows_w535
        inputs.representativeImageProvider inputs.closedMapRows :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsKeepsLocalizationW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedMapRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedMapRows
        inputs).functorCategoryLocalization =
      inputs.functorCategoryLocalization :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsUsesDirectRightLimitStabilityW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedEmbeddingRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedEmbeddingRows
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsUsesW535ColimitStabilityW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedEmbeddingRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedEmbeddingRows
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedEmbeddingRows_w535
        inputs.representativeImageProvider inputs.closedEmbeddingRows :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsKeepsLocalizationW1361
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectLimitRepresentativeImageClosedEmbeddingRows) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitRepresentativeImageClosedEmbeddingRows
        inputs).functorCategoryLocalization =
      inputs.functorCategoryLocalization :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsNormalizedUsesDirectRightLimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedMapRowsNormalized
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsNormalizedUsesW535ColimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedMapRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedMapRows_w535
        inputs.representativeImageProvider inputs.closedMapRows :=
  rfl

theorem w532DirectLimitRepImageClosedMapRowsNormalizedUsesNormalizedLocalizationW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedMapRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedMapRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsNormalizedUsesDirectRightLimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedEmbeddingRowsNormalized
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsNormalizedUsesW535ColimitStabilityW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedEmbeddingRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_representativeImage_and_closedEmbeddingRows_w535
        inputs.representativeImageProvider inputs.closedEmbeddingRows :=
  rfl

theorem w532DirectLimitRepImageClosedEmbeddingRowsNormalizedUsesNormalizedLocalizationW1361
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitRepImageClosedEmbeddingRowsNormalized) :
    (metrizableWppTransferInputs_of_directLimitRepImageClosedEmbeddingRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

structure MetrizableRepresentativeImageDirectLimitTransferBundleFieldSplitGuardStateW1361 :
    Type where
  seed : String
  inspectedBoundary : String
  inputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableRepresentativeImageDirectLimitTransferBundleFieldSplitGuardStateW1361 :
    MetrizableRepresentativeImageDirectLimitTransferBundleFieldSplitGuardStateW1361 where
  seed := "w1361-representative-image-direct-limit-transfer-bundle-field-split-guard"
  inspectedBoundary :=
    "W532 representative-image normalized and direct-limit closed-map and\
      closed-embedding row transfer bundles"
  inputCount :=
    canonicalW532RepresentativeImageDirectLimitTransferBundleInputNamesW1361.length
  providerSearchResult :=
    "proved: normalized representative-image bundles keep limit stability and\
      use normalized localization; direct-limit representative-image bundles\
      rebuild limit stability from direct WPP right fields, rebuild colimit\
      stability through W535, and keep explicit or normalized localization"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1361RepresentativeImageDirectLimitTransferBundleFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableRepresentativeImageDirectLimitTransferBundleFieldSplitGuardStateW1361;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
