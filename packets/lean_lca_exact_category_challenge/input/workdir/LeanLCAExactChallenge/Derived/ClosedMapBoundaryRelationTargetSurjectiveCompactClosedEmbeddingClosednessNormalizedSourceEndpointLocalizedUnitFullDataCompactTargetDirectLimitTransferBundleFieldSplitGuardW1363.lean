import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTopTargetDirectLimitTransferBundleFieldSplitGuardW1362
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1363 records the W532 direct-limit transfer bundles for W517 compact-target
data. The constructors rebuild limit stability from direct WPP right fields,
rebuild colimit stability through W535, and preserve explicit, fixed-target,
or normalized localization fields.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpRowAwareClosedMapClosedRangeOnlyProjectionV370SupportW527
open WppOpW535FiniteShapeTransferConcreteRowsV370SupportW535

namespace Dbounded

def canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363 :
    List String :=
  ["direct WPP right fields",
    "ClosedNatTransOrdinaryCompactTargetRelationProviderW517",
    "ComponentwiseClosedMapRowsProviderW527 or ComponentwiseClosedEmbeddingRowsProviderW527",
    "explicit, fixed-target, or normalized WalkingParallelPair localization"]

theorem canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363_count :
    canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363.length = 4 :=
  rfl

theorem canonicalW532CompactTargetDirectLimitTransferBundleExpandsCurrentSurfaceW1363 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363_count]
  norm_num

theorem w532DirectLimitCompactTargetClosedMapRowsUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedMapRows
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedMapRows
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedMapRows_w535
        inputs.provider inputs.closedMapRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsKeepsLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedMapRows
        inputs).functorCategoryLocalization =
      inputs.functorCategoryLocalization :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRows
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRows
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedEmbeddingRows_w535
        inputs.provider inputs.closedEmbeddingRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsKeepsLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRows
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRows
        inputs).functorCategoryLocalization =
      inputs.functorCategoryLocalization :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsFixedTargetsUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsFixedTargets
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsFixedTargetsUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsFixedTargets
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedMapRows_w535
        inputs.provider inputs.closedMapRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsFixedTargetsUsesFixedTargetLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsFixedTargets
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
        inputs.fixedTargetInputs :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsFixedTargetsUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsFixedTargets
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsFixedTargetsUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsFixedTargets
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedEmbeddingRows_w535
        inputs.provider inputs.closedEmbeddingRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsFixedTargetsUsesFixedTargetLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsFixedTargets
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsFixedTargets
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
        inputs.fixedTargetInputs :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsNormalizedUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsNormalized
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsNormalizedUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedMapRows_w535
        inputs.provider inputs.closedMapRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedMapRowsNormalizedUsesNormalizedLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedMapRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedMapRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsNormalizedUsesDirectRightLimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsNormalized
        inputs).limitStability =
      metrizableWalkingParallelPairLimitStability_of_directRightFields
        inputs.rightOpen inputs.rightSurjective :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsNormalizedUsesW535ColimitStabilityW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsNormalized
        inputs).colimitStability =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedEmbeddingRows_w535
        inputs.provider inputs.closedEmbeddingRows :=
  rfl

theorem w532DirectLimitCompactTargetClosedEmbeddingRowsNormalizedUsesNormalizedLocalizationW1363
    (inputs :
      MetrizableWppTransferInputsFromDirectLimitClosedEmbeddingRowsNormalized
        ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    (metrizableWppTransferInputs_of_directLimitCompactTargetRelationClosedEmbeddingRowsNormalized
        inputs).functorCategoryLocalization =
      Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
        inputs.normalizedInputs :=
  rfl

structure MetrizableCompactTargetDirectLimitTransferBundleFieldSplitGuardStateW1363 :
    Type where
  seed : String
  inspectedBoundary : String
  inputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCompactTargetDirectLimitTransferBundleFieldSplitGuardStateW1363 :
    MetrizableCompactTargetDirectLimitTransferBundleFieldSplitGuardStateW1363 where
  seed := "w1363-compact-target-direct-limit-transfer-bundle-field-split-guard"
  inspectedBoundary :=
    "W532 compact-target direct-limit closed-map and closed-embedding row\
      transfer bundles"
  inputCount :=
    canonicalW532CompactTargetDirectLimitTransferBundleInputNamesW1363.length
  providerSearchResult :=
    "proved: compact-target direct-limit W532 bundles rebuild limit stability\
      from direct WPP right fields, rebuild colimit stability through W535,\
      and preserve explicit, fixed-target, or normalized localization"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1363CompactTargetDirectLimitTransferBundleFieldSplitGuard_productSuccess :
    (let state := currentMetrizableCompactTargetDirectLimitTransferBundleFieldSplitGuardStateW1363;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
