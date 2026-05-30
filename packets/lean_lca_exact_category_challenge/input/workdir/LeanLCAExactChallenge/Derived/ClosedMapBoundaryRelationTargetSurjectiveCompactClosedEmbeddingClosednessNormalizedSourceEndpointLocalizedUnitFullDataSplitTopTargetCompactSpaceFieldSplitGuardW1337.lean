import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetSurjectiveCompactAdapterFieldSplitGuardW1336
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1337 records the W600 split top-target compact-space field split. W600 splits
W516 top-target data into relation-pullback and target-relation-top providers,
combines target-top data with W597 compact target spaces, and then feeds W599.
The route still exposes W600's twelve-input row-stable surface and therefore
does not close the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

def canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337 :
    List String :=
  metrizableWppSplitTopTargetCompactSpaceRowsStableInputNamesW600

theorem canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337_count :
    canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337.length =
      12 :=
  metrizableWppSplitTopTargetCompactSpaceRowsStableInputNamesW600_count

theorem canonicalW600SplitTopTargetCompactSpaceFieldSplitExpandsCurrentSurfaceW1337 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337_count]
  norm_num

theorem w600TopTargetRelationPullbackProjectionW1337
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    (topTargetRelationProvider_of_splitFields_w600 hpullback htop
        X Y α hclosed).relation_pullback =
      hpullback X Y α hclosed :=
  rfl

theorem w600TopTargetRelationTopProjectionW1337
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    (topTargetRelationProvider_of_splitFields_w600 hpullback htop
        X Y α hclosed).target_relation_top =
      htop X Y α hclosed :=
  rfl

theorem w600RelationFieldsPullbackProjectionW1337
    (hfields : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    relationPullbackProvider_of_relationFields_w600 hfields X Y α hclosed =
      (hfields X Y α hclosed).relation_pullback :=
  rfl

theorem w600CompactTargetRunsThroughW593W1337
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597) :
    compactTargetRelationProvider_of_splitTopTarget_targetCompactSpace_w600
        hpullback htop hcompactSpace =
      compactTargetRelationProvider_of_splitFields_w593 hpullback
        (targetRelationCompactProvider_of_targetRelationTop_targetCompactSpace_w600
          htop hcompactSpace) :=
  rfl

theorem w600ClosedMapKeepsRightOpenBoundaryW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w600ClosedMapUsesTopTargetProviderW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).topTargetProvider =
      topTargetRelationProvider_of_splitFields_w600
        inputs.relationPullbackProvider inputs.targetRelationTopProvider :=
  rfl

theorem w600ClosedMapKeepsTargetCompactSpaceW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).targetCompactSpaceProvider =
      inputs.targetCompactSpaceProvider :=
  rfl

theorem w600ClosedMapKeepsRowsW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).closedMapRows =
      inputs.closedMapRows :=
  rfl

theorem w600ClosedEmbeddingKeepsSourcePiZeroBoundaryW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w600ClosedEmbeddingUsesTopTargetProviderW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).topTargetProvider =
      topTargetRelationProvider_of_splitFields_w600
        inputs.relationPullbackProvider inputs.targetRelationTopProvider :=
  rfl

theorem w600ClosedEmbeddingKeepsTargetCompactSpaceW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).targetCompactSpaceProvider =
      inputs.targetCompactSpaceProvider :=
  rfl

theorem w600ClosedEmbeddingKeepsRowsW1337
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).closedEmbeddingRows =
      inputs.closedEmbeddingRows :=
  rfl

structure MetrizableSplitTopTargetCompactSpaceFieldSplitGuardStateW1337 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitTopTargetCompactSpaceFieldSplitGuardStateW1337 :
    MetrizableSplitTopTargetCompactSpaceFieldSplitGuardStateW1337 where
  seed := "w1337-split-top-target-compact-space-field-split-guard"
  inspectedBoundary :=
    "W600 field split from relation-pullback, target-top, and target compact\
      space data into W599 row-level bundles"
  routeSurfaceCount :=
    canonicalW600SplitTopTargetCompactSpaceFieldSplitInputNamesW1337.length
  providerSearchResult :=
    "proved: W600 reconstructs W516 top-target data from relation-pullback and\
      target-top fields, routes compact-target data through W593, and preserves\
      representative W600 closed-map/closed-embedding bundle fields while\
      rebuilding W599, but its route surface still has twelve inputs and\
      expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1337SplitTopTargetCompactSpaceFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableSplitTopTargetCompactSpaceFieldSplitGuardStateW1337;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
