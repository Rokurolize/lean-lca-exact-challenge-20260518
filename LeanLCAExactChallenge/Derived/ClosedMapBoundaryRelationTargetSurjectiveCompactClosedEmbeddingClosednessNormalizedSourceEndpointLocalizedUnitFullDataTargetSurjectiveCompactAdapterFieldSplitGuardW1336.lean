import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetSurjectiveCompactProviderFieldSplitGuardW1335
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1336 records the W601 target-surjective compact-codomain adapter field split.
W601 separates target-difference surjectivity and target-codomain compactness,
then repackages them for W600/W606 routes. The route still exposes four inputs
and therefore does not close the current one-input W987 obligation.
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

def canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336 :
    List String :=
  metrizableWppTargetSurjectiveCompactInputNamesW601

theorem canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336_count :
    canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336.length =
      4 :=
  metrizableWppTargetSurjectiveCompactInputNamesW601_count

theorem canonicalW601TargetSurjectiveCompactAdapterFieldSplitExpandsCurrentSurfaceW1336 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336_count]
  norm_num

theorem w601TargetCompactProjectionAtW1336
    (hcompact : TargetCodomainCompactSpaceProviderW601)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    targetCompactSpaceProvider_of_targetCodomainCompact_w601
        hcompact X Y α hclosed =
      hcompact Y :=
  rfl

theorem w601TopTargetProviderRunsThroughSplitW600W1336
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hsurj : TargetDifferenceSurjectiveProviderW601) :
    topTargetProvider_of_pullback_targetSurjective_w601 hpullback hsurj =
      topTargetRelationProvider_of_splitFields_w600 hpullback
        (targetTopProvider_of_targetSurjective_w601 hsurj) :=
  rfl

theorem w601CompactTargetProviderRunsThroughSplitW600W1336
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hsurj : TargetDifferenceSurjectiveProviderW601)
    (hcompact : TargetCodomainCompactSpaceProviderW601) :
    compactTargetProvider_of_pullback_targetSurjective_compactCodomain_w601
        hpullback hsurj hcompact =
      compactTargetRelationProvider_of_splitTopTarget_targetCompactSpace_w600
        hpullback
        (targetTopProvider_of_targetSurjective_w601 hsurj)
        (targetCompactSpaceProvider_of_targetCodomainCompact_w601 hcompact) :=
  rfl

theorem w606ClosedMapKeepsRightOpenBoundaryW1336
    (inputs : MetrizableWppTargetSurjectiveCompactClosedMapRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w606ClosedMapUsesTargetTopProjectionW1336
    (inputs : MetrizableWppTargetSurjectiveCompactClosedMapRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).targetRelationTopProvider =
      targetTopProvider_of_targetSurjective_w601
        inputs.targetDifferenceSurjectiveProvider :=
  rfl

theorem w606ClosedMapUsesTargetCompactProjectionW1336
    (inputs : MetrizableWppTargetSurjectiveCompactClosedMapRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).targetCompactSpaceProvider =
      targetCompactSpaceProvider_of_targetCodomainCompact_w601
        inputs.targetCodomainCompactSpaceProvider :=
  rfl

theorem w606ClosedMapKeepsRowsW1336
    (inputs : MetrizableWppTargetSurjectiveCompactClosedMapRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).closedMapRows =
      inputs.closedMapRows :=
  rfl

theorem w606ClosedEmbeddingKeepsSourcePiZeroBoundaryW1336
    (inputs :
      MetrizableWppTargetSurjectiveCompactClosedEmbeddingRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w606ClosedEmbeddingUsesTargetTopProjectionW1336
    (inputs :
      MetrizableWppTargetSurjectiveCompactClosedEmbeddingRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).targetRelationTopProvider =
      targetTopProvider_of_targetSurjective_w601
        inputs.targetDifferenceSurjectiveProvider :=
  rfl

theorem w606ClosedEmbeddingUsesTargetCompactProjectionW1336
    (inputs :
      MetrizableWppTargetSurjectiveCompactClosedEmbeddingRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).targetCompactSpaceProvider =
      targetCompactSpaceProvider_of_targetCodomainCompact_w601
        inputs.targetCodomainCompactSpaceProvider :=
  rfl

theorem w606ClosedEmbeddingKeepsRowsW1336
    (inputs :
      MetrizableWppTargetSurjectiveCompactClosedEmbeddingRowsNormalizedBundleW606) :
    (metrizableWppSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_targetSurjectiveCompactW606
        inputs).closedEmbeddingRows =
      inputs.closedEmbeddingRows :=
  rfl

structure MetrizableTargetSurjectiveCompactAdapterFieldSplitGuardStateW1336 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactAdapterFieldSplitGuardStateW1336 :
    MetrizableTargetSurjectiveCompactAdapterFieldSplitGuardStateW1336 where
  seed := "w1336-target-surjective-compact-adapter-field-split-guard"
  inspectedBoundary :=
    "W601 field split from target-difference surjectivity and target-codomain\
      compactness into W600/W606 target providers"
  routeSurfaceCount :=
    canonicalW601TargetSurjectiveCompactAdapterFieldSplitInputNamesW1336.length
  providerSearchResult :=
    "proved: W601 compact-codomain data projects to W597 target compact-space\
      data, the W601 pullback adapters run through W600 split fields, and W606\
      closed-map/closed-embedding bundles preserve representative fields while\
      using the W601 target-top and compact-space projections, but its route\
      surface still has four inputs and expands the current one-input W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1336TargetSurjectiveCompactAdapterFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactAdapterFieldSplitGuardStateW1336;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
