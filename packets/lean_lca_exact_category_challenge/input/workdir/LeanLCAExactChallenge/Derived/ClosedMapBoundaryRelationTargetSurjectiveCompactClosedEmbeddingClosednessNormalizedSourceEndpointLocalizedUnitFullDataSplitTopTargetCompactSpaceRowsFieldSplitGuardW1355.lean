import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTopTargetCompactSpaceRowsFieldSplitGuardW1354
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1355 completes the local W600 split top-target compact-space row guard
started by W1337. It records the remaining normalized-bundle fields, stable
bundle adapters, and endpoint delegations for the closed-map and
closed-embedding row routes.
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
open WppOpSelectedDifferenceClosedMapClosedRangeOnlyV370SupportW525
open WppOpRowAwareClosedRangeOnlyProjectionV370SupportW526
open WppOpRowAwareClosedMapClosedRangeOnlyProjectionV370SupportW527
open WppOpW535FiniteShapeTransferConcreteRowsV370SupportW535

namespace Dbounded

def canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355 :
    List String :=
  metrizableWppSplitTopTargetCompactSpaceRowsStableInputNamesW600

theorem canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355_count :
    canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355.length =
      12 :=
  metrizableWppSplitTopTargetCompactSpaceRowsStableInputNamesW600_count

theorem canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitExpandsCurrentSurfaceW1355 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355_count]
  norm_num

theorem w600ClosedMapKeepsSourcePiZeroBoundaryW1355
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w600ClosedMapKeepsNormalizedInputsW1355
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

theorem w600ClosedEmbeddingKeepsRightOpenBoundaryW1355
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w600ClosedEmbeddingKeepsNormalizedInputsW1355
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

theorem w600ClosedMapStableBundleKeepsSplitBundleW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).topTargetBundle =
      metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsNormalizedBundle_of_splitTopTargetW600
        inputs.splitTopTargetBundle :=
  rfl

theorem w600ClosedMapStableBundleKeepsPretriangulatedW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).pretriangulated =
      inputs.pretriangulated :=
  rfl

theorem w600ClosedMapStableBundleKeepsTriangulatedW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedMapRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).triangulated =
      inputs.triangulated :=
  rfl

theorem w600ClosedEmbeddingStableBundleKeepsSplitBundleW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).topTargetBundle =
      metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsNormalizedBundle_of_splitTopTargetW600
        inputs.splitTopTargetBundle :=
  rfl

theorem w600ClosedEmbeddingStableBundleKeepsPretriangulatedW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).pretriangulated =
      inputs.pretriangulated :=
  rfl

theorem w600ClosedEmbeddingStableBundleKeepsTriangulatedW1355
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundleW600) :
    (metrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceClosedEmbeddingRowsHomotopyIsoClosedStableBundle_of_splitTopTargetW600
        inputs).triangulated =
      inputs.triangulated :=
  rfl

theorem w600ClosedMapExactEndpointDelegatesToW595W1355
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    exactAcyclic_of_splitTopTarget_targetCompactSpace_closedMap_w600
        hpullback htop hcompactSpace hclosedMap =
      exactAcyclic_of_splitCompactTargetRelation_closedMap_w595 hpullback
        (targetRelationCompactProvider_of_targetRelationTop_targetCompactSpace_w600
          htop hcompactSpace)
        hclosedMap :=
  rfl

theorem w600ClosedEmbeddingExactEndpointDelegatesToW595W1355
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    exactAcyclic_of_splitTopTarget_targetCompactSpace_closedEmbedding_w600
        hpullback htop hcompactSpace hclosedEmbedding =
      exactAcyclic_of_splitCompactTargetRelation_closedEmbedding_w595 hpullback
        (targetRelationCompactProvider_of_targetRelationTop_targetCompactSpace_w600
          htop hcompactSpace)
        hclosedEmbedding :=
  rfl

theorem w600ClosedMapRowsColimitEndpointDelegatesToW535W1355
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedMapRows : ComponentwiseClosedMapRowsProviderW527) :
    walkingParallelPairColimitStability_of_splitTopTargetCompactSpace_closedMapRows_w600
        hpullback htop hcompactSpace hclosedMapRows =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedMapRows_w535
        (compactTargetRelationProvider_of_splitTopTarget_targetCompactSpace_w600
          hpullback htop hcompactSpace)
        hclosedMapRows :=
  rfl

theorem w600ClosedEmbeddingRowsColimitEndpointDelegatesToW535W1355
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (htop : ClosedNatTransOrdinaryTargetRelationTopProviderW600)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedEmbeddingRows : ComponentwiseClosedEmbeddingRowsProviderW527) :
    walkingParallelPairColimitStability_of_splitTopTargetCompactSpace_closedEmbeddingRows_w600
        hpullback htop hcompactSpace hclosedEmbeddingRows =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedEmbeddingRows_w535
        (compactTargetRelationProvider_of_splitTopTarget_targetCompactSpace_w600
          hpullback htop hcompactSpace)
        hclosedEmbeddingRows :=
  rfl

structure MetrizableSplitTopTargetCompactSpaceRowsFieldSplitGuardStateW1355 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitTopTargetCompactSpaceRowsFieldSplitGuardStateW1355 :
    MetrizableSplitTopTargetCompactSpaceRowsFieldSplitGuardStateW1355 where
  seed := "w1355-split-top-target-compact-space-rows-field-split-guard"
  inspectedBoundary :=
    "W600 normalized and stable row bundles plus exact and colimit endpoints"
  routeSurfaceCount :=
    canonicalW600SplitTopTargetCompactSpaceRowsFieldSplitInputNamesW1355.length
  providerSearchResult :=
    "proved: W600 closed-map and closed-embedding row bundles preserve the\
      remaining boundary and normalized fields, stable bundles preserve the\
      stable categorical fields, and exact/colimit endpoints delegate through\
      W595 and W535 while the route still exposes twelve inputs"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1355SplitTopTargetCompactSpaceRowsFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableSplitTopTargetCompactSpaceRowsFieldSplitGuardStateW1355;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
