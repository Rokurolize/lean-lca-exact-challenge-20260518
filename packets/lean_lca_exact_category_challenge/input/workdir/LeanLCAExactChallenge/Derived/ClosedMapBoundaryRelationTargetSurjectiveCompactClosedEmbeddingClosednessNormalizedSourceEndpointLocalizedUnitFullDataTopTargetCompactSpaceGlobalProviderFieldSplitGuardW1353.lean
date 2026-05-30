import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSplitCompactTargetEndpointsFieldSplitGuardW1352
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1353 records the W598 top-target compact-space global-provider field split.
W598 converts W516 top-target data plus target compact-space data into W593/W594
split compact-target bundles, while copying the global closed-map or
closed-embedding provider and normalized inputs. The route still exposes an
eleven-input stable surface and therefore does not close the current one-input
W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer

namespace Dbounded

def canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353 :
    List String :=
  metrizableWppTopTargetCompactSpaceStableInputNamesW598

theorem canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353_count :
    canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353.length =
      11 :=
  metrizableWppTopTargetCompactSpaceStableInputNamesW598_count

theorem canonicalW598TopTargetCompactSpaceGlobalProviderExpandsCurrentSurfaceW1353 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353_count]
  norm_num

theorem w598ClosedMapBundleKeepsRightOpenBoundaryW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w598ClosedMapBundleKeepsSourcePiZeroBoundaryW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w598ClosedMapBundleUsesTopTargetRelationPullbackW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).relationPullbackProvider =
      relationPullbackProvider_of_topTargetRelation_w597 inputs.topTargetProvider :=
  rfl

theorem w598ClosedMapBundleUsesTopTargetCompactnessW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).targetCompactProvider =
      targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
        inputs.topTargetProvider inputs.targetCompactSpaceProvider :=
  rfl

theorem w598ClosedMapBundleKeepsClosedMapProviderW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).closedMapProvider =
      inputs.closedMapProvider :=
  rfl

theorem w598ClosedMapBundleKeepsNormalizedInputsW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

theorem w598ClosedEmbeddingBundleKeepsRightOpenBoundaryW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w598ClosedEmbeddingBundleKeepsSourcePiZeroBoundaryW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w598ClosedEmbeddingBundleUsesTopTargetRelationPullbackW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).relationPullbackProvider =
      relationPullbackProvider_of_topTargetRelation_w597 inputs.topTargetProvider :=
  rfl

theorem w598ClosedEmbeddingBundleUsesTopTargetCompactnessW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).targetCompactProvider =
      targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
        inputs.topTargetProvider inputs.targetCompactSpaceProvider :=
  rfl

theorem w598ClosedEmbeddingBundleKeepsClosedEmbeddingProviderW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).closedEmbeddingProvider =
      inputs.closedEmbeddingProvider :=
  rfl

theorem w598ClosedEmbeddingBundleKeepsNormalizedInputsW1353
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingNormalizedBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_topTargetCompactSpaceW598
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

theorem w598ClosedMapStableBundleKeepsPretriangulatedW1353
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapHomotopyIsoClosedStableBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapHomotopyIsoClosedStableBundle_of_topTargetCompactSpaceW598
        inputs).pretriangulated =
      inputs.pretriangulated :=
  rfl

theorem w598ClosedMapStableBundleKeepsTriangulatedW1353
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedMapHomotopyIsoClosedStableBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapHomotopyIsoClosedStableBundle_of_topTargetCompactSpaceW598
        inputs).triangulated =
      inputs.triangulated :=
  rfl

theorem w598ClosedEmbeddingStableBundleKeepsPretriangulatedW1353
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingHomotopyIsoClosedStableBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundle_of_topTargetCompactSpaceW598
        inputs).pretriangulated =
      inputs.pretriangulated :=
  rfl

theorem w598ClosedEmbeddingStableBundleKeepsTriangulatedW1353
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroTopTargetCompactSpaceGlobalClosedEmbeddingHomotopyIsoClosedStableBundleW598) :
    (metrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundle_of_topTargetCompactSpaceW598
        inputs).triangulated =
      inputs.triangulated :=
  rfl

structure MetrizableTopTargetCompactSpaceGlobalProviderFieldSplitGuardStateW1353 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTopTargetCompactSpaceGlobalProviderFieldSplitGuardStateW1353 :
    MetrizableTopTargetCompactSpaceGlobalProviderFieldSplitGuardStateW1353 where
  seed := "w1353-top-target-compact-space-global-provider-field-split-guard"
  inspectedBoundary :=
    "W598 field split from W516 top-target and target compact-space data into\
      W593/W594 split compact-target global-provider routes"
  routeSurfaceCount :=
    canonicalW598TopTargetCompactSpaceGlobalProviderInputNamesW1353.length
  providerSearchResult :=
    "proved: W598 copies the right-open boundary, source pi-zero boundary,\
      global provider, and normalized inputs while rebuilding relation-pullback\
      and target-compactness providers through W597, and stable bundles keep\
      their pretriangulated and triangulated witnesses; the stable route still\
      has eleven inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1353TopTargetCompactSpaceGlobalProviderFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableTopTargetCompactSpaceGlobalProviderFieldSplitGuardStateW1353;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
