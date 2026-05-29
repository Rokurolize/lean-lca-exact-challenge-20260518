import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSplitCompactTargetGlobalClosedMapFieldSplitGuardW1350
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1351 records the W594 split compact-target global closed-embedding field split.
W594 is the closed-embedding analogue of W593: it reconstructs the W517
compact-target provider from relation-pullback and target-relation compactness
providers, then copies the closed-embedding normalized bundle fields into the
W581 compact-target route. The route still exposes an eleven-input stable
surface and therefore does not close the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer

namespace Dbounded

def canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351 :
    List String :=
  metrizableWppSplitCompactTargetGlobalClosedEmbeddingStableInputNamesW594

theorem canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351_count :
    canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351.length =
      11 :=
  metrizableWppSplitCompactTargetGlobalClosedEmbeddingStableInputNamesW594_count

theorem canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitExpandsCurrentSurfaceW1351 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351_count]
  norm_num

theorem w594ClosedEmbeddingBundleKeepsRightOpenBoundaryW1351
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w594ClosedEmbeddingBundleKeepsSourcePiZeroBoundaryW1351
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w594ClosedEmbeddingBundleUsesSplitCompactTargetProviderW1351
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs).compactTargetProvider =
      compactTargetRelationProvider_of_splitFields_w593
        inputs.relationPullbackProvider inputs.targetCompactProvider :=
  rfl

theorem w594ClosedEmbeddingBundleKeepsClosedEmbeddingProviderW1351
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs).closedEmbeddingProvider =
      inputs.closedEmbeddingProvider :=
  rfl

theorem w594ClosedEmbeddingBundleKeepsNormalizedInputsW1351
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingNormalizedBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

theorem w594StableBundleUsesConvertedCompactTargetBundleW1351
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundle_of_splitCompactTargetW594
        inputs).compactTargetBundle =
      metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingNormalizedBundle_of_splitCompactTargetW594
        inputs.compactTargetBundle :=
  rfl

theorem w594StableBundleKeepsPretriangulatedW1351
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundle_of_splitCompactTargetW594
        inputs).pretriangulated =
      inputs.pretriangulated :=
  rfl

theorem w594StableBundleKeepsTriangulatedW1351
    [(exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundleW594) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedEmbeddingHomotopyIsoClosedStableBundle_of_splitCompactTargetW594
        inputs).triangulated =
      inputs.triangulated :=
  rfl

structure MetrizableSplitCompactTargetGlobalClosedEmbeddingFieldSplitGuardStateW1351 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitCompactTargetGlobalClosedEmbeddingFieldSplitGuardStateW1351 :
    MetrizableSplitCompactTargetGlobalClosedEmbeddingFieldSplitGuardStateW1351 where
  seed := "w1351-split-compact-target-global-closed-embedding-field-split-guard"
  inspectedBoundary :=
    "W594 field split from relation-pullback and target-relation compactness\
      providers into the W581 compact-target global closed-embedding route"
  routeSurfaceCount :=
    canonicalW594SplitCompactTargetGlobalClosedEmbeddingFieldSplitInputNamesW1351.length
  providerSearchResult :=
    "proved: W594 copies the right-open boundary, source pi-zero boundary,\
      closed-embedding provider, and normalized inputs into W581 while\
      rebuilding only the compact-target provider, and the stable bundle keeps\
      its pretriangulated and triangulated witnesses; the stable route still\
      has eleven inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1351SplitCompactTargetGlobalClosedEmbeddingFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableSplitCompactTargetGlobalClosedEmbeddingFieldSplitGuardStateW1351;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
