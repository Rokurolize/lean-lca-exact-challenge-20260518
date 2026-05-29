import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTopTargetRelationRepresentativeImageFieldSplitGuardW1349
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1350 records the W593 split compact-target global closed-map field split.
W593 reconstructs the W517 compact-target provider from relation-pullback and
target-relation compactness providers, then copies the closed-map normalized
bundle fields into the W591 compact-target route. The route still exposes an
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

def canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350 :
    List String :=
  metrizableWppSplitCompactTargetGlobalClosedMapStableInputNamesW593

theorem canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350_count :
    canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350.length =
      11 :=
  metrizableWppSplitCompactTargetGlobalClosedMapStableInputNamesW593_count

theorem canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitExpandsCurrentSurfaceW1350 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350_count]
  norm_num

theorem w593CompactTargetRelationKeepsRelationPullbackW1350
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact
        X Y α hclosed).relation_pullback =
      hpullback X Y α hclosed :=
  rfl

theorem w593CompactTargetRelationKeepsTargetCompactnessW1350
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact
        X Y α hclosed).target_relation_compact =
      hcompact X Y α hclosed :=
  rfl

theorem w593ClosedMapBundleKeepsRightOpenBoundaryW1350
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundleW593) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedMapNormalizedBundle_of_splitCompactTargetW593
        inputs).rightOpenBoundary =
      inputs.rightOpenBoundary :=
  rfl

theorem w593ClosedMapBundleKeepsSourcePiZeroBoundaryW1350
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundleW593) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedMapNormalizedBundle_of_splitCompactTargetW593
        inputs).sourcePiZeroBoundary =
      inputs.sourcePiZeroBoundary :=
  rfl

theorem w593ClosedMapBundleUsesSplitCompactTargetProviderW1350
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundleW593) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedMapNormalizedBundle_of_splitCompactTargetW593
        inputs).compactTargetProvider =
      compactTargetRelationProvider_of_splitFields_w593
        inputs.relationPullbackProvider inputs.targetCompactProvider :=
  rfl

theorem w593ClosedMapBundleKeepsClosedMapProviderW1350
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundleW593) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedMapNormalizedBundle_of_splitCompactTargetW593
        inputs).closedMapProvider =
      inputs.closedMapProvider :=
  rfl

theorem w593ClosedMapBundleKeepsNormalizedInputsW1350
    (inputs :
      MetrizableWppRightOpenClosedQuotientPiZeroSplitCompactTargetGlobalClosedMapNormalizedBundleW593) :
    (metrizableWppRightOpenClosedQuotientPiZeroCompactTargetGlobalClosedMapNormalizedBundle_of_splitCompactTargetW593
        inputs).normalizedInputs =
      inputs.normalizedInputs :=
  rfl

structure MetrizableSplitCompactTargetGlobalClosedMapFieldSplitGuardStateW1350 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitCompactTargetGlobalClosedMapFieldSplitGuardStateW1350 :
    MetrizableSplitCompactTargetGlobalClosedMapFieldSplitGuardStateW1350 where
  seed := "w1350-split-compact-target-global-closed-map-field-split-guard"
  inspectedBoundary :=
    "W593 field split from relation-pullback and target-relation compactness\
      providers into the W591 compact-target global closed-map route"
  routeSurfaceCount :=
    canonicalW593SplitCompactTargetGlobalClosedMapFieldSplitInputNamesW1350.length
  providerSearchResult :=
    "proved: W593 preserves both W517 compact-target fields and copies the\
      right-open boundary, source pi-zero boundary, closed-map provider, and\
      normalized inputs into W591 while rebuilding only the compact-target\
      provider; the stable route still has eleven inputs and expands the\
      current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1350SplitCompactTargetGlobalClosedMapFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableSplitCompactTargetGlobalClosedMapFieldSplitGuardStateW1350;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
