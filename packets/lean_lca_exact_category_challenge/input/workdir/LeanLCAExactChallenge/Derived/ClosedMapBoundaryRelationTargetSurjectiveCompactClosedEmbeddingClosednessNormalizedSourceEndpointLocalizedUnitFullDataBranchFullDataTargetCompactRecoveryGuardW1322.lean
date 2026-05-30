import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataPrimitiveUnitComponentsGuardW1321
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataRoute

/-!
W1322 records the W998 branch-full-data route. W998 derives W715 target
surjective-compact data from the existing W987 branch-full-data provider via
W977/W944 target no-univ data and then feeds W997, but it still leaves the
current one-input W987 obligation unchanged.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW998BranchFullDataInputNamesW1322 : List String :=
  branchFullDataInputNamesW998

theorem canonicalW998BranchFullDataInputNamesW1322_count :
    canonicalW998BranchFullDataInputNamesW1322.length = 1 :=
  branchFullDataInputNamesW998_count

theorem canonicalW998BranchFullDataKeepsCurrentSurfaceW1322 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      canonicalW998BranchFullDataInputNamesW1322.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW998BranchFullDataInputNamesW1322_count]

theorem w998BuildsTargetCompactBranchProviderFromW987W1322
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998
        fullData).targetSurjectiveCompactData =
      targetSurjectiveCompactDataOfBranchFullDataW998 fullData :=
  rfl

theorem w998KeepsBranchFullDataW1322
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998
        fullData).branchFullData =
      fullData :=
  rfl

theorem w998FullDataRunsThroughW997W1322
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    fullDataOfBranchFullDataW998 fullData =
      fullDataOfTargetSurjectiveCompactBranchFullDataW997
        (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998
          fullData) :=
  rfl

theorem w998TargetNoUnivComesFromW987LeavesW1322
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    targetNoUnivDataOfBranchFullDataW998 fullData =
      targetNoUnivDataOfFullDataW977
        (w981LeavesOfFullDataW987 fullData).fullData :=
  rfl

structure MetrizableBranchFullDataTargetCompactRecoveryGuardStateW1322 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataTargetCompactRecoveryGuardStateW1322 :
    MetrizableBranchFullDataTargetCompactRecoveryGuardStateW1322 where
  seed := "w1322-branch-full-data-target-compact-recovery-guard"
  inspectedBoundary :=
    "W998 recovery of W715 target-surjective compact data from the W987\
      branch-full-data provider"
  routeSurfaceCount := canonicalW998BranchFullDataInputNamesW1322.length
  providerSearchResult :=
    "proved: W998 derives target-surjective compact data from W987 and feeds\
      W997, but this keeps the same one-input W987 surface rather than closing\
      the remaining obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1322BranchFullDataTargetCompactRecoveryGuard_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataTargetCompactRecoveryGuardStateW1322;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
