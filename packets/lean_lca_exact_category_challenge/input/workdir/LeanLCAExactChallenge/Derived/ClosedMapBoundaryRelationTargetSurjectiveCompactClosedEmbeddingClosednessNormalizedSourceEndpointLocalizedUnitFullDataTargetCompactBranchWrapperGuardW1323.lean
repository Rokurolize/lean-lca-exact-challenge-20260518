import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBranchFullDataTargetCompactRecoveryGuardW1322
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W1323 records the W997 target-surjective-compact branch-full-data wrapper.
W997 packages W715 target-surjective compact data and W987 branch full data
behind one provider, so its surface has one input like the current W987
obligation but still contains the unclosed W987 provider internally.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW997TargetCompactBranchFullDataInputNamesW1323 :
    List String :=
  targetSurjectiveCompactBranchFullDataInputNamesW997

theorem canonicalW997TargetCompactBranchFullDataInputNamesW1323_count :
    canonicalW997TargetCompactBranchFullDataInputNamesW1323.length = 1 :=
  targetSurjectiveCompactBranchFullDataInputNamesW997_count

theorem canonicalW997BranchWrapperKeepsCurrentSurfaceW1323 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      canonicalW997TargetCompactBranchFullDataInputNamesW1323.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW997TargetCompactBranchFullDataInputNamesW1323_count]

theorem w997ProjectsTargetSurjectiveCompactDataW1323
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    targetSurjectiveCompactDataOfTargetSurjectiveCompactBranchFullDataW997 data =
      data.targetSurjectiveCompactData :=
  rfl

theorem w997ProjectsBranchFullDataW1323
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    branchFullDataOfTargetSurjectiveCompactBranchFullDataW997 data =
      data.branchFullData :=
  rfl

theorem w997BuildsW996SurfaceW1323
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
        data).fullData =
      data.branchFullData :=
  rfl

theorem w997FullDataRunsThroughW996W1323
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    fullDataOfTargetSurjectiveCompactBranchFullDataW997 data =
      fullDataOfTargetSurjectiveCompactFullDataW996
        (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
          data) :=
  rfl

structure MetrizableTargetCompactBranchWrapperGuardStateW1323 : Type where
  seed : String
  inspectedBoundary : String
  wrapperSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetCompactBranchWrapperGuardStateW1323 :
    MetrizableTargetCompactBranchWrapperGuardStateW1323 where
  seed := "w1323-target-compact-branch-wrapper-guard"
  inspectedBoundary :=
    "W997 wrapper containing W715 target-surjective compact data and W987\
      branch full data"
  wrapperSurfaceCount :=
    canonicalW997TargetCompactBranchFullDataInputNamesW1323.length
  providerSearchResult :=
    "proved: W997 has a one-input wrapper surface, but that provider still\
      contains both W715 and the unclosed W987 branch-full-data obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1323TargetCompactBranchWrapperGuard_productSuccess :
    (let state :=
        currentMetrizableTargetCompactBranchWrapperGuardStateW1323;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
