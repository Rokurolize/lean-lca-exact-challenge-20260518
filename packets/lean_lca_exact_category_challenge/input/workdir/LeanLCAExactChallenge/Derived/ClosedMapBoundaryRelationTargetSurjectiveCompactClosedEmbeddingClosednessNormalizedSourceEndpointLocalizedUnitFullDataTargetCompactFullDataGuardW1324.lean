import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetCompactBranchWrapperGuardW1323
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromFullDataRoute

/-!
W1324 records the W996 target-surjective-compact full-data route. W996 absorbs
W995's separate W730 boundary/relation data and W986 target/closedness/
normalized-source/endpoint data into one W987 full-data provider, but keeps
W715 target-surjective compact data as a separate assumption, so it expands the
current one-input W987 obligation to two inputs.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW996TargetCompactFullDataInputNamesW1324 : List String :=
  targetSurjectiveCompactFullDataInputNamesW996

theorem canonicalW996TargetCompactFullDataInputNamesW1324_count :
    canonicalW996TargetCompactFullDataInputNamesW1324.length = 2 :=
  targetSurjectiveCompactFullDataInputNamesW996_count

theorem canonicalW996TargetCompactFullDataExpandsCurrentSurfaceW1324 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW996TargetCompactFullDataInputNamesW1324.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW996TargetCompactFullDataInputNamesW1324_count]
  norm_num

theorem w996ProjectsTargetSurjectiveCompactDataW1324
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    targetSurjectiveCompactDataOfTargetSurjectiveCompactFullDataW996 data =
      data.targetSurjectiveCompactData :=
  rfl

theorem w996ProjectsBoundaryRelationFromW987W1324
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    boundaryRelationDataOfTargetSurjectiveCompactFullDataW996 data =
      boundaryRelationDataOfFullDataW987 data.fullData :=
  rfl

theorem w996ProjectsInnerFullDataFromW987W1324
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactFullDataW996 data =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        data.fullData :=
  rfl

theorem w996FullDataRunsThroughW995W1324
    (data : BoundaryRelationTargetSurjectiveCompactFullDataProviderW996) :
    fullDataOfTargetSurjectiveCompactFullDataW996 data =
      fullDataOfTargetSurjectiveCompactTargetProviderW995
        (targetProviderDataOfTargetSurjectiveCompactFullDataW996 data) :=
  rfl

structure MetrizableTargetCompactFullDataGuardStateW1324 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetCompactFullDataGuardStateW1324 :
    MetrizableTargetCompactFullDataGuardStateW1324 where
  seed := "w1324-target-compact-full-data-guard"
  inspectedBoundary :=
    "W996 construction of W995 target-provider data from W715 and W987 full\
      data"
  routeSurfaceCount := canonicalW996TargetCompactFullDataInputNamesW1324.length
  providerSearchResult :=
    "proved: W996 absorbs W730 and W986 through W987 full data, but keeps W715\
      as a separate input, so this route expands the current one-input W987\
      obligation to two inputs"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1324TargetCompactFullDataGuard_productSuccess :
    (let state :=
        currentMetrizableTargetCompactFullDataGuardStateW1324;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
