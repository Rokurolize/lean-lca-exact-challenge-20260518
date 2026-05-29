import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTargetCompactFullDataGuardW1324
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromTargetProviderRoute

/-!
W1325 records the W995 target-surjective-compact target-provider route. W995
uses the W986 branch-specific target/closedness/normalized-source/endpoint
provider to supply W994's W973 and W950 fields, but the route still exposes the
three-input W730/W715/W986 surface and therefore expands the current one-input
W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW995TargetCompactTargetProviderInputNamesW1325 :
    List String :=
  targetSurjectiveCompactTargetProviderInputNamesW995

theorem canonicalW995TargetCompactTargetProviderInputNamesW1325_count :
    canonicalW995TargetCompactTargetProviderInputNamesW1325.length = 3 :=
  targetSurjectiveCompactTargetProviderInputNamesW995_count

theorem canonicalW995TargetCompactTargetProviderExpandsCurrentSurfaceW1325 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW995TargetCompactTargetProviderInputNamesW1325.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW995TargetCompactTargetProviderInputNamesW1325_count]
  norm_num

theorem w995ProjectsTargetClosedEmbeddingClosednessDataW1325
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    targetClosedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995 data =
      targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w995ProjectsClosedEmbeddingClosednessDataW1325
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    closedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995 data =
      closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
        (targetClosedEmbeddingClosednessDataOfTargetSurjectiveCompactTargetProviderW995
          data) :=
  rfl

theorem w995ProjectsNormalizedEndpointDataW1325
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    normalizedSourceEndpointLocalizedUnitDataOfTargetSurjectiveCompactTargetProviderW995 data =
      normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
        data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
  rfl

theorem w995FullDataRunsThroughW994W1325
    (data :
      BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995) :
    fullDataOfTargetSurjectiveCompactTargetProviderW995 data =
      fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994
        (normalizedSourceEndpointDataOfTargetSurjectiveCompactTargetProviderW995
          data) :=
  rfl

structure MetrizableTargetCompactTargetProviderGuardStateW1325 : Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetCompactTargetProviderGuardStateW1325 :
    MetrizableTargetCompactTargetProviderGuardStateW1325 where
  seed := "w1325-target-compact-target-provider-guard"
  inspectedBoundary :=
    "W995 construction of W994 data from W730, W715, and W986"
  routeSurfaceCount :=
    canonicalW995TargetCompactTargetProviderInputNamesW1325.length
  providerSearchResult :=
    "proved: W995 supplies W994's W973 and W950 fields from W986, but its\
      route surface has three inputs and expands the current one-input W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1325TargetCompactTargetProviderGuard_productSuccess :
    (let state :=
        currentMetrizableTargetCompactTargetProviderGuardStateW1325;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
