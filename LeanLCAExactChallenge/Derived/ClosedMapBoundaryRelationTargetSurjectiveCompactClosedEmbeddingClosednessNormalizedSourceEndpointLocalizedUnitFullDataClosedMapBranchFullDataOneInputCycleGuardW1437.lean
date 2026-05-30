import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataStableConvergenceFieldSplitGuardW1436
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBranchFullDataCurrentFullDataCycleGuardW1271

/-!
W1437 pins down the remaining W1436 branch-full-data surface. The W1169
surface is the W1016/W1007 branch-full-data surface, and W1007's sole input is
the W987 branch-specific full-data provider. This matches the W1270/W1271
one-input current-full-data cycle, so it is boundary evidence rather than a
product-success witness.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- The W1007 branch-full-data input is exactly the wrapped W987 provider. -/
theorem w1007BranchFullDataInputIsW987W1437
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    branchFullDataInputOfBranchFullDataW1007 branchFullData =
      branchFullData.branchFullData :=
  rfl

/-- The W1169 branch-full-data surface is the same one-input W1007 surface. -/
theorem w1169BranchFullDataInputNamesMatchW1007W1437 :
    branchFullDataInputNamesW1169 = branchFullDataInputNamesW1007 :=
  rfl

/-- The W1169 surface has the same count as W1007's W987 input surface. -/
theorem w1169BranchFullDataInputCountMatchesW1007W1437 :
    branchFullDataInputNamesW1169.length =
      branchFullDataInputNamesW1007.length :=
  congrArg List.length w1169BranchFullDataInputNamesMatchW1007W1437

/-- The W1169 surface count matches W1270's W987-to-W977 payload surface. -/
theorem w1169BranchFullDataInputCountMatchesW1270W1437 :
    branchFullDataInputNamesW1169.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [branchFullDataInputNamesW1169_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

/-- The W1169 surface count also matches the W1271 current-full-data cycle. -/
theorem w1169BranchFullDataInputCountMatchesW1271W1437 :
    branchFullDataInputNamesW1169.length =
      branchFullDataCurrentFullDataCycleInputNamesW1271.length := by
  rw [branchFullDataInputNamesW1169_count,
    branchFullDataCurrentFullDataCycleInputNamesW1271_count]

/-- The W1007 W987 input count matches W1270's branch-full-data payload surface. -/
theorem w1007BranchFullDataInputCountMatchesW1270W1437 :
    branchFullDataInputNamesW1007.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [branchFullDataInputNamesW1007_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

/-- W1437 keeps the one remaining W987 input explicit. -/
theorem w1437ClosedMapBranchFullDataUnderlyingW987InputCount :
    branchFullDataInputNamesW1007.length = 1 :=
  branchFullDataInputNamesW1007_count

/-- Current W1437 nonterminal surface/cycle state. -/
structure ClosedMapBranchFullDataOneInputCycleStateW1437 : Type where
  seed : String
  declarations : List String
  surfaceProjectionResult : String
  cycleBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1437 records that W1436's single branch-full-data input is still the W987 surface. -/
def currentClosedMapBranchFullDataOneInputCycleStateW1437 :
    ClosedMapBranchFullDataOneInputCycleStateW1437 where
  seed := "w1437-closed-map-branch-full-data-one-input-cycle"
  declarations :=
    ["w1007BranchFullDataInputIsW987W1437",
      "w1169BranchFullDataInputNamesMatchW1007W1437",
      "w1169BranchFullDataInputCountMatchesW1007W1437",
      "w1169BranchFullDataInputCountMatchesW1270W1437",
      "w1169BranchFullDataInputCountMatchesW1271W1437",
      "w1007BranchFullDataInputCountMatchesW1270W1437",
      "w1437ClosedMapBranchFullDataUnderlyingW987InputCount"]
  surfaceProjectionResult :=
    "proved: the W1436/W1169 one-input branch-full-data surface is the W1007\
      surface, and W1007's wrapped input is the W987 branch-specific full-data\
      provider"
  cycleBoundaryResult :=
    "proved: the W1169/W1007 one-input surface has the same count as the\
      W1270 branch-full-data-to-current-full-data payload and the W1271\
      current-full-data cycle, so this records the remaining W987 obligation\
      rather than product completion"
  remainingInputs := branchFullDataInputNamesW1007
  productSuccessClaimed := false

theorem currentW1437ClosedMapBranchFullDataOneInputCycle_productSuccess :
    currentClosedMapBranchFullDataOneInputCycleStateW1437.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
