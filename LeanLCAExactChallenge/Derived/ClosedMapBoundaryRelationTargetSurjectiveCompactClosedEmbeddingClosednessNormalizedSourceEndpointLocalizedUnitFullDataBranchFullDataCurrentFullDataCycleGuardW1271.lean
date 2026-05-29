import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataRoute

/-!
W1271 guards the final one-input surface against a tempting cycle: W999 can
construct W987 branch full data from W977 current full data, but W1270 is using
W987 branch full data to construct that W977 current full-data payload.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def branchFullDataCurrentFullDataCycleInputNamesW1271 : List String :=
  currentFullDataInputNamesW999

theorem branchFullDataCurrentFullDataCycleInputNamesW1271_count :
    branchFullDataCurrentFullDataCycleInputNamesW1271.length = 1 :=
  currentFullDataInputNamesW999_count

theorem branchFullDataCurrentFullDataCycleDoesNotReduceW1271 :
    branchFullDataCurrentFullDataCycleInputNamesW1271.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [branchFullDataCurrentFullDataCycleInputNamesW1271_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

structure MetrizableBranchFullDataCurrentFullDataCycleGuardStateW1271 :
    Type where
  seed : String
  declarations : List String
  cycleResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataCurrentFullDataCycleGuardStateW1271 :
    MetrizableBranchFullDataCurrentFullDataCycleGuardStateW1271
    where
  seed := "w1271-branch-full-data-current-full-data-cycle-guard"
  declarations :=
    ["branchFullDataCurrentFullDataCycleInputNamesW1271",
      "branchFullDataCurrentFullDataCycleInputNamesW1271_count",
      "branchFullDataCurrentFullDataCycleDoesNotReduceW1271",
      "branchFullDataOfCurrentFullDataW999",
      "currentFullDataPayloadOfBranchFullDataW1270"]
  cycleResult :=
    "proved: W999 constructs W987 branch full data from a W977 current\
      full-data payload, while W1270 constructs that W977 payload from W987;\
      this is a one-input cycle, not a completion witness"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1271BranchFullDataCurrentFullDataCycleGuard_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataCurrentFullDataCycleGuardStateW1271;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
