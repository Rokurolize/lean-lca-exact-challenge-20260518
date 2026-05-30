import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataDirectRoutePayloadTransitionGuardW1295
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromTargetNormalizedEndpointW1269
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBranchFullDataCurrentFullDataCycleGuardW1271

/-!
W1296 records the final payload surface reduction and the immediate
current-full-data cycle boundary.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

theorem terminalPayloadSurfaceReducesToBranchFullDataW1296 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269.length ∧
    currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269.length <
      currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    currentFullDataPayloadFromTargetNormalizedEndpointInputNamesW1269_count,
    currentFullDataPayloadFromNormalizedSourceEndpointLocalizedUnitInputNamesW1268_count]
  exact ⟨by decide, by decide⟩

theorem terminalPayloadCycleKeepsBranchFullDataSurfaceW1296 :
    branchFullDataCurrentFullDataCycleInputNamesW1271.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  exact branchFullDataCurrentFullDataCycleDoesNotReduceW1271

structure MetrizableTerminalPayloadCycleBoundaryGuardStateW1296 : Type where
  seed : String
  inspectedRoutes : List String
  routeInputCounts : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTerminalPayloadCycleBoundaryGuardStateW1296 :
    MetrizableTerminalPayloadCycleBoundaryGuardStateW1296 where
  seed := "w1296-terminal-payload-cycle-boundary-guard"
  inspectedRoutes :=
    ["W1269 target-normalized endpoint payload", "W1270 branch-full-data payload",
      "W1271 branch-full-data/current-full-data cycle"]
  routeInputCounts :=
    [("W1268 normalized-source endpoint payload", 3),
      ("W1269 target-normalized endpoint payload", 2),
      ("W1270 branch-full-data payload", 1),
      ("W1271 current-full-data cycle", 1)]
  providerSearchResult :=
    "proved: W1269 and W1270 reduce the payload surface to the one-input W987\
      branch-full-data provider, while W1271 shows the W999 route keeps that\
      one-input cyclic surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1296TerminalPayloadCycleBoundaryGuard_productSuccess :
    (let state :=
        currentMetrizableTerminalPayloadCycleBoundaryGuardStateW1296;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
