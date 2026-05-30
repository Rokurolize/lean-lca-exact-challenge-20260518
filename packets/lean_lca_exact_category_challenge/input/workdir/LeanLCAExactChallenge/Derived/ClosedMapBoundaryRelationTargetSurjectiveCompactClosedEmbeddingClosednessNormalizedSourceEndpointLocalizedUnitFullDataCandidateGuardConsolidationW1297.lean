import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTerminalPayloadCycleBoundaryGuardW1296
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataBranchFullDataRouteCandidateGuardW1272
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFieldExpansionCandidateGuardW1273
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderAtomExpansionGuardW1274
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataAtomRouteExpansionGuardW1275
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataDirectAtomSplitGuardW1276
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataOldClosednessRouteGuardW1277

/-!
W1297 consolidates the W1272-W1277 candidate guards around the remaining W987
one-input surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

theorem candidateOneInputSurfacesKeepCurrentSurfaceW1297 :
    branchFullDataRouteCandidateInputNamesW1272.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length ∧
    oldClosednessFullProviderInputNamesW1277.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  exact ⟨branchFullDataRouteCandidateDoesNotReduceW1272,
    oldClosednessFullProviderDoesNotReduceW1277⟩

theorem immediateCandidateExpansionsDoNotReduceW1297 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetClosedEmbeddingClosednessCandidateInputNamesW1272.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      localizedUnitChoiceCandidateInputNamesW1272.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      unitStrictExactIsoCandidateInputNamesW1272.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      oldTargetClosednessRouteInputNamesW1277.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    targetClosedEmbeddingClosednessCandidateInputNamesW1272_count,
    localizedUnitChoiceCandidateInputNamesW1272_count,
    unitStrictExactIsoCandidateInputNamesW1272_count,
    oldTargetClosednessRouteInputNamesW1277_count]
  norm_num

theorem previouslyRecordedCandidateExpansionsDoNotReduceW1297 :
    (currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        targetProviderCandidateInputNamesW1273.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        componentFieldsCandidateInputNamesW1273.length) ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      fullDataProviderAtomInputNamesW1274.length ∧
    (currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        boundaryDataRouteCandidateInputNamesW1275.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        relationDataRouteCandidateInputNamesW1275.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        targetClosednessAtomRouteCandidateInputNamesW1275.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        normalizedEndpointAtomRouteCandidateInputNamesW1275.length) ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      directAtomSplitInputNamesW1276.length ∧
    (currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        currentBranchBoundaryFieldSplitInputNamesW1276.length ∧
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
        currentBranchRelationFieldSplitInputNamesW1276.length) := by
  exact ⟨fieldExpansionCandidatesDoNotReduceW1273,
    fullDataProviderAtomExpansionDoesNotReduceW1274,
    atomRouteCandidatesDoNotReduceW1275,
    directAtomSplitDoesNotReduceW1276,
    currentBranchFieldSplitsDoNotReduceW1276⟩

structure MetrizableCandidateGuardConsolidationStateW1297 : Type where
  seed : String
  oneInputSurfaces : List String
  expandingCandidateCounts : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCandidateGuardConsolidationStateW1297 :
    MetrizableCandidateGuardConsolidationStateW1297 where
  seed := "w1297-candidate-guard-consolidation"
  oneInputSurfaces :=
    ["W1272 W1205 branch-full-data route candidate",
      "W1277 W952 old closedness full-provider route"]
  expandingCandidateCounts :=
    [("W1272 target-closed-embedding-closedness candidate", 3),
      ("W1272 localized-unit-choice candidate", 6),
      ("W1272 unit-strict-exact-iso candidate", 7),
      ("W1273 field expansion candidates", 2),
      ("W1273 field expansion candidates", 3),
      ("W1273 field expansion candidates", 18),
      ("W1274 atom opening", 4), ("W1275 atom routes", 22),
      ("W1275 atom routes", 21), ("W1275 atom routes", 2),
      ("W1275 atom routes", 3), ("W1276 direct atom split", 8),
      ("W1276 current branch field splits", 31),
      ("W1276 current branch field splits", 32),
      ("W1277 old target closedness route", 6)]
  providerSearchResult :=
    "proved: W1272 and W1277 one-input alternatives keep the current W1270\
      surface, while W1272-W1277 expansion candidates have larger surfaces"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1297CandidateGuardConsolidation_productSuccess :
    (let state :=
        currentMetrizableCandidateGuardConsolidationStateW1297;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
