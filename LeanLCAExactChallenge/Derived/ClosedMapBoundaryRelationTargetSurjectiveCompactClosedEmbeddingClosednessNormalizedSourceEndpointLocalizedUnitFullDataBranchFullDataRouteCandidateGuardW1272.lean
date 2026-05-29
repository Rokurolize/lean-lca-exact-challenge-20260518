import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1205
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteW1167
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1164
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRouteW1091

/-!
W1272 records the nonterminal W987 provider-search result after W1271.

The W1205 branch-full-data route is a one-input route, but its W1007 input
wraps the same W987 branch-specific full-data provider, so it does not reduce
the W1270 W987 surface. Nearby W987-producing routes from W1167, W1164, and
W1091 expand the surface to three, six, and seven inputs respectively.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

def branchFullDataRouteCandidateInputNamesW1272 : List String :=
  branchFullDataInputNamesW1205

theorem branchFullDataRouteCandidateInputNamesW1272_count :
    branchFullDataRouteCandidateInputNamesW1272.length = 1 :=
  branchFullDataInputNamesW1205_count

theorem branchFullDataRouteCandidateDoesNotReduceW1272 :
    branchFullDataRouteCandidateInputNamesW1272.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length :=
  by
    rw [branchFullDataRouteCandidateInputNamesW1272_count,
      currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

def targetClosedEmbeddingClosednessCandidateInputNamesW1272 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1167

theorem targetClosedEmbeddingClosednessCandidateInputNamesW1272_count :
    targetClosedEmbeddingClosednessCandidateInputNamesW1272.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1167_count

def localizedUnitChoiceCandidateInputNamesW1272 : List String :=
  localizedUnitChoiceInputNamesW1164

theorem localizedUnitChoiceCandidateInputNamesW1272_count :
    localizedUnitChoiceCandidateInputNamesW1272.length = 6 :=
  localizedUnitChoiceInputNamesW1164_count

def unitStrictExactIsoCandidateInputNamesW1272 : List String :=
  unitStrictExactIsoDataInputNamesW1091

theorem unitStrictExactIsoCandidateInputNamesW1272_count :
    unitStrictExactIsoCandidateInputNamesW1272.length = 7 :=
  unitStrictExactIsoDataInputNamesW1091_count

structure MetrizableBranchFullDataRouteCandidateGuardStateW1272 : Type where
  seed : String
  inspectedRoutes : List String
  oneInputCandidate : List String
  expandingCandidates : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataRouteCandidateGuardStateW1272 :
    MetrizableBranchFullDataRouteCandidateGuardStateW1272 where
  seed := "w1272-branch-full-data-route-candidate-guard"
  inspectedRoutes :=
    ["W1205 branch-full-data route",
      "W1167 target/closed-embedding-closedness route",
      "W1164 localized-unit-choice route",
      "W1091 unit-strict-exact-iso route"]
  oneInputCandidate := branchFullDataRouteCandidateInputNamesW1272
  expandingCandidates :=
    [("W1167 target/closed-embedding-closedness route", 3),
      ("W1164 localized-unit-choice route", 6),
      ("W1091 unit-strict-exact-iso route", 7)]
  providerSearchResult :=
    "proved: W1205 has one input but that input is W1007, a wrapper around the\
      same W987 branch-specific full-data provider; W1167/W1164/W1091 expand\
      the W987 search surface to 3/6/7 inputs and are not terminal witnesses"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1272BranchFullDataRouteCandidateGuard_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataRouteCandidateGuardStateW1272;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
