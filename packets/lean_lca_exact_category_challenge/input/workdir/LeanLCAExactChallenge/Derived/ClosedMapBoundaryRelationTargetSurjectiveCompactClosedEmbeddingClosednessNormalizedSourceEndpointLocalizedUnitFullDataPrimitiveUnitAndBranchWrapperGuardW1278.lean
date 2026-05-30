import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataOldClosednessRouteGuardW1277
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromPrimitiveUnitComponentsRoute

/-!
W1278 records two remaining base-route candidates around the W987 surface.

W998 is a one-input route from W987 back through the W997 target-surjective-
compact wrapper; it therefore does not reduce the current W1270 one-input W987
surface. W990 is a genuine primitive-unit-components constructor for W987, but
its checked input ledger has eight entries.
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

def branchWrapperInputNamesW1278 : List String :=
  branchFullDataInputNamesW998

theorem branchWrapperInputNamesW1278_count :
    branchWrapperInputNamesW1278.length = 1 :=
  branchFullDataInputNamesW998_count

theorem branchWrapperDoesNotReduceW1278 :
    branchWrapperInputNamesW1278.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [branchWrapperInputNamesW1278_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

def targetSurjectiveCompactBranchWrapperInputNamesW1278 : List String :=
  targetSurjectiveCompactBranchFullDataInputNamesW997

theorem targetSurjectiveCompactBranchWrapperInputNamesW1278_count :
    targetSurjectiveCompactBranchWrapperInputNamesW1278.length = 1 :=
  targetSurjectiveCompactBranchFullDataInputNamesW997_count

theorem targetSurjectiveCompactBranchWrapperDoesNotReduceW1278 :
    targetSurjectiveCompactBranchWrapperInputNamesW1278.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [targetSurjectiveCompactBranchWrapperInputNamesW1278_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

def primitiveUnitComponentsInputNamesW1278 : List String :=
  primitiveUnitComponentsInputNamesW990

theorem primitiveUnitComponentsInputNamesW1278_count :
    primitiveUnitComponentsInputNamesW1278.length = 8 :=
  primitiveUnitComponentsInputNamesW990_count

theorem primitiveUnitComponentsRouteDoesNotReduceW1278 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      primitiveUnitComponentsInputNamesW1278.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    primitiveUnitComponentsInputNamesW1278_count]
  norm_num

structure MetrizablePrimitiveUnitAndBranchWrapperGuardStateW1278 : Type where
  seed : String
  inspectedRoutes : List String
  branchWrapperInputs : List String
  targetSurjectiveCompactBranchWrapperInputs : List String
  primitiveUnitInputs : List String
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizablePrimitiveUnitAndBranchWrapperGuardStateW1278 :
    MetrizablePrimitiveUnitAndBranchWrapperGuardStateW1278 where
  seed := "w1278-primitive-unit-and-branch-wrapper-guard"
  inspectedRoutes :=
    ["fullDataOfBranchFullDataW998",
      "BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997",
      "fullDataOfPrimitiveUnitComponentsW990"]
  branchWrapperInputs := branchWrapperInputNamesW1278
  targetSurjectiveCompactBranchWrapperInputs :=
    targetSurjectiveCompactBranchWrapperInputNamesW1278
  primitiveUnitInputs := primitiveUnitComponentsInputNamesW1278
  providerSearchResult :=
    "proved: W998 and W997 are one-input wrapper surfaces around W987 and do\
      not reduce the current W1270 W987 input; W990 constructs W987 only after\
      expanding to eight primitive-unit-component inputs"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1278PrimitiveUnitAndBranchWrapperGuard_productSuccess :
    (let state :=
        currentMetrizablePrimitiveUnitAndBranchWrapperGuardStateW1278;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
