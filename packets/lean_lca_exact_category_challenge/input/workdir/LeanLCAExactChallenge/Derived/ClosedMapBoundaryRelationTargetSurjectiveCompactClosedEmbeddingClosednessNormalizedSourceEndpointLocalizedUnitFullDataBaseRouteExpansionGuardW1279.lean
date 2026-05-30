import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataPrimitiveUnitAndBranchWrapperGuardW1278
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute

/-!
W1279 records the remaining W99x base-route expansions around the W987 surface.

W996, W994, W993, W991, and W992 all construct W987 through checked routes, but
each exposes more inputs than the current W1270 one-input W987 provider.
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

def targetSurjectiveCompactFullDataInputNamesW1279 : List String :=
  targetSurjectiveCompactFullDataInputNamesW996

theorem targetSurjectiveCompactFullDataInputNamesW1279_count :
    targetSurjectiveCompactFullDataInputNamesW1279.length = 2 :=
  targetSurjectiveCompactFullDataInputNamesW996_count

def targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279 :
    List String :=
  targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994

theorem targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279_count :
    targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279.length =
      4 :=
  targetSurjectiveCompactNormalizedSourceEndpointInputNamesW994_count

def targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279 :
    List String :=
  targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993

theorem targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279_count :
    targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279.length = 6 :=
  targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993_count

def kernelCokernelTopIsoComponentFieldsInputNamesW1279 :
    List String :=
  kernelCokernelTopIsoComponentFieldsInputNamesW991

theorem kernelCokernelTopIsoComponentFieldsInputNamesW1279_count :
    kernelCokernelTopIsoComponentFieldsInputNamesW1279.length = 13 :=
  kernelCokernelTopIsoComponentFieldsInputNamesW991_count

def targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279 :
    List String :=
  targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992

theorem targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279_count :
    targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279.length =
      13 :=
  targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992_count

theorem baseRouteExpansionsDoNotReduceW1279 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetSurjectiveCompactFullDataInputNamesW1279.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      kernelCokernelTopIsoComponentFieldsInputNamesW1279.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    targetSurjectiveCompactFullDataInputNamesW1279_count,
    targetSurjectiveCompactNormalizedSourceEndpointInputNamesW1279_count,
    targetSurjectiveCompactLocalizedUnitChoiceInputNamesW1279_count,
    kernelCokernelTopIsoComponentFieldsInputNamesW1279_count,
    targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW1279_count]
  norm_num

structure MetrizableBaseRouteExpansionGuardStateW1279 : Type where
  seed : String
  inspectedRoutes : List String
  routeInputCounts : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBaseRouteExpansionGuardStateW1279 :
    MetrizableBaseRouteExpansionGuardStateW1279 where
  seed := "w1279-base-route-expansion-guard"
  inspectedRoutes :=
    ["fullDataOfTargetSurjectiveCompactFullDataW996",
      "fullDataOfTargetSurjectiveCompactNormalizedSourceEndpointW994",
      "fullDataOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "fullDataOfKernelCokernelTopIsoComponentFieldsW991",
      "fullDataOfTargetSurjectiveCompactW992"]
  routeInputCounts :=
    [("W996 target-surjective-compact full-data route", 2),
      ("W994 target-surjective-compact normalized-source/endpoint route", 4),
      ("W993 target-surjective-compact localized-unit-choice route", 6),
      ("W991 kernel/cokernel-top iso component-fields route", 13),
      ("W992 target-surjective-compact kernel/cokernel-top iso route", 13)]
  providerSearchResult :=
    "proved: the remaining W99x base W987-producing routes expose 2, 4, 6,\
      13, and 13 inputs, so none reduces the current W1270 one-input W987\
      provider"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1279BaseRouteExpansionGuard_productSuccess :
    (let state :=
        currentMetrizableBaseRouteExpansionGuardStateW1279;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
