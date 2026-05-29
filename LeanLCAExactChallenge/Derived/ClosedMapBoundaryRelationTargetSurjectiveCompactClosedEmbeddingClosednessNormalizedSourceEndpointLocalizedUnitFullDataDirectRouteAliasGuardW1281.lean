import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataOlderChainExpansionGuardW1280
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceToUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRoute

/-!
W1281 records the unnumbered W1016-W1024 direct-route alias layer.

The branch/current wrappers remain at the current W1270 one-input surface;
the component-field and older aliases expand beyond it.
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

def branchFullDataAliasInputNamesW1281 : List String :=
  branchFullDataInputNamesW1016

theorem branchFullDataAliasInputNamesW1281_count :
    branchFullDataAliasInputNamesW1281.length = 1 :=
  branchFullDataInputNamesW1016_count

def currentFullDataAliasInputNamesW1281 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataAliasInputNamesW1281_count :
    currentFullDataAliasInputNamesW1281.length = 1 :=
  currentFullDataInputNamesW1017_count

def componentFieldsAliasInputNamesW1281 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsAliasInputNamesW1281_count :
    componentFieldsAliasInputNamesW1281.length = 18 :=
  componentFieldsInputNamesW1018_count

def unitStrictExactIsoDataAliasInputNamesW1281 : List String :=
  unitStrictExactIsoDataInputNamesW1019

theorem unitStrictExactIsoDataAliasInputNamesW1281_count :
    unitStrictExactIsoDataAliasInputNamesW1281.length = 7 :=
  unitStrictExactIsoDataInputNamesW1019_count

def localizedUnitChoiceAliasInputNamesW1281 : List String :=
  localizedUnitChoiceInputNamesW1020

theorem localizedUnitChoiceAliasInputNamesW1281_count :
    localizedUnitChoiceAliasInputNamesW1281.length = 6 :=
  localizedUnitChoiceInputNamesW1020_count

def endpointLocalizedUnitAliasInputNamesW1281 : List String :=
  endpointLocalizedUnitInputNamesW1021

theorem endpointLocalizedUnitAliasInputNamesW1281_count :
    endpointLocalizedUnitAliasInputNamesW1281.length = 5 :=
  endpointLocalizedUnitInputNamesW1021_count

def normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281 :
    List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1022

theorem normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281_count :
    normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1022_count

def targetClosedEmbeddingClosednessAliasInputNamesW1281 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1023

theorem targetClosedEmbeddingClosednessAliasInputNamesW1281_count :
    targetClosedEmbeddingClosednessAliasInputNamesW1281.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1023_count

def targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281 :
    List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1024

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281.length = 2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1024_count

theorem directRouteWrappersKeepCurrentSurfaceW1281 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      branchFullDataAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      currentFullDataAliasInputNamesW1281.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    branchFullDataAliasInputNamesW1281_count,
    currentFullDataAliasInputNamesW1281_count]
  exact ⟨rfl, rfl⟩

theorem directRouteAliasesDoNotReduceW1281 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      componentFieldsAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      unitStrictExactIsoDataAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      localizedUnitChoiceAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      endpointLocalizedUnitAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetClosedEmbeddingClosednessAliasInputNamesW1281.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    componentFieldsAliasInputNamesW1281_count,
    unitStrictExactIsoDataAliasInputNamesW1281_count,
    localizedUnitChoiceAliasInputNamesW1281_count,
    endpointLocalizedUnitAliasInputNamesW1281_count,
    normalizedSourceEndpointLocalizedUnitAliasInputNamesW1281_count,
    targetClosedEmbeddingClosednessAliasInputNamesW1281_count,
    targetClosedEmbeddingClosednessNormalizedSourceEndpointAliasInputNamesW1281_count]
  norm_num

structure MetrizableDirectRouteAliasGuardStateW1281 : Type where
  seed : String
  inspectedRoutes : List String
  routeInputCounts : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableDirectRouteAliasGuardStateW1281 :
    MetrizableDirectRouteAliasGuardStateW1281 where
  seed := "w1281-direct-route-alias-guard"
  inspectedRoutes :=
    ["fullDataOfBranchFullDataW1016",
      "fullDataOfCurrentFullDataW1017",
      "fullDataOfComponentFieldsW1018",
      "fullDataOfUnitStrictExactIsoDataW1019",
      "fullDataOfLocalizedUnitChoiceW1020",
      "fullDataOfEndpointLocalizedUnitW1021",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "fullDataOfTargetClosedEmbeddingClosednessW1023",
      "fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1024"]
  routeInputCounts :=
    [("W1016 branch-full-data wrapper", 1),
      ("W1017 current-full-data wrapper", 1),
      ("W1018 component-field alias", 18),
      ("W1019 unit-strict-exact-iso-data alias", 7),
      ("W1020 localized-unit-choice alias", 6),
      ("W1021 endpoint-localized-unit alias", 5),
      ("W1022 normalized-source/endpoint-localized-unit alias", 4),
      ("W1023 target/closed-embedding-closedness alias", 3),
      ("W1024 target/closed-embedding-closedness/normalized-endpoint alias", 2)]
  providerSearchResult :=
    "proved: W1016 and W1017 preserve the current W1270 one-input surface,\
      while W1018-W1024 expose 18, 7, 6, 5, 4, 3, and 2 inputs"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1281DirectRouteAliasGuard_productSuccess :
    (let state :=
        currentMetrizableDirectRouteAliasGuardStateW1281;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
