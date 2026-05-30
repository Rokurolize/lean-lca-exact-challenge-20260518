import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromTargetProviderRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsDirectRoute

/-!
W1273 records that opening the remaining W987 provider through nearby field
routes expands, rather than closes, the W1270 one-input surface.
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

def targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273 :
    List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273.length =
      2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006_count

def targetProviderCandidateInputNamesW1273 : List String :=
  targetSurjectiveCompactTargetProviderInputNamesW995

theorem targetProviderCandidateInputNamesW1273_count :
    targetProviderCandidateInputNamesW1273.length = 3 :=
  targetSurjectiveCompactTargetProviderInputNamesW995_count

def componentFieldsCandidateInputNamesW1273 : List String :=
  componentFieldsInputNamesW1009

theorem componentFieldsCandidateInputNamesW1273_count :
    componentFieldsCandidateInputNamesW1273.length = 18 :=
  componentFieldsInputNamesW1009_count

theorem fieldExpansionCandidatesDoNotReduceW1273 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetProviderCandidateInputNamesW1273.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      componentFieldsCandidateInputNamesW1273.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    targetClosedEmbeddingClosednessNormalizedSourceEndpointCandidateInputNamesW1273_count,
    targetProviderCandidateInputNamesW1273_count,
    componentFieldsCandidateInputNamesW1273_count]
  norm_num

structure MetrizableFieldExpansionCandidateGuardStateW1273 : Type where
  seed : String
  inspectedRoutes : List String
  expandingCandidates : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableFieldExpansionCandidateGuardStateW1273 :
    MetrizableFieldExpansionCandidateGuardStateW1273 where
  seed := "w1273-field-expansion-candidate-guard"
  inspectedRoutes :=
    ["W1006 target/closed-embedding-closedness/normalized-source/endpoint route",
      "W995 target-provider route",
      "W1009 component-field route"]
  expandingCandidates :=
    [("W1006 target/closed-embedding-closedness/normalized-source/endpoint route", 2),
      ("W995 target-provider route", 3),
      ("W1009 component-field route", 18)]
  providerSearchResult :=
    "proved: W1006 opens W987 into W730 plus W986, W995 opens it into W730\
      plus W715 plus W986, and W1009 opens it through component fields; all\
      expand the W1270 one-input W987 surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1273FieldExpansionCandidateGuard_productSuccess :
    (let state :=
        currentMetrizableFieldExpansionCandidateGuardStateW1273;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
