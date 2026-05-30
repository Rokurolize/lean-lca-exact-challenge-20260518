import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1275 records that the checked routes for the W1274 atom candidates are still
larger than the W1270 one-input W987 surface.
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

def boundaryDataRouteCandidateInputNamesW1275 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryExplicitRelationFieldsTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW716

theorem boundaryDataRouteCandidateInputNamesW1275_count :
    boundaryDataRouteCandidateInputNamesW1275.length = 22 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryExplicitRelationFieldsTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW716_count

def relationDataRouteCandidateInputNamesW1275 : List String :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW717

theorem relationDataRouteCandidateInputNamesW1275_count :
    relationDataRouteCandidateInputNamesW1275.length = 21 :=
  metrizableAcceptedStableBoundedDerivedInfinityCategoryRelationDataTargetSurjectiveCompactBoundaryEndpointStrictTopologyGlobalDiagramComponentMappedCokernelClosedInputNamesW717_count

def targetClosednessAtomRouteCandidateInputNamesW1275 : List String :=
  targetClosedEmbeddingClosednessDataInputNamesW984

theorem targetClosednessAtomRouteCandidateInputNamesW1275_count :
    targetClosednessAtomRouteCandidateInputNamesW1275.length = 2 :=
  targetClosedEmbeddingClosednessDataInputNamesW984_count

def normalizedEndpointAtomRouteCandidateInputNamesW1275 : List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950

theorem normalizedEndpointAtomRouteCandidateInputNamesW1275_count :
    normalizedEndpointAtomRouteCandidateInputNamesW1275.length = 3 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataFieldsInputNamesW950_count

theorem atomRouteCandidatesDoNotReduceW1275 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      boundaryDataRouteCandidateInputNamesW1275.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      relationDataRouteCandidateInputNamesW1275.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      targetClosednessAtomRouteCandidateInputNamesW1275.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      normalizedEndpointAtomRouteCandidateInputNamesW1275.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    boundaryDataRouteCandidateInputNamesW1275_count,
    relationDataRouteCandidateInputNamesW1275_count,
    targetClosednessAtomRouteCandidateInputNamesW1275_count,
    normalizedEndpointAtomRouteCandidateInputNamesW1275_count]
  norm_num

structure MetrizableAtomRouteExpansionGuardStateW1275 : Type where
  seed : String
  inspectedRoutes : List String
  expandingCandidates : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableAtomRouteExpansionGuardStateW1275 :
    MetrizableAtomRouteExpansionGuardStateW1275 where
  seed := "w1275-atom-route-expansion-guard"
  inspectedRoutes :=
    ["W716 boundary-data route",
      "W717 relation-data route",
      "W984 target/closed-embedding-closedness atom route",
      "W950 normalized-source/endpoint-localized-unit route"]
  expandingCandidates :=
    [("W716 boundary-data route", 22),
      ("W717 relation-data route", 21),
      ("W984 target/closed-embedding-closedness atom route", 2),
      ("W950 normalized-source/endpoint-localized-unit route", 3)]
  providerSearchResult :=
    "proved: checked routes for W716/W717/W984/W950 all have more inputs\
      than the W1270 one-input W987 surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1275AtomRouteExpansionGuard_productSuccess :
    (let state :=
        currentMetrizableAtomRouteExpansionGuardStateW1275;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
