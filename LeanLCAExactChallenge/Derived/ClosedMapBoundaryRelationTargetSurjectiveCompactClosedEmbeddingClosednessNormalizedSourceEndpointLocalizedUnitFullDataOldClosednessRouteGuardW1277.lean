import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataDirectAtomSplitGuardW1276
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1277 records why the older W952 one-provider route is not a discharge of the
current W987 provider.

W952 is also a one-input full-provider surface, but it routes target closedness
through W947 and W725. The current W987 path keeps the W984/W973
closed-embedding-specific provider surface. Replacing W987 by W952 therefore
does not reduce the one remaining input and would switch to the older
closedness branch shape.
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

def oldClosednessFullProviderInputNamesW1277 : List String :=
  closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952

theorem oldClosednessFullProviderInputNamesW1277_count :
    oldClosednessFullProviderInputNamesW1277.length = 1 :=
  closedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldsInputNamesW952_count

theorem oldClosednessFullProviderDoesNotReduceW1277 :
    oldClosednessFullProviderInputNamesW1277.length =
      currentFullDataPayloadFromBranchFullDataInputNamesW1270.length := by
  rw [oldClosednessFullProviderInputNamesW1277_count,
    currentFullDataPayloadFromBranchFullDataInputNamesW1270_count]

def oldTargetClosednessRouteInputNamesW1277 : List String :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947

theorem oldTargetClosednessRouteInputNamesW1277_count :
    oldTargetClosednessRouteInputNamesW1277.length = 6 :=
  closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW947_count

def branchSpecificTargetClosednessInputNamesW1277 : List String :=
  targetClosedEmbeddingClosednessDataInputNamesW984

theorem branchSpecificTargetClosednessInputNamesW1277_count :
    branchSpecificTargetClosednessInputNamesW1277.length = 2 :=
  targetClosedEmbeddingClosednessDataInputNamesW984_count

theorem oldTargetClosednessRouteExpandsBranchSpecificSurfaceW1277 :
    branchSpecificTargetClosednessInputNamesW1277.length <
      oldTargetClosednessRouteInputNamesW1277.length := by
  rw [branchSpecificTargetClosednessInputNamesW1277_count,
    oldTargetClosednessRouteInputNamesW1277_count]
  norm_num

structure MetrizableOldClosednessRouteGuardStateW1277 : Type where
  seed : String
  inspectedProviders : List String
  oldFullProviderInputs : List String
  currentFullProviderInputs : List String
  oldClosednessInputs : List String
  branchSpecificClosednessInputs : List String
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableOldClosednessRouteGuardStateW1277 :
    MetrizableOldClosednessRouteGuardStateW1277 where
  seed := "w1277-old-closedness-route-guard"
  inspectedProviders :=
    ["BoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW952",
      "TargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW951",
      "TargetNoUnivMembershipClosednessDataProviderW947",
      "MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725",
      "TargetNoUnivClosedEmbeddingClosednessDataProviderW984",
      "ClosedEmbeddingClosednessDataProviderW973"]
  oldFullProviderInputs := oldClosednessFullProviderInputNamesW1277
  currentFullProviderInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  oldClosednessInputs := oldTargetClosednessRouteInputNamesW1277
  branchSpecificClosednessInputs := branchSpecificTargetClosednessInputNamesW1277
  providerSearchResult :=
    "proved: W952 is another one-input provider surface and therefore does not\
      reduce the current W987 input; its W947/W725 closedness route expands to\
      the older six-input target/closedness surface instead of the W984/W973\
      closed-embedding-specific surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1277OldClosednessRouteGuard_productSuccess :
    (let state :=
        currentMetrizableOldClosednessRouteGuardStateW1277;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
