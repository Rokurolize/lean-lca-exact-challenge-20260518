import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W1274 records the atom-level opening of the remaining W987 provider.

The W987 package contains W730 boundary/relation data and W986
target/closedness/normalized-source/endpoint-localized data. Opening those two
packages gives W716/W717 and W984/W950 provider atoms, so this route expands the
W1270 one-input surface to four lower-level inputs.
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

def boundaryRelationAtomInputNamesW1274 : List String :=
  ["W716 WPP boundary data provider",
    "W717 closed natural transformation relation data provider"]

theorem boundaryRelationAtomInputNamesW1274_count :
    boundaryRelationAtomInputNamesW1274.length = 2 :=
  rfl

def targetNormalizedEndpointAtomInputNamesW1274 : List String :=
  ["W984 target/closed-embedding-closedness data provider",
    "W950 normalized-source/endpoint-localized-unit data provider"]

theorem targetNormalizedEndpointAtomInputNamesW1274_count :
    targetNormalizedEndpointAtomInputNamesW1274.length = 2 :=
  rfl

def fullDataProviderAtomInputNamesW1274 : List String :=
  boundaryRelationAtomInputNamesW1274 ++
    targetNormalizedEndpointAtomInputNamesW1274

theorem fullDataProviderAtomInputNamesW1274_count :
    fullDataProviderAtomInputNamesW1274.length = 4 := by
  rw [fullDataProviderAtomInputNamesW1274,
    List.length_append,
    boundaryRelationAtomInputNamesW1274_count,
    targetNormalizedEndpointAtomInputNamesW1274_count]

theorem fullDataProviderAtomExpansionDoesNotReduceW1274 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      fullDataProviderAtomInputNamesW1274.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    fullDataProviderAtomInputNamesW1274_count]
  norm_num

structure MetrizableFullDataProviderAtomExpansionGuardStateW1274 : Type where
  seed : String
  openedPackages : List String
  atomInputs : List String
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableFullDataProviderAtomExpansionGuardStateW1274 :
    MetrizableFullDataProviderAtomExpansionGuardStateW1274 where
  seed := "w1274-full-data-provider-atom-expansion-guard"
  openedPackages :=
    ["W730 boundary/relation data provider",
      "W986 target/closedness/normalized-source/endpoint-localized data provider"]
  atomInputs := fullDataProviderAtomInputNamesW1274
  providerSearchResult :=
    "proved: opening W987 through W730 and W986 exposes W716/W717/W984/W950\
      provider atoms, increasing the W1270 one-input surface to four inputs"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1274FullDataProviderAtomExpansionGuard_productSuccess :
    (let state :=
        currentMetrizableFullDataProviderAtomExpansionGuardStateW1274;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
