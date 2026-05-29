import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCurrentFullDataPayloadFromBranchFullDataW1270
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryFieldsComponentFieldsMappedCokernelFieldTargetDataEndpointFactsRoute
import LeanLCAExactChallenge.Derived.ClosedMapRelationFieldsBoundaryFieldsComponentFieldsRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationEndpointLocalizedUnitDataPrimitiveFieldRoute

/-!
W1276 records the direct field-split constructors for the W1274 atom candidates.

W907 builds W716 from two raw boundary fields and W908 builds W717 from two raw
relation fields. W984 and W950 are also two-field provider packages. This direct
split still expands the W1270 one-input W987 surface.
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

def directAtomSplitInputNamesW1276 : List String :=
  ["right-open closed-quotient-cover boundary field",
    "source-difference cokernel pi-zero boundary field",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W948 normalized-source-triangulation data provider",
    "W949 endpoint-localized-unit data provider"]

theorem directAtomSplitInputNamesW1276_count :
    directAtomSplitInputNamesW1276.length = 8 :=
  rfl

theorem directAtomSplitDoesNotReduceW1276 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      directAtomSplitInputNamesW1276.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    directAtomSplitInputNamesW1276_count]
  norm_num

def currentBranchBoundaryFieldSplitInputNamesW1276 : List String :=
  closedMapBoundaryFieldsInputNamesW907

theorem currentBranchBoundaryFieldSplitInputNamesW1276_count :
    currentBranchBoundaryFieldSplitInputNamesW1276.length = 31 :=
  closedMapBoundaryFieldsInputNamesW907_count

def currentBranchRelationFieldSplitInputNamesW1276 : List String :=
  closedMapRelationFieldsInputNamesW908

theorem currentBranchRelationFieldSplitInputNamesW1276_count :
    currentBranchRelationFieldSplitInputNamesW1276.length = 32 :=
  closedMapRelationFieldsInputNamesW908_count

theorem currentBranchFieldSplitsDoNotReduceW1276 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      currentBranchBoundaryFieldSplitInputNamesW1276.length ∧
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      currentBranchRelationFieldSplitInputNamesW1276.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    currentBranchBoundaryFieldSplitInputNamesW1276_count,
    currentBranchRelationFieldSplitInputNamesW1276_count]
  norm_num

structure MetrizableDirectAtomSplitGuardStateW1276 : Type where
  seed : String
  inspectedConstructors : List String
  directAtomInputs : List String
  currentBranchExpansions : List (String × Nat)
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableDirectAtomSplitGuardStateW1276 :
    MetrizableDirectAtomSplitGuardStateW1276 where
  seed := "w1276-direct-atom-split-guard"
  inspectedConstructors :=
    ["boundaryDataOfFieldsW907",
      "relationDataOfFieldsW908",
      "TargetNoUnivClosedEmbeddingClosednessDataProviderW984",
      "NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950"]
  directAtomInputs := directAtomSplitInputNamesW1276
  currentBranchExpansions :=
    [("W907 current branch boundary-field split", 31),
      ("W908 current branch relation-field split", 32)]
  providerSearchResult :=
    "proved: direct atom splitting exposes eight raw/provider inputs, and the\
      current W907/W908 branches have 31/32 inputs; none closes the W1270\
      one-input W987 surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1276DirectAtomSplitGuard_productSuccess :
    (let state :=
        currentMetrizableDirectAtomSplitGuardStateW1276;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
