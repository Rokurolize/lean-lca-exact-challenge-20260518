import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteW1093
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1094 replaces W1093's W1012 endpoint-localized-unit input surface by the
existing W1013 normalized-source/endpoint-localized-unit input surface. W1013 already
constructs the W1003 endpoint-localized-unit provider accepted by W1093.
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

/-- W1094 constructs the W1003 endpoint-localized-unit surface through W1013 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    normalizedSourceEndpointLocalizedUnitData

/-- W1094 constructs the W982 localized-unit-choice surface from W1004 through W1093. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W981 provider surface from W1004 through W1093. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W971 component-field surface from W1004 through W1093. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W1008 current-full-data surface from W1004 through W1093. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W1007 branch-full-data surface from W1004 through W1093. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1093. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1093. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1093. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1093. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W982 localized-unit-choice surface after routing through W1093. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W981 surface after routing through W1093. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W971 component fields after routing through W1093. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1008 current-full-data surface after routing through W1093. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1007 branch-full-data surface after routing through W1093. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1093. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1093. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1093. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1093 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1093. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the twice-rebuilt W981 surface after routing through W1093. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the twice-rebuilt W971 component fields after routing through W1093. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1008 current-full-data surface after the nested W1093 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the rebuilt W1007 branch-full-data surface after the nested W1093 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1093. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 exposes the triply rebuilt W971 component fields after routing through W1093. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs W977 current full data from W1004 through W1093. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 constructs W987 branch full data from W1004 through W1093. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 recovers W715 target surjective-compact data from W1004 through W1093. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

/-- W1094 returns the constructed W987 branch full data from W1004 through W1093. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1094
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1094 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1094_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1094.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1094 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1094 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1094
    where
  seed := "w1094-normalized-source-endpoint-localized-unit-to-w1093-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1094",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1094",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1094",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1094",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1094",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1094",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1094",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1094",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1094",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1094_count"]
  providerRepackagingResult :=
    "proved: W1094 constructs the W1093 W1012 endpoint-localized-unit\
      input surface from W1013 normalized-source/endpoint-localized-unit data\
      and feeds W1093"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1094 inherits W1093/W1092/W1091/W1090/W1089/W1088/W1087/\
      W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1013 constructs the endpoint-localized-unit provider"
  exactAtResult :=
    "proved: the W1094 W1013 normalized-source/endpoint-localized-unit\
      input surface feeds W1093/W1092/W1091/W1090/W1089/W1088/W1087/\
      W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1094
  productSuccessClaimed := false

theorem currentW1094NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1094;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
