import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteW1156
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1157 replaces W1156's W1012 endpoint-localized-unit input surface by the
existing W1013 normalized-source/endpoint-localized-unit input surface. W1013 already
constructs the W1003 endpoint-localized-unit provider accepted by W1156.
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

/-- W1157 constructs the W1003 endpoint-localized-unit surface through W1013 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    normalizedSourceEndpointLocalizedUnitData

/-- W1157 constructs the W982 localized-unit-choice surface from W1004 through W1156. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W981 provider surface from W1004 through W1156. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W971 component-field surface from W1004 through W1156. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W1008 current-full-data surface from W1004 through W1156. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W1007 branch-full-data surface from W1004 through W1156. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1156. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1156. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1156. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1156. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W982 localized-unit-choice surface after routing through W1156. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W981 surface after routing through W1156. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W971 component fields after routing through W1156. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1008 current-full-data surface after routing through W1156. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1007 branch-full-data surface after routing through W1156. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1156. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1156. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1156. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1156 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1156. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the twice-rebuilt W981 surface after routing through W1156. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the twice-rebuilt W971 component fields after routing through W1156. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1008 current-full-data surface after the nested W1156 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the rebuilt W1007 branch-full-data surface after the nested W1156 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1156. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 exposes the triply rebuilt W971 component fields after routing through W1156. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs W977 current full data from W1004 through W1156. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 constructs W987 branch full data from W1004 through W1156. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 recovers W715 target surjective-compact data from W1004 through W1156. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

/-- W1157 returns the constructed W987 branch full data from W1004 through W1156. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1157
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1156
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1157 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1157_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1157.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1013_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1157 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1157 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1157
    where
  seed := "w1157-normalized-source-endpoint-localized-unit-to-w1156-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1157",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1157",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1157",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1157",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1157",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1157",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1157",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1157",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1157",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1157_count"]
  providerRepackagingResult :=
    "proved: W1157 constructs the W1156 W1012 endpoint-localized-unit\
      input surface from W1013 normalized-source/endpoint-localized-unit data\
      and feeds W1156"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1157 inherits W1156/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1013 constructs the endpoint-localized-unit provider"
  exactAtResult :=
    "proved: the W1157 W1013 normalized-source/endpoint-localized-unit\
      input surface feeds W1156/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1157
  productSuccessClaimed := false

theorem currentW1157NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1157;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
