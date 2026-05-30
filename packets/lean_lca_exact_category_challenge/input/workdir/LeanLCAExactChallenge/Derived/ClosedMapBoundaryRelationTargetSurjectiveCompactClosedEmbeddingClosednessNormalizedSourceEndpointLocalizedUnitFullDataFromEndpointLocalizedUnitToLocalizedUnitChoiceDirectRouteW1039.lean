import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1038
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute

/-!
W1039 replaces W1038's W982 localized-unit-choice provider surface by the
existing W1012 endpoint-localized-unit surface. W1012 already constructs W982,
and W1039 feeds that provider into W1038.
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

/-- W1039 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData

/-- W1039 constructs the W981 provider surface from W1003 through W1038. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W971 component-field surface from W1003 through W1038. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W1008 current-full-data surface from W1003 through W1038. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W1007 branch-full-data surface from W1003 through W1038. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1038. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1038. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1038. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1038. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W982 localized-unit-choice surface after routing through W1038. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W981 surface after routing through W1038. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W971 component fields after routing through W1038. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1008 current-full-data surface after routing through W1038. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1007 branch-full-data surface after routing through W1038. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1038. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1038. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1038. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1038 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W982 localized-unit-choice surface after the nested W1038 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W981 surface after the nested W1038 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W971 component fields after the nested W1038 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1008 current-full-data surface after the nested W1038 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the rebuilt W1007 branch-full-data surface after the nested W1038 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1038. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 exposes the twice-rebuilt W971 component fields after routing through W1038. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs W977 current full data from W1003 through W1038. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 constructs W987 branch full data from W1003 through W1038. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 recovers W715 target surjective-compact data from W1003 through W1038. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

/-- W1039 returns the constructed W987 branch full data from W1003 through W1038. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1038
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1039 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1039 : List String :=
  endpointLocalizedUnitInputNamesW1012

theorem endpointLocalizedUnitInputNamesW1039_count :
    endpointLocalizedUnitInputNamesW1039.length = 5 :=
  endpointLocalizedUnitInputNamesW1012_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1039 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1039 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1039
    where
  seed := "w1039-endpoint-localized-unit-to-w1038-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1039",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1039",
      "componentFieldsOfEndpointLocalizedUnitW1039",
      "currentFullDataProviderOfEndpointLocalizedUnitW1039",
      "branchFullDataProviderOfEndpointLocalizedUnitW1039",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1039",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1039",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1039",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1039",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1039",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1039",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1039",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1039",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1039",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1039",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039",
      "currentFullDataOfEndpointLocalizedUnitW1039",
      "branchFullDataOfEndpointLocalizedUnitW1039",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1039",
      "fullDataOfEndpointLocalizedUnitW1039",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1039",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1039",
      "endpointLocalizedUnitInputNamesW1039_count"]
  providerRepackagingResult :=
    "proved: W1039 constructs the W1038 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data through W1012 and feeds W1038"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1039 inherits W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W1012 constructs W982"
  exactAtResult :=
    "proved: the W1039 W1003 endpoint-localized-unit provider surface feeds\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/\
      W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/\
      W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1039
  productSuccessClaimed := false

theorem currentW1039EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1039;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
