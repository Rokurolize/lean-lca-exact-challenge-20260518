import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRouteW1064
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceDirectRoute

/-!
W1065 replaces W1064's W981 endpoint/unit-strict-exact provider surface by the
existing W1011 localized-unit-choice surface. W1011 already constructs W981
from W982, and W1065 feeds that provider into W1064.
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

/-- W1065 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData

/-- W1065 constructs the W971 component-field surface from W982 through W1064. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1008 current-full-data surface from W982 through W1064. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1007 branch-full-data surface from W982 through W1064. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1006 target/closedness/normalized-source/endpoint surface from W982 through W1064. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1005 target/closed-embedding-closedness surface from W982 through W1064. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1004 normalized-source/endpoint-localized-unit surface from W982 through W1064. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs the W1003 endpoint-localized-unit surface from W982 through W1064. -/
noncomputable def endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W982 localized-unit-choice surface after routing through W1064. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W981 surface after routing through W1064. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W971 component fields after routing through W1064. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1008 current-full-data surface after routing through W1064. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1007 branch-full-data surface after routing through W1064. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1064. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1064. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1064. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1064. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W982 localized-unit-choice surface after the nested W1064 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W981 surface after the nested W1064 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W971 component fields after the nested W1064 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1008 current-full-data surface after the nested W1064 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the rebuilt W1007 branch-full-data surface after the nested W1064 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1064. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 exposes the twice-rebuilt W971 component fields after routing through W1064. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs W977 current full data from W982 through W1064. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 constructs W987 branch full data from W982 through W1064. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 recovers W715 target surjective-compact data from W982 through W1064. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

/-- W1065 returns the constructed W987 branch full data from W982 through W1064. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1065
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1065 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1065 : List String :=
  localizedUnitChoiceInputNamesW1011

theorem localizedUnitChoiceInputNamesW1065_count :
    localizedUnitChoiceInputNamesW1065.length = 6 :=
  localizedUnitChoiceInputNamesW1011_count

structure MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1065 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1065 :
    MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1065
    where
  seed := "w1065-localized-unit-choice-to-w1064-unit-strict-exact-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1065",
      "componentFieldsOfLocalizedUnitChoiceW1065",
      "currentFullDataProviderOfLocalizedUnitChoiceW1065",
      "branchFullDataProviderOfLocalizedUnitChoiceW1065",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1065",
      "targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1065",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1065",
      "endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1065",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1065",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1065",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065",
      "currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1065",
      "branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1065",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1065",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1065",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1065",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1065",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1065",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1065",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1065",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1065",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1065",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1065",
      "currentFullDataOfLocalizedUnitChoiceW1065",
      "branchFullDataOfLocalizedUnitChoiceW1065",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1065",
      "fullDataOfLocalizedUnitChoiceW1065",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1065",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1065",
      "localizedUnitChoiceInputNamesW1065_count"]
  providerRepackagingResult :=
    "proved: W1065 constructs the W1064 W981 endpoint/unit-strict-exact\
      provider surface from W982 localized-unit-choice data through W1011\
      and feeds W1064"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1065 inherits W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/\
      W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1011 constructs W981"
  exactAtResult :=
    "proved: the W1065 W982 localized-unit-choice provider surface feeds\
      W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/\
      W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1065
  productSuccessClaimed := false

theorem currentW1065LocalizedUnitChoiceToUnitStrictExactIsoDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1065;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
