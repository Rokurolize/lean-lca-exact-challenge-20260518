import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRouteW1163
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceDirectRoute

/-!
W1164 replaces W1163's W981 endpoint/unit-strict-exact provider surface by the
existing W1011 localized-unit-choice surface. W1011 already constructs W981
from W982, and W1164 feeds that provider into W1163.
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

/-- W1164 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData

/-- W1164 constructs the W971 component-field surface from W982 through W1163. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1008 current-full-data surface from W982 through W1163. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1007 branch-full-data surface from W982 through W1163. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1006 target/closedness/normalized-source/endpoint surface from W982 through W1163. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1005 target/closed-embedding-closedness surface from W982 through W1163. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1004 normalized-source/endpoint-localized-unit surface from W982 through W1163. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs the W1003 endpoint-localized-unit surface from W982 through W1163. -/
noncomputable def endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W982 localized-unit-choice surface after routing through W1163. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W981 surface after routing through W1163. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W971 component fields after routing through W1163. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1008 current-full-data surface after routing through W1163. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1007 branch-full-data surface after routing through W1163. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1163. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1163. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1163. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1163. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W982 localized-unit-choice surface after the nested W1163 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W981 surface after the nested W1163 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W971 component fields after the nested W1163 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1008 current-full-data surface after the nested W1163 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the rebuilt W1007 branch-full-data surface after the nested W1163 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1163. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 exposes the twice-rebuilt W971 component fields after routing through W1163. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs W977 current full data from W982 through W1163. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 constructs W987 branch full data from W982 through W1163. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 recovers W715 target surjective-compact data from W982 through W1163. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

/-- W1164 returns the constructed W987 branch full data from W982 through W1163. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1164
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1163
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1164 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1164 : List String :=
  localizedUnitChoiceInputNamesW1011

theorem localizedUnitChoiceInputNamesW1164_count :
    localizedUnitChoiceInputNamesW1164.length = 6 :=
  localizedUnitChoiceInputNamesW1011_count

structure MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1164 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1164 :
    MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1164
    where
  seed := "w1164-localized-unit-choice-to-w1163-unit-strict-exact-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1164",
      "componentFieldsOfLocalizedUnitChoiceW1164",
      "currentFullDataProviderOfLocalizedUnitChoiceW1164",
      "branchFullDataProviderOfLocalizedUnitChoiceW1164",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1164",
      "targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1164",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1164",
      "endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1164",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1164",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1164",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164",
      "currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1164",
      "branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1164",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1164",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1164",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1164",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1164",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1164",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1164",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1164",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1164",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1164",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1164",
      "currentFullDataOfLocalizedUnitChoiceW1164",
      "branchFullDataOfLocalizedUnitChoiceW1164",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1164",
      "fullDataOfLocalizedUnitChoiceW1164",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1164",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1164",
      "localizedUnitChoiceInputNamesW1164_count"]
  providerRepackagingResult :=
    "proved: W1164 constructs the W1163 W981 endpoint/unit-strict-exact\
      provider surface from W982 localized-unit-choice data through W1011\
      and feeds W1163"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1164 inherits W1163/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/\
      W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/W1085/\
      W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/\
      W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/\
      W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/\
      W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998 target surjective-compact recovery\
      after W1011 constructs W981"
  exactAtResult :=
    "proved: the W1164 W982 localized-unit-choice provider surface feeds\
      W1163/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/\
      W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/\
      W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/\
      W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/\
      W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/\
      W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/\
      W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/\
      W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/\
      W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/\
      W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1164
  productSuccessClaimed := false

theorem currentW1164LocalizedUnitChoiceToUnitStrictExactIsoDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1164;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
