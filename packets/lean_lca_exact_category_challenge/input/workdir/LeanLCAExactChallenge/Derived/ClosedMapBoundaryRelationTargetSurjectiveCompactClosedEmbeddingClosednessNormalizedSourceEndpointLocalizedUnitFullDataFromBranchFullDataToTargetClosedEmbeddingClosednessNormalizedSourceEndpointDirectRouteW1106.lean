import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteW1105
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute

/-!
W1106 replaces W1105's W1006 target/closedness/normalized-source/endpoint
surface by the existing W1016 branch-full-data route. W1016 already constructs
W1006, and W1106 feeds that provider into W1105.
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

/-- W1106 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1016 data. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
    branchFullData

/-- W1106 constructs the W1005 target/closed-embedding-closedness surface from W1007 through W1105. -/
def targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1007 through W1105. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W1003 endpoint-localized-unit surface from W1007 through W1105. -/
def endpointLocalizedUnitDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W982 localized-unit-choice surface from W1007 through W1105. -/
def localizedUnitChoiceDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W981 provider surface from W1007 through W1105. -/
noncomputable def unitStrictExactIsoDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W971 component-field surface from W1007 through W1105. -/
noncomputable def componentFieldsOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W1008 current-full-data surface from W1007 through W1105. -/
noncomputable def currentFullDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs the W1007 branch-full-data surface from W1007 through W1105. -/
noncomputable def branchFullDataProviderOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface through W1105. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1105. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1105. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1105. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W982 localized-unit-choice surface after routing through W1105. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W981 surface after routing through W1105. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W971 component fields after routing through W1105. -/
noncomputable def componentFieldsOfComponentFieldsOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W1008 current-full-data surface after routing through W1105. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the rebuilt W1007 branch-full-data surface after routing through W1105. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1105. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 exposes the twice-rebuilt W971 component fields after routing through W1105. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs W977 current full data from W1007 through W1105. -/
noncomputable def currentFullDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 constructs W987 branch full data from W1007 through W1105. -/
noncomputable def branchFullDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 recovers W715 target surjective-compact data from W1007 through W1105. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

/-- W1106 returns the constructed W987 branch full data from W1007 through W1105. -/
noncomputable def fullDataOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

theorem directBoundedLeftCalculusOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW1106
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1105
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106
      branchFullData)

def branchFullDataInputNamesW1106 : List String :=
  branchFullDataInputNamesW1016

theorem branchFullDataInputNamesW1106_count :
    branchFullDataInputNamesW1106.length = 1 :=
  branchFullDataInputNamesW1016_count

structure MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1106 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1106 :
    MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1106
    where
  seed := "w1106-branch-full-data-to-w1105-target-closed-embedding-closedness-normalized-source-endpoint-route"
  declarations :=
    ["targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1106",
      "targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1106",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1106",
      "endpointLocalizedUnitDataProviderOfBranchFullDataW1106",
      "localizedUnitChoiceDataOfBranchFullDataW1106",
      "unitStrictExactIsoDataOfBranchFullDataW1106",
      "componentFieldsOfBranchFullDataW1106",
      "currentFullDataProviderOfBranchFullDataW1106",
      "branchFullDataProviderOfBranchFullDataW1106",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1106",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1106",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1106",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1106",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1106",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1106",
      "componentFieldsOfComponentFieldsOfBranchFullDataW1106",
      "currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1106",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataW1106",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1106",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1106",
      "currentFullDataOfBranchFullDataW1106",
      "branchFullDataOfBranchFullDataW1106",
      "targetSurjectiveCompactDataOfBranchFullDataW1106",
      "fullDataOfBranchFullDataW1106",
      "directBoundedLeftCalculusOfBranchFullDataW1106",
      "boundedDerivedInfinityCategoryOfBranchFullDataW1106",
      "branchFullDataInputNamesW1106_count"]
  providerRepackagingResult :=
    "proved: W1106 constructs the W1105 W1006 target/closedness/normalized-source/endpoint\
      provider surface from W1016 branch-full-data and feeds W1105"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1106 inherits W1105/W1104/W1103/W1102/W1101/W1100/\
      W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/\
      W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/\
      W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/\
      W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/\
      W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/\
      W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/\
      W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/\
      W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1016 constructs W1006"
  exactAtResult :=
    "proved: the W1106 W1016 branch-full-data provider surface feeds\
      W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := branchFullDataInputNamesW1106
  productSuccessClaimed := false

theorem currentW1106BranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1106;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
