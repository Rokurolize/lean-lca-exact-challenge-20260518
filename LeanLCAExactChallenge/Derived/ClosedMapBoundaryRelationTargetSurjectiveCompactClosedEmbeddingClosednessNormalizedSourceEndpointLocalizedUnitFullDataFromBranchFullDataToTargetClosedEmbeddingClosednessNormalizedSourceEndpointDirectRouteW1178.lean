import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteW1177
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute

/-!
W1178 replaces W1177's W1006 target/closedness/normalized-source/endpoint
surface by the existing W1016 branch-full-data route. W1016 already constructs
W1006, and W1178 feeds that provider into W1177.
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

/-- W1178 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1016 data. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1016
    branchFullData

/-- W1178 constructs the W1005 target/closed-embedding-closedness surface from W1007 through W1177. -/
def targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1007 through W1177. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W1003 endpoint-localized-unit surface from W1007 through W1177. -/
def endpointLocalizedUnitDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W982 localized-unit-choice surface from W1007 through W1177. -/
def localizedUnitChoiceDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W981 provider surface from W1007 through W1177. -/
noncomputable def unitStrictExactIsoDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W971 component-field surface from W1007 through W1177. -/
noncomputable def componentFieldsOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W1008 current-full-data surface from W1007 through W1177. -/
noncomputable def currentFullDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs the W1007 branch-full-data surface from W1007 through W1177. -/
noncomputable def branchFullDataProviderOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface through W1177. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1177. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1177. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1177. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W982 localized-unit-choice surface after routing through W1177. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W981 surface after routing through W1177. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W971 component fields after routing through W1177. -/
noncomputable def componentFieldsOfComponentFieldsOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W1008 current-full-data surface after routing through W1177. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the rebuilt W1007 branch-full-data surface after routing through W1177. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1177. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 exposes the twice-rebuilt W971 component fields after routing through W1177. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs W977 current full data from W1007 through W1177. -/
noncomputable def currentFullDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 constructs W987 branch full data from W1007 through W1177. -/
noncomputable def branchFullDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 recovers W715 target surjective-compact data from W1007 through W1177. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

/-- W1178 returns the constructed W987 branch full data from W1007 through W1177. -/
noncomputable def fullDataOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

theorem directBoundedLeftCalculusOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW1178
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1177
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178
      branchFullData)

def branchFullDataInputNamesW1178 : List String :=
  branchFullDataInputNamesW1016

theorem branchFullDataInputNamesW1178_count :
    branchFullDataInputNamesW1178.length = 1 :=
  branchFullDataInputNamesW1016_count

structure MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1178 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1178 :
    MetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1178
    where
  seed := "w1178-branch-full-data-to-w1177-target-closed-embedding-closedness-normalized-source-endpoint-route"
  declarations :=
    ["targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1178",
      "targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1178",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1178",
      "endpointLocalizedUnitDataProviderOfBranchFullDataW1178",
      "localizedUnitChoiceDataOfBranchFullDataW1178",
      "unitStrictExactIsoDataOfBranchFullDataW1178",
      "componentFieldsOfBranchFullDataW1178",
      "currentFullDataProviderOfBranchFullDataW1178",
      "branchFullDataProviderOfBranchFullDataW1178",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1178",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1178",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1178",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1178",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1178",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1178",
      "componentFieldsOfComponentFieldsOfBranchFullDataW1178",
      "currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1178",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataW1178",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1178",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1178",
      "currentFullDataOfBranchFullDataW1178",
      "branchFullDataOfBranchFullDataW1178",
      "targetSurjectiveCompactDataOfBranchFullDataW1178",
      "fullDataOfBranchFullDataW1178",
      "directBoundedLeftCalculusOfBranchFullDataW1178",
      "boundedDerivedInfinityCategoryOfBranchFullDataW1178",
      "branchFullDataInputNamesW1178_count"]
  providerRepackagingResult :=
    "proved: W1178 constructs the W1177 W1006 target/closedness/normalized-source/endpoint\
      provider surface from W1016 branch-full-data and feeds W1177"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1178 inherits W1177/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
      W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/\
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
    "proved: the W1178 W1016 branch-full-data provider surface feeds\
      W1177/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
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
  remainingInputs := branchFullDataInputNamesW1178
  productSuccessClaimed := false

theorem currentW1178BranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute_productSuccess :
    (let state :=
        currentMetrizableBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteStateW1178;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
