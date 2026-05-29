import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1214
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1215 replaces W1214's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1215 feeds
that provider into W1214.
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

/-- W1215 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1215 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1214. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1214. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1214. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W1003 endpoint-localized-unit surface from W1008 through W1214. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W982 localized-unit-choice surface from W1008 through W1214. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W981 provider surface from W1008 through W1214. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W971 component-field surface from W1008 through W1214. -/
noncomputable def componentFieldsOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs the W1008 current-full-data surface from W1008 through W1214. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1007 branch-full-data surface after routing through W1214. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1214. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1214. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1214. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1214. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W982 localized-unit-choice surface after routing through W1214. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W981 surface after routing through W1214. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W971 component fields after routing through W1214. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1008 current-full-data surface after routing through W1214. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the rebuilt W1007 branch-full-data surface after routing through W1214. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1214. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 exposes the twice-rebuilt W971 component fields after routing through W1214. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs W977 current full data from W1008 through W1214. -/
noncomputable def currentFullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 constructs W987 branch full data from W1008 through W1214. -/
noncomputable def branchFullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 recovers W715 target surjective-compact data from W1008 through W1214. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

/-- W1215 returns the constructed W987 branch full data from W1008 through W1214. -/
noncomputable def fullDataOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1215
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1214
    (branchFullDataProviderOfCurrentFullDataW1215 currentFullData)

def currentFullDataInputNamesW1215 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1215_count :
    currentFullDataInputNamesW1215.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1215 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1215 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1215
    where
  seed := "w1215-current-full-data-to-w1214-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1215",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1215",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1215",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1215",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1215",
      "localizedUnitChoiceDataOfCurrentFullDataW1215",
      "unitStrictExactIsoDataOfCurrentFullDataW1215",
      "componentFieldsOfCurrentFullDataW1215",
      "currentFullDataProviderOfCurrentFullDataW1215",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1215",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1215",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1215",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1215",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1215",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1215",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1215",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1215",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1215",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1215",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1215",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1215",
      "currentFullDataOfCurrentFullDataW1215",
      "branchFullDataOfCurrentFullDataW1215",
      "targetSurjectiveCompactDataOfCurrentFullDataW1215",
      "fullDataOfCurrentFullDataW1215",
      "directBoundedLeftCalculusOfCurrentFullDataW1215",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1215",
      "currentFullDataInputNamesW1215_count"]
  providerRepackagingResult :=
    "proved: W1215 constructs the W1214 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1214"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1215 inherits W1214/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
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
      surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1215 W1017 current-full-data provider surface feeds\
      W1214/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/\
      W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/\
      W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/\
      W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/\
      W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/\
      W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1215
  productSuccessClaimed := false

theorem currentW1215CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1215;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
