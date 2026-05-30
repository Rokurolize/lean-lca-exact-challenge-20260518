import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1232
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1233 replaces W1232's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1233 feeds
that provider into W1232.
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

/-- W1233 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1233 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1232. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1232. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1232. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W1003 endpoint-localized-unit surface from W1008 through W1232. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W982 localized-unit-choice surface from W1008 through W1232. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W981 provider surface from W1008 through W1232. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W971 component-field surface from W1008 through W1232. -/
noncomputable def componentFieldsOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs the W1008 current-full-data surface from W1008 through W1232. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1007 branch-full-data surface after routing through W1232. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1232. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1232. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1232. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1232. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W982 localized-unit-choice surface after routing through W1232. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W981 surface after routing through W1232. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W971 component fields after routing through W1232. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1008 current-full-data surface after routing through W1232. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the rebuilt W1007 branch-full-data surface after routing through W1232. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1232. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 exposes the twice-rebuilt W971 component fields after routing through W1232. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs W977 current full data from W1008 through W1232. -/
noncomputable def currentFullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 constructs W987 branch full data from W1008 through W1232. -/
noncomputable def branchFullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 recovers W715 target surjective-compact data from W1008 through W1232. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

/-- W1233 returns the constructed W987 branch full data from W1008 through W1232. -/
noncomputable def fullDataOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1233
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1232
    (branchFullDataProviderOfCurrentFullDataW1233 currentFullData)

def currentFullDataInputNamesW1233 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1233_count :
    currentFullDataInputNamesW1233.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1233 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1233 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1233
    where
  seed := "w1233-current-full-data-to-w1232-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1233",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1233",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1233",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1233",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1233",
      "localizedUnitChoiceDataOfCurrentFullDataW1233",
      "unitStrictExactIsoDataOfCurrentFullDataW1233",
      "componentFieldsOfCurrentFullDataW1233",
      "currentFullDataProviderOfCurrentFullDataW1233",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1233",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1233",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1233",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1233",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1233",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1233",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1233",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1233",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1233",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1233",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1233",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1233",
      "currentFullDataOfCurrentFullDataW1233",
      "branchFullDataOfCurrentFullDataW1233",
      "targetSurjectiveCompactDataOfCurrentFullDataW1233",
      "fullDataOfCurrentFullDataW1233",
      "directBoundedLeftCalculusOfCurrentFullDataW1233",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1233",
      "currentFullDataInputNamesW1233_count"]
  providerRepackagingResult :=
    "proved: W1233 constructs the W1232 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1232"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1233 inherits W1232/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
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
    "proved: the W1233 W1017 current-full-data provider surface feeds\
      W1232/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
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
  remainingInputs := currentFullDataInputNamesW1233
  productSuccessClaimed := false

theorem currentW1233CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1233;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
