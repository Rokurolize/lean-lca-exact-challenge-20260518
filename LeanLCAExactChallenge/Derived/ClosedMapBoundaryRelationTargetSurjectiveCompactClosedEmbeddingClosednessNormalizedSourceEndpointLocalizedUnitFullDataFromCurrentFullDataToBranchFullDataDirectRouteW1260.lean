import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1259
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1260 replaces W1259's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1260 feeds
that provider into W1259.
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

/-- W1260 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1260 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1259. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1259. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1259. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W1003 endpoint-localized-unit surface from W1008 through W1259. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W982 localized-unit-choice surface from W1008 through W1259. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W981 provider surface from W1008 through W1259. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W971 component-field surface from W1008 through W1259. -/
noncomputable def componentFieldsOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs the W1008 current-full-data surface from W1008 through W1259. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1007 branch-full-data surface after routing through W1259. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1259. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1259. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1259. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1259. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W982 localized-unit-choice surface after routing through W1259. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W981 surface after routing through W1259. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W971 component fields after routing through W1259. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1008 current-full-data surface after routing through W1259. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the rebuilt W1007 branch-full-data surface after routing through W1259. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1259. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 exposes the twice-rebuilt W971 component fields after routing through W1259. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs W977 current full data from W1008 through W1259. -/
noncomputable def currentFullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 constructs W987 branch full data from W1008 through W1259. -/
noncomputable def branchFullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 recovers W715 target surjective-compact data from W1008 through W1259. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

/-- W1260 returns the constructed W987 branch full data from W1008 through W1259. -/
noncomputable def fullDataOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1260
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1259
    (branchFullDataProviderOfCurrentFullDataW1260 currentFullData)

def currentFullDataInputNamesW1260 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1260_count :
    currentFullDataInputNamesW1260.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1260 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1260 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1260
    where
  seed := "w1260-current-full-data-to-w1259-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1260",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1260",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1260",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1260",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1260",
      "localizedUnitChoiceDataOfCurrentFullDataW1260",
      "unitStrictExactIsoDataOfCurrentFullDataW1260",
      "componentFieldsOfCurrentFullDataW1260",
      "currentFullDataProviderOfCurrentFullDataW1260",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1260",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1260",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1260",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1260",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1260",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1260",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1260",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1260",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1260",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1260",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1260",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1260",
      "currentFullDataOfCurrentFullDataW1260",
      "branchFullDataOfCurrentFullDataW1260",
      "targetSurjectiveCompactDataOfCurrentFullDataW1260",
      "fullDataOfCurrentFullDataW1260",
      "directBoundedLeftCalculusOfCurrentFullDataW1260",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1260",
      "currentFullDataInputNamesW1260_count"]
  providerRepackagingResult :=
    "proved: W1260 constructs the W1259 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1259"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1260 inherits W1259/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
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
    "proved: the W1260 W1017 current-full-data provider surface feeds\
      W1259/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
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
  remainingInputs := currentFullDataInputNamesW1260
  productSuccessClaimed := false

theorem currentW1260CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1260;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
