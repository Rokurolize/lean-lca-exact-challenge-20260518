import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1134
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1135 replaces W1134's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1135 feeds
that provider into W1134.
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

/-- W1135 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1135 constructs the W1007 branch-full-data surface from W1009 through W1134. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1134. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1134. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1134. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W1003 endpoint-localized-unit surface from W1009 through W1134. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W982 localized-unit-choice surface from W1009 through W1134. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W981 provider surface from W1009 through W1134. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs the W971 component-field surface from W1009 through W1134. -/
noncomputable def componentFieldsOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1008 current-full-data surface after routing through W1134. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1007 branch-full-data surface after routing through W1134. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1134. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1134. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1134. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1134. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W982 localized-unit-choice surface after routing through W1134. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W981 surface after routing through W1134. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W971 component fields after routing through W1134. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1008 current-full-data surface after routing through W1134. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the rebuilt W1007 branch-full-data surface after routing through W1134. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1134. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 exposes the twice-rebuilt W971 component fields after routing through W1134. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs W977 current full data from W1009 through W1134. -/
noncomputable def currentFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 constructs W987 branch full data from W1009 through W1134. -/
noncomputable def branchFullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 recovers W715 target surjective-compact data from W1009 through W1134. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

/-- W1135 returns the constructed W987 branch full data from W1009 through W1134. -/
noncomputable def fullDataOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1135
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1134
    (currentFullDataProviderOfComponentFieldsW1135 componentFields)

def componentFieldsInputNamesW1135 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1135_count :
    componentFieldsInputNamesW1135.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1135 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1135 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1135
    where
  seed := "w1135-component-fields-to-w1134-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1135",
      "branchFullDataProviderOfComponentFieldsW1135",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1135",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1135",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1135",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1135",
      "localizedUnitChoiceDataOfComponentFieldsW1135",
      "unitStrictExactIsoDataOfComponentFieldsW1135",
      "componentFieldsOfComponentFieldsW1135",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1135",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1135",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1135",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1135",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1135",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1135",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1135",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1135",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1135",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1135",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1135",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1135",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1135",
      "currentFullDataOfComponentFieldsW1135",
      "branchFullDataOfComponentFieldsW1135",
      "targetSurjectiveCompactDataOfComponentFieldsW1135",
      "fullDataOfComponentFieldsW1135",
      "directBoundedLeftCalculusOfComponentFieldsW1135",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1135",
      "componentFieldsInputNamesW1135_count"]
  providerRepackagingResult :=
    "proved: W1135 constructs the W1134 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1134"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1135 inherits W1134/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/\
      W1092/W1091/W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/\
      W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/\
      W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/\
      W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/\
      W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/\
      W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W1018 constructs W1008"
  exactAtResult :=
    "proved: the W1135 W1018 component-field provider surface feeds\
      W1134/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
      W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/\
      W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/\
      W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/\
      W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/\
      W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/\
      W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/\
      W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/\
      W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1135
  productSuccessClaimed := false

theorem currentW1135ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1135;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
