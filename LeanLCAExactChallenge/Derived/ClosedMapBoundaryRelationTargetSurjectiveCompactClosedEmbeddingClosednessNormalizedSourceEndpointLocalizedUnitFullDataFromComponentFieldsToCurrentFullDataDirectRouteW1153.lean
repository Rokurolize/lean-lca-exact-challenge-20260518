import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1152
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1153 replaces W1152's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1153 feeds
that provider into W1152.
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

/-- W1153 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1153 constructs the W1007 branch-full-data surface from W1009 through W1152. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1152. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1152. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1152. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W1003 endpoint-localized-unit surface from W1009 through W1152. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W982 localized-unit-choice surface from W1009 through W1152. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W981 provider surface from W1009 through W1152. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs the W971 component-field surface from W1009 through W1152. -/
noncomputable def componentFieldsOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1008 current-full-data surface after routing through W1152. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1007 branch-full-data surface after routing through W1152. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1152. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1152. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1152. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1152. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W982 localized-unit-choice surface after routing through W1152. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W981 surface after routing through W1152. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W971 component fields after routing through W1152. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1008 current-full-data surface after routing through W1152. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the rebuilt W1007 branch-full-data surface after routing through W1152. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1152. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 exposes the twice-rebuilt W971 component fields after routing through W1152. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs W977 current full data from W1009 through W1152. -/
noncomputable def currentFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 constructs W987 branch full data from W1009 through W1152. -/
noncomputable def branchFullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 recovers W715 target surjective-compact data from W1009 through W1152. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

/-- W1153 returns the constructed W987 branch full data from W1009 through W1152. -/
noncomputable def fullDataOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1153
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1152
    (currentFullDataProviderOfComponentFieldsW1153 componentFields)

def componentFieldsInputNamesW1153 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1153_count :
    componentFieldsInputNamesW1153.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1153 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1153 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1153
    where
  seed := "w1153-component-fields-to-w1152-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1153",
      "branchFullDataProviderOfComponentFieldsW1153",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1153",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1153",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1153",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1153",
      "localizedUnitChoiceDataOfComponentFieldsW1153",
      "unitStrictExactIsoDataOfComponentFieldsW1153",
      "componentFieldsOfComponentFieldsW1153",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1153",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1153",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1153",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1153",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1153",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1153",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1153",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1153",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1153",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1153",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1153",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1153",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1153",
      "currentFullDataOfComponentFieldsW1153",
      "branchFullDataOfComponentFieldsW1153",
      "targetSurjectiveCompactDataOfComponentFieldsW1153",
      "fullDataOfComponentFieldsW1153",
      "directBoundedLeftCalculusOfComponentFieldsW1153",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1153",
      "componentFieldsInputNamesW1153_count"]
  providerRepackagingResult :=
    "proved: W1153 constructs the W1152 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1152"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1153 inherits W1152/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/\
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
    "proved: the W1153 W1018 component-field provider surface feeds\
      W1152/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
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
  remainingInputs := componentFieldsInputNamesW1153
  productSuccessClaimed := false

theorem currentW1153ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1153;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
