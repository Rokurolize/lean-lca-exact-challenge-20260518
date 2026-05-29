import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1215
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1216 replaces W1215's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1216 feeds
that provider into W1215.
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

/-- W1216 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1216 constructs the W1007 branch-full-data surface from W1009 through W1215. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1215. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1215. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1215. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W1003 endpoint-localized-unit surface from W1009 through W1215. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W982 localized-unit-choice surface from W1009 through W1215. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W981 provider surface from W1009 through W1215. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs the W971 component-field surface from W1009 through W1215. -/
noncomputable def componentFieldsOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1008 current-full-data surface after routing through W1215. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1007 branch-full-data surface after routing through W1215. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1215. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1215. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1215. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1215. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W982 localized-unit-choice surface after routing through W1215. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W981 surface after routing through W1215. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W971 component fields after routing through W1215. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1008 current-full-data surface after routing through W1215. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the rebuilt W1007 branch-full-data surface after routing through W1215. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1215. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 exposes the twice-rebuilt W971 component fields after routing through W1215. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs W977 current full data from W1009 through W1215. -/
noncomputable def currentFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 constructs W987 branch full data from W1009 through W1215. -/
noncomputable def branchFullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 recovers W715 target surjective-compact data from W1009 through W1215. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

/-- W1216 returns the constructed W987 branch full data from W1009 through W1215. -/
noncomputable def fullDataOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1216
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1215
    (currentFullDataProviderOfComponentFieldsW1216 componentFields)

def componentFieldsInputNamesW1216 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1216_count :
    componentFieldsInputNamesW1216.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1216 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1216 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1216
    where
  seed := "w1216-component-fields-to-w1215-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1216",
      "branchFullDataProviderOfComponentFieldsW1216",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1216",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1216",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1216",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1216",
      "localizedUnitChoiceDataOfComponentFieldsW1216",
      "unitStrictExactIsoDataOfComponentFieldsW1216",
      "componentFieldsOfComponentFieldsW1216",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1216",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1216",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1216",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1216",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1216",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1216",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1216",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1216",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1216",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1216",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1216",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1216",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1216",
      "currentFullDataOfComponentFieldsW1216",
      "branchFullDataOfComponentFieldsW1216",
      "targetSurjectiveCompactDataOfComponentFieldsW1216",
      "fullDataOfComponentFieldsW1216",
      "directBoundedLeftCalculusOfComponentFieldsW1216",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1216",
      "componentFieldsInputNamesW1216_count"]
  providerRepackagingResult :=
    "proved: W1216 constructs the W1215 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1215"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1216 inherits W1215/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/\
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
    "proved: the W1216 W1018 component-field provider surface feeds\
      W1215/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
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
  remainingInputs := componentFieldsInputNamesW1216
  productSuccessClaimed := false

theorem currentW1216ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1216;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
