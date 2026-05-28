import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1125
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1126 replaces W1125's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1126 feeds
that provider into W1125.
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

/-- W1126 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1126 constructs the W1007 branch-full-data surface from W1009 through W1125. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1125. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1125. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1125. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W1003 endpoint-localized-unit surface from W1009 through W1125. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W982 localized-unit-choice surface from W1009 through W1125. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W981 provider surface from W1009 through W1125. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs the W971 component-field surface from W1009 through W1125. -/
noncomputable def componentFieldsOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1008 current-full-data surface after routing through W1125. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1007 branch-full-data surface after routing through W1125. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1125. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1125. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1125. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1125. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W982 localized-unit-choice surface after routing through W1125. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W981 surface after routing through W1125. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W971 component fields after routing through W1125. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1008 current-full-data surface after routing through W1125. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the rebuilt W1007 branch-full-data surface after routing through W1125. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1125. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 exposes the twice-rebuilt W971 component fields after routing through W1125. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs W977 current full data from W1009 through W1125. -/
noncomputable def currentFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 constructs W987 branch full data from W1009 through W1125. -/
noncomputable def branchFullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 recovers W715 target surjective-compact data from W1009 through W1125. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

/-- W1126 returns the constructed W987 branch full data from W1009 through W1125. -/
noncomputable def fullDataOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1126
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1125
    (currentFullDataProviderOfComponentFieldsW1126 componentFields)

def componentFieldsInputNamesW1126 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1126_count :
    componentFieldsInputNamesW1126.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1126 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1126 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1126
    where
  seed := "w1126-component-fields-to-w1125-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1126",
      "branchFullDataProviderOfComponentFieldsW1126",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1126",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1126",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1126",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1126",
      "localizedUnitChoiceDataOfComponentFieldsW1126",
      "unitStrictExactIsoDataOfComponentFieldsW1126",
      "componentFieldsOfComponentFieldsW1126",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1126",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1126",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1126",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1126",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1126",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1126",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1126",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1126",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1126",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1126",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1126",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1126",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1126",
      "currentFullDataOfComponentFieldsW1126",
      "branchFullDataOfComponentFieldsW1126",
      "targetSurjectiveCompactDataOfComponentFieldsW1126",
      "fullDataOfComponentFieldsW1126",
      "directBoundedLeftCalculusOfComponentFieldsW1126",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1126",
      "componentFieldsInputNamesW1126_count"]
  providerRepackagingResult :=
    "proved: W1126 constructs the W1125 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1125"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1126 inherits W1125/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/\
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
    "proved: the W1126 W1018 component-field provider surface feeds\
      W1125/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
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
  remainingInputs := componentFieldsInputNamesW1126
  productSuccessClaimed := false

theorem currentW1126ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1126;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
