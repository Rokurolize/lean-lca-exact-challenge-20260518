import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1089
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1090 replaces W1089's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1090 feeds
that provider into W1089.
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

/-- W1090 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1090 constructs the W1007 branch-full-data surface from W1009 through W1089. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1089. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1089. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1089. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W1003 endpoint-localized-unit surface from W1009 through W1089. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W982 localized-unit-choice surface from W1009 through W1089. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W981 provider surface from W1009 through W1089. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs the W971 component-field surface from W1009 through W1089. -/
noncomputable def componentFieldsOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1008 current-full-data surface after routing through W1089. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1007 branch-full-data surface after routing through W1089. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1089. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1089. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1089. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1089. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W982 localized-unit-choice surface after routing through W1089. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W981 surface after routing through W1089. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W971 component fields after routing through W1089. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1008 current-full-data surface after routing through W1089. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the rebuilt W1007 branch-full-data surface after routing through W1089. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1089. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 exposes the twice-rebuilt W971 component fields after routing through W1089. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs W977 current full data from W1009 through W1089. -/
noncomputable def currentFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 constructs W987 branch full data from W1009 through W1089. -/
noncomputable def branchFullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 recovers W715 target surjective-compact data from W1009 through W1089. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

/-- W1090 returns the constructed W987 branch full data from W1009 through W1089. -/
noncomputable def fullDataOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1090
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1089
    (currentFullDataProviderOfComponentFieldsW1090 componentFields)

def componentFieldsInputNamesW1090 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1090_count :
    componentFieldsInputNamesW1090.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1090 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1090 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1090
    where
  seed := "w1090-component-fields-to-w1089-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1090",
      "branchFullDataProviderOfComponentFieldsW1090",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1090",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1090",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1090",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1090",
      "localizedUnitChoiceDataOfComponentFieldsW1090",
      "unitStrictExactIsoDataOfComponentFieldsW1090",
      "componentFieldsOfComponentFieldsW1090",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1090",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1090",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1090",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1090",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1090",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1090",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1090",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1090",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1090",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1090",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1090",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1090",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1090",
      "currentFullDataOfComponentFieldsW1090",
      "branchFullDataOfComponentFieldsW1090",
      "targetSurjectiveCompactDataOfComponentFieldsW1090",
      "fullDataOfComponentFieldsW1090",
      "directBoundedLeftCalculusOfComponentFieldsW1090",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1090",
      "componentFieldsInputNamesW1090_count"]
  providerRepackagingResult :=
    "proved: W1090 constructs the W1089 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1089"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1090 inherits W1089/W1088/W1087/W1086/W1085/W1084/W1083/\
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
    "proved: the W1090 W1018 component-field provider surface feeds\
      W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/\
      W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/\
      W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/\
      W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/\
      W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/\
      W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/\
      W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1090
  productSuccessClaimed := false

theorem currentW1090ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1090;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
