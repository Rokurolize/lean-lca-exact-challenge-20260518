import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1097
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1098 replaces W1097's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1098 feeds
that provider into W1097.
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

/-- W1098 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1098 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1097. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1097. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1097. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W1003 endpoint-localized-unit surface from W1008 through W1097. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W982 localized-unit-choice surface from W1008 through W1097. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W981 provider surface from W1008 through W1097. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W971 component-field surface from W1008 through W1097. -/
noncomputable def componentFieldsOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs the W1008 current-full-data surface from W1008 through W1097. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1007 branch-full-data surface after routing through W1097. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1097. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1097. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1097. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1097. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W982 localized-unit-choice surface after routing through W1097. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W981 surface after routing through W1097. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W971 component fields after routing through W1097. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1008 current-full-data surface after routing through W1097. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the rebuilt W1007 branch-full-data surface after routing through W1097. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1097. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 exposes the twice-rebuilt W971 component fields after routing through W1097. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs W977 current full data from W1008 through W1097. -/
noncomputable def currentFullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 constructs W987 branch full data from W1008 through W1097. -/
noncomputable def branchFullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 recovers W715 target surjective-compact data from W1008 through W1097. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

/-- W1098 returns the constructed W987 branch full data from W1008 through W1097. -/
noncomputable def fullDataOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1098
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1097
    (branchFullDataProviderOfCurrentFullDataW1098 currentFullData)

def currentFullDataInputNamesW1098 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1098_count :
    currentFullDataInputNamesW1098.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1098 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1098 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1098
    where
  seed := "w1098-current-full-data-to-w1097-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1098",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1098",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1098",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1098",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1098",
      "localizedUnitChoiceDataOfCurrentFullDataW1098",
      "unitStrictExactIsoDataOfCurrentFullDataW1098",
      "componentFieldsOfCurrentFullDataW1098",
      "currentFullDataProviderOfCurrentFullDataW1098",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1098",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1098",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1098",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1098",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1098",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1098",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1098",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1098",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1098",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1098",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1098",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1098",
      "currentFullDataOfCurrentFullDataW1098",
      "branchFullDataOfCurrentFullDataW1098",
      "targetSurjectiveCompactDataOfCurrentFullDataW1098",
      "fullDataOfCurrentFullDataW1098",
      "directBoundedLeftCalculusOfCurrentFullDataW1098",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1098",
      "currentFullDataInputNamesW1098_count"]
  providerRepackagingResult :=
    "proved: W1098 constructs the W1097 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1097"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1098 inherits W1097/W1096/W1095/W1094/W1093/W1092/\
      W1091/W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/\
      W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/\
      W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/\
      W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/\
      W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/\
      W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1098 W1017 current-full-data provider surface feeds\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/\
      W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1098
  productSuccessClaimed := false

theorem currentW1098CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1098;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
