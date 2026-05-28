import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1180
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1181 replaces W1180's W1018 component-field input surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1181 feeds those fields into W1180.
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

/-- W1181 constructs the W1180 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1181 constructs the W1008 current-full-data surface from W981 data through W1180. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W1007 branch-full-data surface from W981 data through W1180. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1180. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1180. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1180. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W1003 endpoint-localized-unit surface from W981 data through W1180. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs the W982 localized-unit-choice surface from W981 data through W1180. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W981 surface after routing through W1180. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W971 component fields after routing through W1180. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1008 current-full-data surface after routing through W1180. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1007 branch-full-data surface after routing through W1180. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1180. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1180. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1180. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1180. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W982 localized-unit-choice surface after routing through W1180. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W981 surface after the nested W1180 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W971 component fields after the nested W1180 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1008 current-full-data surface after the nested W1180 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the rebuilt W1007 branch-full-data surface after the nested W1180 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1180. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 exposes the twice-rebuilt W971 component fields after routing through W1180. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs W977 current full data from W981 data through W1180. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 constructs W987 branch full data from W981 data through W1180. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 recovers W715 target surjective-compact data from W981 data through W1180. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

/-- W1181 returns the constructed W987 branch full data from W981 data through W1180. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1181
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1180
    (componentFieldsOfUnitStrictExactIsoDataW1181 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1181 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1181_count :
    unitStrictExactIsoDataInputNamesW1181.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1181 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1181 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1181
    where
  seed := "w1181-unit-strict-exact-iso-data-to-w1180-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1181",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1181",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1181",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1181",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1181",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1181",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1181",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1181",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1181",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1181",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1181",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1181",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1181",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1181",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1181",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1181",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1181",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1181",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1181",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1181",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1181",
      "currentFullDataOfUnitStrictExactIsoDataW1181",
      "branchFullDataOfUnitStrictExactIsoDataW1181",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1181",
      "fullDataOfUnitStrictExactIsoDataW1181",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1181",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1181",
      "unitStrictExactIsoDataInputNamesW1181_count"]
  providerRepackagingResult :=
    "proved: W1181 constructs the W1180 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1180"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1181 inherits W1180/W1116/W1115/W1114/W1113/W1112/\
      W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/\
      W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/\
      W1091/W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/\
      W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/\
      W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/\
      W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/\
      W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/\
      W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1181 W981 endpoint/unit-strict-exact provider surface feeds\
      W1180/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/\
      W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/\
      W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1181
  productSuccessClaimed := false

theorem currentW1181UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1181;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
