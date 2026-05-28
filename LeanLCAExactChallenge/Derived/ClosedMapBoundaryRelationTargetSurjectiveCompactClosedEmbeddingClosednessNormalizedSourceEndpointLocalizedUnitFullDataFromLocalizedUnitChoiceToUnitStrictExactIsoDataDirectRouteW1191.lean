import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRouteW1190
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceDirectRoute

/-!
W1191 replaces W1190's W981 endpoint/unit-strict-exact provider surface by the
existing W1011 localized-unit-choice surface. W1011 already constructs W981
from W982, and W1191 feeds that provider into W1190.
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

/-- W1191 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1011 localizedUnitChoiceData

/-- W1191 constructs the W971 component-field surface from W982 through W1190. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1008 current-full-data surface from W982 through W1190. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1007 branch-full-data surface from W982 through W1190. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1006 target/closedness/normalized-source/endpoint surface from W982 through W1190. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1005 target/closed-embedding-closedness surface from W982 through W1190. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1004 normalized-source/endpoint-localized-unit surface from W982 through W1190. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs the W1003 endpoint-localized-unit surface from W982 through W1190. -/
noncomputable def endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W982 localized-unit-choice surface after routing through W1190. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W981 surface after routing through W1190. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W971 component fields after routing through W1190. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1008 current-full-data surface after routing through W1190. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1007 branch-full-data surface after routing through W1190. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1190. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1190. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1190. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1190. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W982 localized-unit-choice surface after the nested W1190 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W981 surface after the nested W1190 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W971 component fields after the nested W1190 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1008 current-full-data surface after the nested W1190 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the rebuilt W1007 branch-full-data surface after the nested W1190 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1190. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 exposes the twice-rebuilt W971 component fields after routing through W1190. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs W977 current full data from W982 through W1190. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 constructs W987 branch full data from W982 through W1190. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 recovers W715 target surjective-compact data from W982 through W1190. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

/-- W1191 returns the constructed W987 branch full data from W982 through W1190. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1191
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1190
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1191 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1191 : List String :=
  localizedUnitChoiceInputNamesW1011

theorem localizedUnitChoiceInputNamesW1191_count :
    localizedUnitChoiceInputNamesW1191.length = 6 :=
  localizedUnitChoiceInputNamesW1011_count

structure MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1191 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1191 :
    MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1191
    where
  seed := "w1191-localized-unit-choice-to-w1190-unit-strict-exact-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1191",
      "componentFieldsOfLocalizedUnitChoiceW1191",
      "currentFullDataProviderOfLocalizedUnitChoiceW1191",
      "branchFullDataProviderOfLocalizedUnitChoiceW1191",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1191",
      "targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1191",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1191",
      "endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1191",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1191",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1191",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191",
      "currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1191",
      "branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1191",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1191",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1191",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1191",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1191",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1191",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1191",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1191",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1191",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1191",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1191",
      "currentFullDataOfLocalizedUnitChoiceW1191",
      "branchFullDataOfLocalizedUnitChoiceW1191",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1191",
      "fullDataOfLocalizedUnitChoiceW1191",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1191",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1191",
      "localizedUnitChoiceInputNamesW1191_count"]
  providerRepackagingResult :=
    "proved: W1191 constructs the W1190 W981 endpoint/unit-strict-exact\
      provider surface from W982 localized-unit-choice data through W1011\
      and feeds W1190"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1191 inherits W1190/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/\
      W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/W1085/\
      W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/\
      W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/\
      W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/\
      W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998 target surjective-compact recovery\
      after W1011 constructs W981"
  exactAtResult :=
    "proved: the W1191 W982 localized-unit-choice provider surface feeds\
      W1190/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/\
      W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/\
      W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/\
      W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/\
      W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/\
      W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/\
      W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/\
      W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/\
      W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/\
      W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1191
  productSuccessClaimed := false

theorem currentW1191LocalizedUnitChoiceToUnitStrictExactIsoDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1191;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
