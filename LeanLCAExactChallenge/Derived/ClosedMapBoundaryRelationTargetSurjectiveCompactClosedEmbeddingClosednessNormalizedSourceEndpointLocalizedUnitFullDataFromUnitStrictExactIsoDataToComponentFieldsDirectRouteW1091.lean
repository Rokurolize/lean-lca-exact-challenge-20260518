import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1090
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1091 replaces W1090's W1018 component-field input surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1091 feeds those fields into W1090.
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

/-- W1091 constructs the W1090 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1091 constructs the W1008 current-full-data surface from W981 data through W1090. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W1007 branch-full-data surface from W981 data through W1090. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1090. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1090. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1090. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W1003 endpoint-localized-unit surface from W981 data through W1090. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs the W982 localized-unit-choice surface from W981 data through W1090. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W981 surface after routing through W1090. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W971 component fields after routing through W1090. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1008 current-full-data surface after routing through W1090. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1007 branch-full-data surface after routing through W1090. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1090. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1090. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1090. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1090. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W982 localized-unit-choice surface after routing through W1090. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W981 surface after the nested W1090 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W971 component fields after the nested W1090 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1008 current-full-data surface after the nested W1090 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the rebuilt W1007 branch-full-data surface after the nested W1090 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1090. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 exposes the twice-rebuilt W971 component fields after routing through W1090. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs W977 current full data from W981 data through W1090. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 constructs W987 branch full data from W981 data through W1090. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 recovers W715 target surjective-compact data from W981 data through W1090. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

/-- W1091 returns the constructed W987 branch full data from W981 data through W1090. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1091
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1090
    (componentFieldsOfUnitStrictExactIsoDataW1091 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1091 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1091_count :
    unitStrictExactIsoDataInputNamesW1091.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1091 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1091 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1091
    where
  seed := "w1091-unit-strict-exact-iso-data-to-w1090-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1091",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1091",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1091",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1091",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1091",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1091",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1091",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1091",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1091",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1091",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1091",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1091",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1091",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1091",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1091",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1091",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1091",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1091",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1091",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1091",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1091",
      "currentFullDataOfUnitStrictExactIsoDataW1091",
      "branchFullDataOfUnitStrictExactIsoDataW1091",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1091",
      "fullDataOfUnitStrictExactIsoDataW1091",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1091",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1091",
      "unitStrictExactIsoDataInputNamesW1091_count"]
  providerRepackagingResult :=
    "proved: W1091 constructs the W1090 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1090"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1091 inherits W1090/W1089/W1088/W1087/W1086/W1085/W1084/\
      W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/\
      W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/\
      W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/\
      W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/\
      W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1091 W981 endpoint/unit-strict-exact provider surface feeds\
      W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/\
      W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/\
      W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/\
      W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/\
      W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/\
      W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/\
      W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1091
  productSuccessClaimed := false

theorem currentW1091UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1091;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
