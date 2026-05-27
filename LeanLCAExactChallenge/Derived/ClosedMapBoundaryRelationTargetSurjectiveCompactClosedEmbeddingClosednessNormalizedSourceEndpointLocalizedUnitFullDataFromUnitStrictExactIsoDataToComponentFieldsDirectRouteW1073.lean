import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1072
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1073 replaces W1072's W1018 component-field input surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1073 feeds those fields into W1072.
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

/-- W1073 constructs the W1072 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1073 constructs the W1008 current-full-data surface from W981 data through W1072. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W1007 branch-full-data surface from W981 data through W1072. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1072. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1072. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1072. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W1003 endpoint-localized-unit surface from W981 data through W1072. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs the W982 localized-unit-choice surface from W981 data through W1072. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W981 surface after routing through W1072. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W971 component fields after routing through W1072. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1008 current-full-data surface after routing through W1072. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1007 branch-full-data surface after routing through W1072. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1072. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1072. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1072. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1072. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W982 localized-unit-choice surface after routing through W1072. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W981 surface after the nested W1072 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W971 component fields after the nested W1072 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1008 current-full-data surface after the nested W1072 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the rebuilt W1007 branch-full-data surface after the nested W1072 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1072. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 exposes the twice-rebuilt W971 component fields after routing through W1072. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs W977 current full data from W981 data through W1072. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 constructs W987 branch full data from W981 data through W1072. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 recovers W715 target surjective-compact data from W981 data through W1072. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

/-- W1073 returns the constructed W987 branch full data from W981 data through W1072. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1073
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1072
    (componentFieldsOfUnitStrictExactIsoDataW1073 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1073 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1073_count :
    unitStrictExactIsoDataInputNamesW1073.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1073 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1073 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1073
    where
  seed := "w1073-unit-strict-exact-iso-data-to-w1072-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1073",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1073",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1073",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1073",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1073",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1073",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1073",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1073",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1073",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1073",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1073",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1073",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1073",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1073",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1073",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1073",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1073",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1073",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1073",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1073",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1073",
      "currentFullDataOfUnitStrictExactIsoDataW1073",
      "branchFullDataOfUnitStrictExactIsoDataW1073",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1073",
      "fullDataOfUnitStrictExactIsoDataW1073",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1073",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1073",
      "unitStrictExactIsoDataInputNamesW1073_count"]
  providerRepackagingResult :=
    "proved: W1073 constructs the W1072 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1072"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1073 inherits W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1073 W981 endpoint/unit-strict-exact provider surface feeds\
      W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/\
      W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/\
      W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/\
      W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1073
  productSuccessClaimed := false

theorem currentW1073UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1073;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
