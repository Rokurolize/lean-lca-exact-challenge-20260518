import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1119
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute

/-!
W1120 replaces W1119's W982 localized-unit-choice provider surface by the
existing W1012 endpoint-localized-unit surface. W1012 already constructs W982,
and W1120 feeds that provider into W1119.
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

/-- W1120 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData

/-- W1120 constructs the W981 provider surface from W1003 through W1119. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W971 component-field surface from W1003 through W1119. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W1008 current-full-data surface from W1003 through W1119. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W1007 branch-full-data surface from W1003 through W1119. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1119. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1119. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1119. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1119. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W982 localized-unit-choice surface after routing through W1119. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W981 surface after routing through W1119. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W971 component fields after routing through W1119. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1008 current-full-data surface after routing through W1119. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1007 branch-full-data surface after routing through W1119. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1119. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1119. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1119. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1119 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W982 localized-unit-choice surface after the nested W1119 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W981 surface after the nested W1119 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W971 component fields after the nested W1119 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1008 current-full-data surface after the nested W1119 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the rebuilt W1007 branch-full-data surface after the nested W1119 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1119. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 exposes the twice-rebuilt W971 component fields after routing through W1119. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs W977 current full data from W1003 through W1119. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 constructs W987 branch full data from W1003 through W1119. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 recovers W715 target surjective-compact data from W1003 through W1119. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

/-- W1120 returns the constructed W987 branch full data from W1003 through W1119. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1120
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1119
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1120 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1120 : List String :=
  endpointLocalizedUnitInputNamesW1012

theorem endpointLocalizedUnitInputNamesW1120_count :
    endpointLocalizedUnitInputNamesW1120.length = 5 :=
  endpointLocalizedUnitInputNamesW1012_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1120 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1120 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1120
    where
  seed := "w1120-endpoint-localized-unit-to-w1119-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1120",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1120",
      "componentFieldsOfEndpointLocalizedUnitW1120",
      "currentFullDataProviderOfEndpointLocalizedUnitW1120",
      "branchFullDataProviderOfEndpointLocalizedUnitW1120",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1120",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1120",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1120",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1120",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1120",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1120",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1120",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1120",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1120",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1120",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1120",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1120",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1120",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1120",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1120",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1120",
      "currentFullDataOfEndpointLocalizedUnitW1120",
      "branchFullDataOfEndpointLocalizedUnitW1120",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1120",
      "fullDataOfEndpointLocalizedUnitW1120",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1120",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1120",
      "endpointLocalizedUnitInputNamesW1120_count"]
  providerRepackagingResult :=
    "proved: W1120 constructs the W1119 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data through W1012 and feeds W1119"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1120 inherits W1119/W1118/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/\
      W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/W1085/\
      W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/\
      W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/\
      W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/\
      W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1012 constructs W982"
  exactAtResult :=
    "proved: the W1120 W1003 endpoint-localized-unit provider surface feeds\
      W1119/W1118/W1117/W1116/W1115/W1114/W1113/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/W1095/W1094/W1093/W1092/\
      W1091/W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/W1082/\
      W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/W1073/W1072/\
      W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/W1062/\
      W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/\
      W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/W1042/\
      W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1120
  productSuccessClaimed := false

theorem currentW1120EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1120;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
