import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1092
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute

/-!
W1093 replaces W1092's W982 localized-unit-choice provider surface by the
existing W1012 endpoint-localized-unit surface. W1012 already constructs W982,
and W1093 feeds that provider into W1092.
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

/-- W1093 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData

/-- W1093 constructs the W981 provider surface from W1003 through W1092. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W971 component-field surface from W1003 through W1092. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W1008 current-full-data surface from W1003 through W1092. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W1007 branch-full-data surface from W1003 through W1092. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1092. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1092. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1092. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1092. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W982 localized-unit-choice surface after routing through W1092. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W981 surface after routing through W1092. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W971 component fields after routing through W1092. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1008 current-full-data surface after routing through W1092. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1007 branch-full-data surface after routing through W1092. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1092. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1092. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1092. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1092 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W982 localized-unit-choice surface after the nested W1092 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W981 surface after the nested W1092 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W971 component fields after the nested W1092 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1008 current-full-data surface after the nested W1092 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the rebuilt W1007 branch-full-data surface after the nested W1092 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1092. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 exposes the twice-rebuilt W971 component fields after routing through W1092. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs W977 current full data from W1003 through W1092. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 constructs W987 branch full data from W1003 through W1092. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 recovers W715 target surjective-compact data from W1003 through W1092. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

/-- W1093 returns the constructed W987 branch full data from W1003 through W1092. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1093
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1092
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1093 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1093 : List String :=
  endpointLocalizedUnitInputNamesW1012

theorem endpointLocalizedUnitInputNamesW1093_count :
    endpointLocalizedUnitInputNamesW1093.length = 5 :=
  endpointLocalizedUnitInputNamesW1012_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1093 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1093 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1093
    where
  seed := "w1093-endpoint-localized-unit-to-w1092-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1093",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1093",
      "componentFieldsOfEndpointLocalizedUnitW1093",
      "currentFullDataProviderOfEndpointLocalizedUnitW1093",
      "branchFullDataProviderOfEndpointLocalizedUnitW1093",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1093",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1093",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1093",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1093",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1093",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1093",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1093",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1093",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1093",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1093",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1093",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1093",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1093",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1093",
      "currentFullDataOfEndpointLocalizedUnitW1093",
      "branchFullDataOfEndpointLocalizedUnitW1093",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1093",
      "fullDataOfEndpointLocalizedUnitW1093",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1093",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1093",
      "endpointLocalizedUnitInputNamesW1093_count"]
  providerRepackagingResult :=
    "proved: W1093 constructs the W1092 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data through W1012 and feeds W1092"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1093 inherits W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/\
      W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/\
      W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/\
      W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1012 constructs W982"
  exactAtResult :=
    "proved: the W1093 W1003 endpoint-localized-unit provider surface feeds\
      W1092/W1091/W1090/W1089/W1088/W1087/W1086/W1085/W1084/W1083/\
      W1082/W1081/W1080/W1079/W1078/W1077/W1076/W1075/W1074/\
      W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/\
      W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/\
      W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/\
      W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1093
  productSuccessClaimed := false

theorem currentW1093EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1093;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
