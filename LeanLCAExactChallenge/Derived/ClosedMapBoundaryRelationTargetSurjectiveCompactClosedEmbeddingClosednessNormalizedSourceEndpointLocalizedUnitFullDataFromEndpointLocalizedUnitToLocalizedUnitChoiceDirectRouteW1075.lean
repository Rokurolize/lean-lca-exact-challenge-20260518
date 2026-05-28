import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1074
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute

/-!
W1075 replaces W1074's W982 localized-unit-choice provider surface by the
existing W1012 endpoint-localized-unit surface. W1012 already constructs W982,
and W1075 feeds that provider into W1074.
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

/-- W1075 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData

/-- W1075 constructs the W981 provider surface from W1003 through W1074. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W971 component-field surface from W1003 through W1074. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W1008 current-full-data surface from W1003 through W1074. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W1007 branch-full-data surface from W1003 through W1074. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1074. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1074. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1074. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1074. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W982 localized-unit-choice surface after routing through W1074. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W981 surface after routing through W1074. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W971 component fields after routing through W1074. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1008 current-full-data surface after routing through W1074. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1007 branch-full-data surface after routing through W1074. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1074. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1074. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1074. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1074 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W982 localized-unit-choice surface after the nested W1074 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W981 surface after the nested W1074 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W971 component fields after the nested W1074 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1008 current-full-data surface after the nested W1074 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the rebuilt W1007 branch-full-data surface after the nested W1074 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1074. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 exposes the twice-rebuilt W971 component fields after routing through W1074. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs W977 current full data from W1003 through W1074. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 constructs W987 branch full data from W1003 through W1074. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 recovers W715 target surjective-compact data from W1003 through W1074. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

/-- W1075 returns the constructed W987 branch full data from W1003 through W1074. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1075
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1074
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1075 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1075 : List String :=
  endpointLocalizedUnitInputNamesW1012

theorem endpointLocalizedUnitInputNamesW1075_count :
    endpointLocalizedUnitInputNamesW1075.length = 5 :=
  endpointLocalizedUnitInputNamesW1012_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1075 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1075 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1075
    where
  seed := "w1075-endpoint-localized-unit-to-w1074-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1075",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1075",
      "componentFieldsOfEndpointLocalizedUnitW1075",
      "currentFullDataProviderOfEndpointLocalizedUnitW1075",
      "branchFullDataProviderOfEndpointLocalizedUnitW1075",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1075",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1075",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1075",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1075",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1075",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1075",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1075",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1075",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1075",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1075",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1075",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1075",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1075",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1075",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1075",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1075",
      "currentFullDataOfEndpointLocalizedUnitW1075",
      "branchFullDataOfEndpointLocalizedUnitW1075",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1075",
      "fullDataOfEndpointLocalizedUnitW1075",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1075",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1075",
      "endpointLocalizedUnitInputNamesW1075_count"]
  providerRepackagingResult :=
    "proved: W1075 constructs the W1074 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data through W1012 and feeds W1074"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1075 inherits W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1012 constructs W982"
  exactAtResult :=
    "proved: the W1075 W1003 endpoint-localized-unit provider surface feeds\
      W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/\
      W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/\
      W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1075
  productSuccessClaimed := false

theorem currentW1075EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1075;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
