import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1070
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1071 replaces W1070's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1071 feeds
that provider into W1070.
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

/-- W1071 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1071 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1070. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1070. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1070. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W1003 endpoint-localized-unit surface from W1008 through W1070. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W982 localized-unit-choice surface from W1008 through W1070. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W981 provider surface from W1008 through W1070. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W971 component-field surface from W1008 through W1070. -/
noncomputable def componentFieldsOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs the W1008 current-full-data surface from W1008 through W1070. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1007 branch-full-data surface after routing through W1070. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1070. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1070. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1070. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1070. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W982 localized-unit-choice surface after routing through W1070. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W981 surface after routing through W1070. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W971 component fields after routing through W1070. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1008 current-full-data surface after routing through W1070. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the rebuilt W1007 branch-full-data surface after routing through W1070. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1070. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 exposes the twice-rebuilt W971 component fields after routing through W1070. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs W977 current full data from W1008 through W1070. -/
noncomputable def currentFullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 constructs W987 branch full data from W1008 through W1070. -/
noncomputable def branchFullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 recovers W715 target surjective-compact data from W1008 through W1070. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

/-- W1071 returns the constructed W987 branch full data from W1008 through W1070. -/
noncomputable def fullDataOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1071
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1070
    (branchFullDataProviderOfCurrentFullDataW1071 currentFullData)

def currentFullDataInputNamesW1071 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1071_count :
    currentFullDataInputNamesW1071.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1071 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1071 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1071
    where
  seed := "w1071-current-full-data-to-w1070-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1071",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1071",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1071",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1071",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1071",
      "localizedUnitChoiceDataOfCurrentFullDataW1071",
      "unitStrictExactIsoDataOfCurrentFullDataW1071",
      "componentFieldsOfCurrentFullDataW1071",
      "currentFullDataProviderOfCurrentFullDataW1071",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1071",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1071",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1071",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1071",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1071",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1071",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1071",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1071",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1071",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1071",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1071",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1071",
      "currentFullDataOfCurrentFullDataW1071",
      "branchFullDataOfCurrentFullDataW1071",
      "targetSurjectiveCompactDataOfCurrentFullDataW1071",
      "fullDataOfCurrentFullDataW1071",
      "directBoundedLeftCalculusOfCurrentFullDataW1071",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1071",
      "currentFullDataInputNamesW1071_count"]
  providerRepackagingResult :=
    "proved: W1071 constructs the W1070 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1070"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1071 inherits W1070/W1069/W1068/W1067/W1066/W1065/W1064/\
      W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/\
      W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/\
      W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1071 W1017 current-full-data provider surface feeds\
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
  remainingInputs := currentFullDataInputNamesW1071
  productSuccessClaimed := false

theorem currentW1071CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1071;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
