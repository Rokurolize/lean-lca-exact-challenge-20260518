import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1079
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1080 replaces W1079's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1080 feeds
that provider into W1079.
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

/-- W1080 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1080 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1079. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1079. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1079. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W1003 endpoint-localized-unit surface from W1008 through W1079. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W982 localized-unit-choice surface from W1008 through W1079. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W981 provider surface from W1008 through W1079. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W971 component-field surface from W1008 through W1079. -/
noncomputable def componentFieldsOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs the W1008 current-full-data surface from W1008 through W1079. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1007 branch-full-data surface after routing through W1079. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1079. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1079. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1079. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1079. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W982 localized-unit-choice surface after routing through W1079. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W981 surface after routing through W1079. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W971 component fields after routing through W1079. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1008 current-full-data surface after routing through W1079. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the rebuilt W1007 branch-full-data surface after routing through W1079. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1079. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 exposes the twice-rebuilt W971 component fields after routing through W1079. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs W977 current full data from W1008 through W1079. -/
noncomputable def currentFullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 constructs W987 branch full data from W1008 through W1079. -/
noncomputable def branchFullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 recovers W715 target surjective-compact data from W1008 through W1079. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

/-- W1080 returns the constructed W987 branch full data from W1008 through W1079. -/
noncomputable def fullDataOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1080
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1079
    (branchFullDataProviderOfCurrentFullDataW1080 currentFullData)

def currentFullDataInputNamesW1080 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1080_count :
    currentFullDataInputNamesW1080.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1080 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1080 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1080
    where
  seed := "w1080-current-full-data-to-w1079-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1080",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1080",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1080",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1080",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1080",
      "localizedUnitChoiceDataOfCurrentFullDataW1080",
      "unitStrictExactIsoDataOfCurrentFullDataW1080",
      "componentFieldsOfCurrentFullDataW1080",
      "currentFullDataProviderOfCurrentFullDataW1080",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1080",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1080",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1080",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1080",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1080",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1080",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1080",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1080",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1080",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1080",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1080",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1080",
      "currentFullDataOfCurrentFullDataW1080",
      "branchFullDataOfCurrentFullDataW1080",
      "targetSurjectiveCompactDataOfCurrentFullDataW1080",
      "fullDataOfCurrentFullDataW1080",
      "directBoundedLeftCalculusOfCurrentFullDataW1080",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1080",
      "currentFullDataInputNamesW1080_count"]
  providerRepackagingResult :=
    "proved: W1080 constructs the W1079 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1079"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1080 inherits W1079/W1078/W1077/W1076/W1075/W1074/W1073/\
      W1072/W1071/W1070/W1069/W1068/W1067/W1066/W1065/W1064/W1063/\
      W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/\
      W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/\
      W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1080 W1017 current-full-data provider surface feeds\
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
  remainingInputs := currentFullDataInputNamesW1080
  productSuccessClaimed := false

theorem currentW1080CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1080;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
