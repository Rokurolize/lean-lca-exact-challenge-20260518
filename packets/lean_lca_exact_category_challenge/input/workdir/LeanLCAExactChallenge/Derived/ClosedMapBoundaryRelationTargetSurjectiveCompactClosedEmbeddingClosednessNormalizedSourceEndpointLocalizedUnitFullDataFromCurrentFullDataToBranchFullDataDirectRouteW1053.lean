import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1052
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1053 replaces W1052's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1053 feeds
that provider into W1052.
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

/-- W1053 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1053 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1052. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1052. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1052. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W1003 endpoint-localized-unit surface from W1008 through W1052. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W982 localized-unit-choice surface from W1008 through W1052. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W981 provider surface from W1008 through W1052. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W971 component-field surface from W1008 through W1052. -/
noncomputable def componentFieldsOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs the W1008 current-full-data surface from W1008 through W1052. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1007 branch-full-data surface after routing through W1052. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1052. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1052. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1052. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1052. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W982 localized-unit-choice surface after routing through W1052. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W981 surface after routing through W1052. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W971 component fields after routing through W1052. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1008 current-full-data surface after routing through W1052. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the rebuilt W1007 branch-full-data surface after routing through W1052. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1052. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 exposes the twice-rebuilt W971 component fields after routing through W1052. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs W977 current full data from W1008 through W1052. -/
noncomputable def currentFullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 constructs W987 branch full data from W1008 through W1052. -/
noncomputable def branchFullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 recovers W715 target surjective-compact data from W1008 through W1052. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

/-- W1053 returns the constructed W987 branch full data from W1008 through W1052. -/
noncomputable def fullDataOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1053
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1052
    (branchFullDataProviderOfCurrentFullDataW1053 currentFullData)

def currentFullDataInputNamesW1053 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1053_count :
    currentFullDataInputNamesW1053.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1053 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1053 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1053
    where
  seed := "w1053-current-full-data-to-w1052-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1053",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1053",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1053",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1053",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1053",
      "localizedUnitChoiceDataOfCurrentFullDataW1053",
      "unitStrictExactIsoDataOfCurrentFullDataW1053",
      "componentFieldsOfCurrentFullDataW1053",
      "currentFullDataProviderOfCurrentFullDataW1053",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1053",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1053",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1053",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1053",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1053",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1053",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1053",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1053",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1053",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1053",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1053",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1053",
      "currentFullDataOfCurrentFullDataW1053",
      "branchFullDataOfCurrentFullDataW1053",
      "targetSurjectiveCompactDataOfCurrentFullDataW1053",
      "fullDataOfCurrentFullDataW1053",
      "directBoundedLeftCalculusOfCurrentFullDataW1053",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1053",
      "currentFullDataInputNamesW1053_count"]
  providerRepackagingResult :=
    "proved: W1053 constructs the W1052 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1052"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1053 inherits W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1053 W1017 current-full-data provider surface feeds\
      W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/\
      W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1053
  productSuccessClaimed := false

theorem currentW1053CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1053;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
