import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1061
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRoute

/-!
W1062 replaces W1061's W1016 branch-full-data input surface by the existing
W1017 current-full-data route. W1017 already constructs W1007, and W1062 feeds
that provider into W1061.
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

/-- W1062 constructs the W1007 branch-full-data surface from W1017 current-full-data data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1017 currentFullData

/-- W1062 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1061. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1061. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1061. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W1003 endpoint-localized-unit surface from W1008 through W1061. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W982 localized-unit-choice surface from W1008 through W1061. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W981 provider surface from W1008 through W1061. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W971 component-field surface from W1008 through W1061. -/
noncomputable def componentFieldsOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs the W1008 current-full-data surface from W1008 through W1061. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1007 branch-full-data surface after routing through W1061. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1061. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1061. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1061. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1061. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W982 localized-unit-choice surface after routing through W1061. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W981 surface after routing through W1061. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W971 component fields after routing through W1061. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1008 current-full-data surface after routing through W1061. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the rebuilt W1007 branch-full-data surface after routing through W1061. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1061. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 exposes the twice-rebuilt W971 component fields after routing through W1061. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs W977 current full data from W1008 through W1061. -/
noncomputable def currentFullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 constructs W987 branch full data from W1008 through W1061. -/
noncomputable def branchFullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 recovers W715 target surjective-compact data from W1008 through W1061. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

/-- W1062 returns the constructed W987 branch full data from W1008 through W1061. -/
noncomputable def fullDataOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1062
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1061
    (branchFullDataProviderOfCurrentFullDataW1062 currentFullData)

def currentFullDataInputNamesW1062 : List String :=
  currentFullDataInputNamesW1017

theorem currentFullDataInputNamesW1062_count :
    currentFullDataInputNamesW1062.length = 1 :=
  currentFullDataInputNamesW1017_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1062 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1062 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1062
    where
  seed := "w1062-current-full-data-to-w1061-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1062",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1062",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1062",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1062",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1062",
      "localizedUnitChoiceDataOfCurrentFullDataW1062",
      "unitStrictExactIsoDataOfCurrentFullDataW1062",
      "componentFieldsOfCurrentFullDataW1062",
      "currentFullDataProviderOfCurrentFullDataW1062",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1062",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1062",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1062",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1062",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1062",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1062",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1062",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1062",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1062",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1062",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1062",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1062",
      "currentFullDataOfCurrentFullDataW1062",
      "branchFullDataOfCurrentFullDataW1062",
      "targetSurjectiveCompactDataOfCurrentFullDataW1062",
      "fullDataOfCurrentFullDataW1062",
      "directBoundedLeftCalculusOfCurrentFullDataW1062",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1062",
      "currentFullDataInputNamesW1062_count"]
  providerRepackagingResult :=
    "proved: W1062 constructs the W1061 W1007 branch-full-data provider\
      surface from W1017 current-full-data and feeds W1061"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1062 inherits W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1017 constructs W1007"
  exactAtResult :=
    "proved: the W1062 W1017 current-full-data provider surface feeds\
      W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/W1043/\
      W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1062
  productSuccessClaimed := false

theorem currentW1062CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1062;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
