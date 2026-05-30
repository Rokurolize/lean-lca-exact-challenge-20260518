import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1043
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataDirectRoute

/-!
W1044 replaces W1043's W1007 branch-full-data surface by the existing W1008
current-full-data surface. W1008 already constructs W1007 from W977 current
full data, and W1044 feeds that provider into W1043.
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

/-- W1044 constructs the W1007 branch-full-data surface from W1008 data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1008 currentFullData

/-- W1044 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1043. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1043. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1043. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W1003 endpoint-localized-unit surface from W1008 through W1043. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W982 localized-unit-choice surface from W1008 through W1043. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W981 provider surface from W1008 through W1043. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W971 component-field surface from W1008 through W1043. -/
noncomputable def componentFieldsOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs the W1008 current-full-data surface from W1008 through W1043. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1007 branch-full-data surface after routing through W1043. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1043. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1043. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1043. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1043. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W982 localized-unit-choice surface after routing through W1043. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W981 surface after routing through W1043. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W971 component fields after routing through W1043. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1008 current-full-data surface after routing through W1043. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the rebuilt W1007 branch-full-data surface after routing through W1043. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1043. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 exposes the twice-rebuilt W971 component fields after routing through W1043. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs W977 current full data from W1008 through W1043. -/
noncomputable def currentFullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 constructs W987 branch full data from W1008 through W1043. -/
noncomputable def branchFullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 recovers W715 target surjective-compact data from W1008 through W1043. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

/-- W1044 returns the constructed W987 branch full data from W1008 through W1043. -/
noncomputable def fullDataOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1044
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1043
    (branchFullDataProviderOfCurrentFullDataW1044 currentFullData)

def currentFullDataInputNamesW1044 : List String :=
  currentFullDataInputNamesW1008

theorem currentFullDataInputNamesW1044_count :
    currentFullDataInputNamesW1044.length = 1 :=
  currentFullDataInputNamesW1008_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1044 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1044 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1044
    where
  seed := "w1044-current-full-data-to-w1043-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1044",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1044",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1044",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1044",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1044",
      "localizedUnitChoiceDataOfCurrentFullDataW1044",
      "unitStrictExactIsoDataOfCurrentFullDataW1044",
      "componentFieldsOfCurrentFullDataW1044",
      "currentFullDataProviderOfCurrentFullDataW1044",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1044",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1044",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1044",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1044",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1044",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1044",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1044",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1044",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1044",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1044",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1044",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1044",
      "currentFullDataOfCurrentFullDataW1044",
      "branchFullDataOfCurrentFullDataW1044",
      "targetSurjectiveCompactDataOfCurrentFullDataW1044",
      "fullDataOfCurrentFullDataW1044",
      "directBoundedLeftCalculusOfCurrentFullDataW1044",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1044",
      "currentFullDataInputNamesW1044_count"]
  providerRepackagingResult :=
    "proved: W1044 constructs the W1043 W1007 branch-full-data provider\
      surface from W1008 current-full-data and feeds W1043"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1044 inherits W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1008 constructs W1007"
  exactAtResult :=
    "proved: the W1044 W1008 current-full-data provider surface feeds\
      W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1044
  productSuccessClaimed := false

theorem currentW1044CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1044;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
