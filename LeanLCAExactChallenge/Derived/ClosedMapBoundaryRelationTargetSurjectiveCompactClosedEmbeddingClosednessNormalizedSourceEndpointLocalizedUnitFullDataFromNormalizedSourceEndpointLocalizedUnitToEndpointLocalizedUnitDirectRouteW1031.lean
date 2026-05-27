import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1030
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1031 replaces W1030's W1003 endpoint-localized-unit provider surface by the
existing W1004 normalized-source/endpoint-localized-unit surface. W1004 already
constructs W1003, and W1031 feeds that provider into W1030.
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

/-- W1031 constructs the W1003 endpoint-localized-unit surface from W1004 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    normalizedSourceEndpointLocalizedUnitData

/-- W1031 constructs the W982 localized-unit-choice surface from W1004 through W1030. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W981 provider surface from W1004 through W1030. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W971 component-field surface from W1004 through W1030. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W1008 current-full-data surface from W1004 through W1030. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W1007 branch-full-data surface from W1004 through W1030. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1030. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1030. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1030. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1030. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W982 localized-unit-choice surface after routing through W1030. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W981 surface after routing through W1030. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W971 component fields after routing through W1030. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W1008 current-full-data surface after routing through W1030. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the rebuilt W1007 branch-full-data surface after routing through W1030. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1030. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 exposes the twice-rebuilt W971 component fields after routing through W1030. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs W977 current full data from W1004 through W1030. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 constructs W987 branch full data from W1004 through W1030. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 recovers W715 target surjective-compact data from W1004 through W1030. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

/-- W1031 returns the constructed W987 branch full data from W1004 through W1030. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1031
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1031 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1031_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1031.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1031 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1031 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1031
    where
  seed := "w1031-normalized-source-endpoint-localized-unit-to-w1030-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1031",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1031",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1031",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1031",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1031",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1031",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1031",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1031",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1031_count"]
  providerRepackagingResult :=
    "proved: W1031 constructs the W1030 W1003 endpoint-localized-unit\
      provider surface from W1004 normalized-source/endpoint-localized-unit\
      data and feeds W1030"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1031 inherits W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W1004 constructs W1003"
  exactAtResult :=
    "proved: the W1031 W1004 normalized-source/endpoint-localized-unit\
      provider surface feeds W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1031
  productSuccessClaimed := false

theorem currentW1031NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1031;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
