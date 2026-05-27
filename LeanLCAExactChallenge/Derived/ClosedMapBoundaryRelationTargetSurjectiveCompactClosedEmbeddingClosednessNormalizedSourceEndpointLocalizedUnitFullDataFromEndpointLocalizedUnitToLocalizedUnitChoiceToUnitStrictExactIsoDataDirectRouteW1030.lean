import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1029
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitRoute

/-!
W1030 replaces W1029's W982 localized-unit-choice provider surface by the
existing W1003 endpoint-localized-unit surface. W1003 already constructs W982,
and W1030 feeds that provider into W1029.
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

/-- W1030 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 endpointLocalizedUnitData

/-- W1030 constructs the W981 provider surface from W1003 through W1029. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W971 component-field surface from W1003 through W1029. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W1008 current-full-data surface from W1003 through W1029. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W1007 branch-full-data surface from W1003 through W1029. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1029. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1029. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1029. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1029. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the rebuilt W982 localized-unit-choice surface after routing through W1029. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the rebuilt W981 surface after routing through W1029. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the rebuilt W971 component fields after routing through W1029. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the rebuilt W1008 current-full-data surface after routing through W1029. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the rebuilt W1007 branch-full-data surface after routing through W1029. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1029. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 exposes the twice-rebuilt W971 component fields after routing through W1029. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs W977 current full data from W1003 through W1029. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 constructs W987 branch full data from W1003 through W1029. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 recovers W715 target surjective-compact data from W1003 through W1029. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

/-- W1030 returns the constructed W987 branch full data from W1003 through W1029. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1030
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1030 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1030 : List String :=
  endpointLocalizedUnitInputNamesW1003

theorem endpointLocalizedUnitInputNamesW1030_count :
    endpointLocalizedUnitInputNamesW1030.length = 5 :=
  endpointLocalizedUnitInputNamesW1003_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1030 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1030 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1030
    where
  seed := "w1030-endpoint-localized-unit-to-w1029-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1030",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1030",
      "componentFieldsOfEndpointLocalizedUnitW1030",
      "currentFullDataProviderOfEndpointLocalizedUnitW1030",
      "branchFullDataProviderOfEndpointLocalizedUnitW1030",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1030",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1030",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1030",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1030",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1030",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1030",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1030",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1030",
      "currentFullDataOfEndpointLocalizedUnitW1030",
      "branchFullDataOfEndpointLocalizedUnitW1030",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1030",
      "fullDataOfEndpointLocalizedUnitW1030",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1030",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1030",
      "endpointLocalizedUnitInputNamesW1030_count"]
  providerRepackagingResult :=
    "proved: W1030 constructs the W1029 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data and feeds W1029"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1030 inherits W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W1003 constructs W982"
  exactAtResult :=
    "proved: the W1030 W1003 endpoint-localized-unit provider surface feeds\
      W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1030
  productSuccessClaimed := false

theorem currentW1030EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1030;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
