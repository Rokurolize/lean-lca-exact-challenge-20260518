import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRouteW1028
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataRoute

/-!
W1029 replaces W1028's W981 endpoint/unit-strict-exact provider surface by the
existing W982 localized-unit-choice surface. W982 already constructs W981, and
W1029 feeds that provider into W1028.
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

/-- W1029 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  fullDataOfLocalizedUnitChoiceW982 localizedUnitChoiceData

/-- W1029 constructs the W971 component-field surface from W982 through W1028. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1008 current-full-data surface from W982 through W1028. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1007 branch-full-data surface from W982 through W1028. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1006 target/closedness/normalized-source/endpoint surface from W982 through W1028. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1005 target/closed-embedding-closedness surface from W982 through W1028. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1004 normalized-source/endpoint-localized-unit surface from W982 through W1028. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs the W1003 endpoint-localized-unit surface from W982 through W1028. -/
noncomputable def endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the rebuilt W982 localized-unit-choice surface after routing through W1028. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the rebuilt W981 surface after routing through W1028. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the rebuilt W971 component fields after routing through W1028. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the rebuilt W1008 current-full-data surface after routing through W1028. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the rebuilt W1007 branch-full-data surface after routing through W1028. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1028. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 exposes the twice-rebuilt W971 component fields after routing through W1028. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs W977 current full data from W982 through W1028. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 constructs W987 branch full data from W982 through W1028. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 recovers W715 target surjective-compact data from W982 through W1028. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

/-- W1029 returns the constructed W987 branch full data from W982 through W1028. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1029
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1028
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1029 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1029 : List String :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982

theorem localizedUnitChoiceInputNamesW1029_count :
    localizedUnitChoiceInputNamesW1029.length = 6 :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count

structure MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1029 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1029 :
    MetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1029
    where
  seed := "w1029-localized-unit-choice-to-w1028-unit-strict-exact-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1029",
      "componentFieldsOfLocalizedUnitChoiceW1029",
      "currentFullDataProviderOfLocalizedUnitChoiceW1029",
      "branchFullDataProviderOfLocalizedUnitChoiceW1029",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1029",
      "targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1029",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029",
      "endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1029",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1029",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1029",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029",
      "currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1029",
      "branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1029",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1029",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1029",
      "currentFullDataOfLocalizedUnitChoiceW1029",
      "branchFullDataOfLocalizedUnitChoiceW1029",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1029",
      "fullDataOfLocalizedUnitChoiceW1029",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1029",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1029",
      "localizedUnitChoiceInputNamesW1029_count"]
  providerRepackagingResult :=
    "proved: W1029 constructs the W1028 W981 endpoint/unit-strict-exact\
      provider surface from W982 localized-unit-choice data and feeds W1028"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1029 inherits W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W982 constructs W981"
  exactAtResult :=
    "proved: the W1029 W982 localized-unit-choice provider surface feeds\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/\
      W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/\
      W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1029
  productSuccessClaimed := false

theorem currentW1029LocalizedUnitChoiceToUnitStrictExactIsoDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteStateW1029;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
