import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataToTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRouteW1034
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataDirectRoute

/-!
W1035 replaces W1034's W1007 branch-full-data surface by the existing W1008
current-full-data surface. W1008 already constructs W1007 from W977 current
full data, and W1035 feeds that provider into W1034.
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

/-- W1035 constructs the W1007 branch-full-data surface from W1008 data. -/
noncomputable def branchFullDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1008 currentFullData

/-- W1035 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1008 through W1034. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W1005 target/closed-embedding-closedness surface from W1008 through W1034. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1008 through W1034. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W1003 endpoint-localized-unit surface from W1008 through W1034. -/
noncomputable def endpointLocalizedUnitDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W982 localized-unit-choice surface from W1008 through W1034. -/
noncomputable def localizedUnitChoiceDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W981 provider surface from W1008 through W1034. -/
noncomputable def unitStrictExactIsoDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W971 component-field surface from W1008 through W1034. -/
noncomputable def componentFieldsOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs the W1008 current-full-data surface from W1008 through W1034. -/
noncomputable def currentFullDataProviderOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1007 branch-full-data surface after routing through W1034. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1034. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1034. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1034. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1034. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W982 localized-unit-choice surface after routing through W1034. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W981 surface after routing through W1034. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W971 component fields after routing through W1034. -/
noncomputable def componentFieldsOfComponentFieldsOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1008 current-full-data surface after routing through W1034. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the rebuilt W1007 branch-full-data surface after routing through W1034. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1034. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 exposes the twice-rebuilt W971 component fields after routing through W1034. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs W977 current full data from W1008 through W1034. -/
noncomputable def currentFullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 constructs W987 branch full data from W1008 through W1034. -/
noncomputable def branchFullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 recovers W715 target surjective-compact data from W1008 through W1034. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

/-- W1035 returns the constructed W987 branch full data from W1008 through W1034. -/
noncomputable def fullDataOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW1035
    (currentFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1034
    (branchFullDataProviderOfCurrentFullDataW1035 currentFullData)

def currentFullDataInputNamesW1035 : List String :=
  currentFullDataInputNamesW1008

theorem currentFullDataInputNamesW1035_count :
    currentFullDataInputNamesW1035.length = 1 :=
  currentFullDataInputNamesW1008_count

structure MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1035 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1035 :
    MetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1035
    where
  seed := "w1035-current-full-data-to-w1034-branch-full-data-route"
  declarations :=
    ["branchFullDataProviderOfCurrentFullDataW1035",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1035",
      "targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1035",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1035",
      "endpointLocalizedUnitDataProviderOfCurrentFullDataW1035",
      "localizedUnitChoiceDataOfCurrentFullDataW1035",
      "unitStrictExactIsoDataOfCurrentFullDataW1035",
      "componentFieldsOfCurrentFullDataW1035",
      "currentFullDataProviderOfCurrentFullDataW1035",
      "branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1035",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1035",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1035",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1035",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1035",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1035",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1035",
      "componentFieldsOfComponentFieldsOfCurrentFullDataW1035",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1035",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1035",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1035",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1035",
      "currentFullDataOfCurrentFullDataW1035",
      "branchFullDataOfCurrentFullDataW1035",
      "targetSurjectiveCompactDataOfCurrentFullDataW1035",
      "fullDataOfCurrentFullDataW1035",
      "directBoundedLeftCalculusOfCurrentFullDataW1035",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW1035",
      "currentFullDataInputNamesW1035_count"]
  providerRepackagingResult :=
    "proved: W1035 constructs the W1034 W1007 branch-full-data provider\
      surface from W1008 current-full-data and feeds W1034"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1035 inherits W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1008 constructs W1007"
  exactAtResult :=
    "proved: the W1035 W1008 current-full-data provider surface feeds\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW1035
  productSuccessClaimed := false

theorem currentW1035CurrentFullDataToBranchFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableCurrentFullDataToBranchFullDataDirectRouteStateW1035;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
