import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataDirectRouteW1047
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitDirectRoute

/-!
W1048 replaces W1047's W982 localized-unit-choice provider surface by the
existing W1012 endpoint-localized-unit surface. W1012 already constructs W982,
and W1048 feeds that provider into W1047.
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

/-- W1048 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1012 endpointLocalizedUnitData

/-- W1048 constructs the W981 provider surface from W1003 through W1047. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W971 component-field surface from W1003 through W1047. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W1008 current-full-data surface from W1003 through W1047. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W1007 branch-full-data surface from W1003 through W1047. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1047. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1047. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1047. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 returns the rebuilt W1003 endpoint-localized-unit surface after routing through W1047. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W982 localized-unit-choice surface after routing through W1047. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W981 surface after routing through W1047. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W971 component fields after routing through W1047. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1008 current-full-data surface after routing through W1047. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1007 branch-full-data surface after routing through W1047. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1047. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1047. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1047. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1047 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W982 localized-unit-choice surface after the nested W1047 pass. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W981 surface after the nested W1047 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W971 component fields after the nested W1047 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1008 current-full-data surface after the nested W1047 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the rebuilt W1007 branch-full-data surface after the nested W1047 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1047. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 exposes the twice-rebuilt W971 component fields after routing through W1047. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs W977 current full data from W1003 through W1047. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 constructs W987 branch full data from W1003 through W1047. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 recovers W715 target surjective-compact data from W1003 through W1047. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

/-- W1048 returns the constructed W987 branch full data from W1003 through W1047. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1048
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1047
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1048 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1048 : List String :=
  endpointLocalizedUnitInputNamesW1012

theorem endpointLocalizedUnitInputNamesW1048_count :
    endpointLocalizedUnitInputNamesW1048.length = 5 :=
  endpointLocalizedUnitInputNamesW1012_count

structure MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1048 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1048 :
    MetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1048
    where
  seed := "w1048-endpoint-localized-unit-to-w1047-localized-unit-choice-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1048",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1048",
      "componentFieldsOfEndpointLocalizedUnitW1048",
      "currentFullDataProviderOfEndpointLocalizedUnitW1048",
      "branchFullDataProviderOfEndpointLocalizedUnitW1048",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1048",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1048",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1048",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1048",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1048",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048",
      "currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1048",
      "branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1048",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1048",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1048",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1048",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1048",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1048",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1048",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1048",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1048",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1048",
      "currentFullDataOfEndpointLocalizedUnitW1048",
      "branchFullDataOfEndpointLocalizedUnitW1048",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1048",
      "fullDataOfEndpointLocalizedUnitW1048",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1048",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1048",
      "endpointLocalizedUnitInputNamesW1048_count"]
  providerRepackagingResult :=
    "proved: W1048 constructs the W1047 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data through W1012 and feeds W1047"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1048 inherits W1047/W1046/W1045/W1044/W1043/W1042/\
      W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/W1033/W1032/\
      W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/W1022/\
      W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/\
      W998 target surjective-compact recovery after W1012 constructs W982"
  exactAtResult :=
    "proved: the W1048 W1003 endpoint-localized-unit provider surface feeds\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1048
  productSuccessClaimed := false

theorem currentW1048EndpointLocalizedUnitToLocalizedUnitChoiceDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteStateW1048;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
