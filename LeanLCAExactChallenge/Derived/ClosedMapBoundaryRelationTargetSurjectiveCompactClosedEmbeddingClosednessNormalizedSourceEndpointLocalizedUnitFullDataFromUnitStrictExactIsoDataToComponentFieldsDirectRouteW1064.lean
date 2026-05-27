import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRouteW1063
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1064 replaces W1063's W1018 component-field input surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1064 feeds those fields into W1063.
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

/-- W1064 constructs the W1063 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1064 constructs the W1008 current-full-data surface from W981 data through W1063. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W1007 branch-full-data surface from W981 data through W1063. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1063. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1063. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1063. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W1003 endpoint-localized-unit surface from W981 data through W1063. -/
noncomputable def endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs the W982 localized-unit-choice surface from W981 data through W1063. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W981 surface after routing through W1063. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W971 component fields after routing through W1063. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1008 current-full-data surface after routing through W1063. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1007 branch-full-data surface after routing through W1063. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1063. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1063. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1063. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1063. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W982 localized-unit-choice surface after routing through W1063. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W981 surface after the nested W1063 pass. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W971 component fields after the nested W1063 pass. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1008 current-full-data surface after the nested W1063 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the rebuilt W1007 branch-full-data surface after the nested W1063 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1063. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 exposes the twice-rebuilt W971 component fields after routing through W1063. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs W977 current full data from W981 data through W1063. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 constructs W987 branch full data from W981 data through W1063. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 recovers W715 target surjective-compact data from W981 data through W1063. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

/-- W1064 returns the constructed W987 branch full data from W981 data through W1063. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1064
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1063
    (componentFieldsOfUnitStrictExactIsoDataW1064 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1064 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1064_count :
    unitStrictExactIsoDataInputNamesW1064.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1064 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1064 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1064
    where
  seed := "w1064-unit-strict-exact-iso-data-to-w1063-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1064",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1064",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1064",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1064",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1064",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064",
      "endpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1064",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1064",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataW1064",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064",
      "currentFullDataProviderOfCurrentFullDataOfUnitStrictExactIsoDataW1064",
      "branchFullDataProviderOfBranchFullDataOfUnitStrictExactIsoDataW1064",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfUnitStrictExactIsoDataW1064",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfUnitStrictExactIsoDataW1064",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfUnitStrictExactIsoDataW1064",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataW1064",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfUnitStrictExactIsoDataW1064",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfUnitStrictExactIsoDataW1064",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfUnitStrictExactIsoDataW1064",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1064",
      "currentFullDataOfUnitStrictExactIsoDataW1064",
      "branchFullDataOfUnitStrictExactIsoDataW1064",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1064",
      "fullDataOfUnitStrictExactIsoDataW1064",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1064",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1064",
      "unitStrictExactIsoDataInputNamesW1064_count"]
  providerRepackagingResult :=
    "proved: W1064 constructs the W1063 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1063"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1064 inherits W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/\
      W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1064 W981 endpoint/unit-strict-exact provider surface feeds\
      W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/\
      W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/\
      W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/\
      W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/\
      W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1064
  productSuccessClaimed := false

theorem currentW1064UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1064;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
