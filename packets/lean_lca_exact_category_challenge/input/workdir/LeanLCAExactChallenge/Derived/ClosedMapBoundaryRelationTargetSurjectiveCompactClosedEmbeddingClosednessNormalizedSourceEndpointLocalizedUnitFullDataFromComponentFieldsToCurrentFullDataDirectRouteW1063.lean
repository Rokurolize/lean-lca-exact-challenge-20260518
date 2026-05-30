import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataToBranchFullDataDirectRouteW1062
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute

/-!
W1063 replaces W1062's W1017 current-full-data input surface by the existing
W1018 component-field route. W1018 already constructs W1008, and W1063 feeds
that provider into W1062.
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

/-- W1063 constructs the W1008 current-full-data surface from W1018 component fields. -/
def currentFullDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018 componentFields

/-- W1063 constructs the W1007 branch-full-data surface from W1009 through W1062. -/
noncomputable def branchFullDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1009 through W1062. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W1005 target/closed-embedding-closedness surface from W1009 through W1062. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1009 through W1062. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W1003 endpoint-localized-unit surface from W1009 through W1062. -/
noncomputable def endpointLocalizedUnitDataProviderOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W982 localized-unit-choice surface from W1009 through W1062. -/
noncomputable def localizedUnitChoiceDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W981 provider surface from W1009 through W1062. -/
noncomputable def unitStrictExactIsoDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs the W971 component-field surface from W1009 through W1062. -/
noncomputable def componentFieldsOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1008 current-full-data surface after routing through W1062. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1007 branch-full-data surface after routing through W1062. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1062. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1062. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1062. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1062. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W982 localized-unit-choice surface after routing through W1062. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W981 surface after routing through W1062. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W971 component fields after routing through W1062. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1008 current-full-data surface after routing through W1062. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the rebuilt W1007 branch-full-data surface after routing through W1062. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1062. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 exposes the twice-rebuilt W971 component fields after routing through W1062. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs W977 current full data from W1009 through W1062. -/
noncomputable def currentFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 constructs W987 branch full data from W1009 through W1062. -/
noncomputable def branchFullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 recovers W715 target surjective-compact data from W1009 through W1062. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

/-- W1063 returns the constructed W987 branch full data from W1009 through W1062. -/
noncomputable def fullDataOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

theorem directBoundedLeftCalculusOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1063
    (componentFields :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW1062
    (currentFullDataProviderOfComponentFieldsW1063 componentFields)

def componentFieldsInputNamesW1063 : List String :=
  componentFieldsInputNamesW1018

theorem componentFieldsInputNamesW1063_count :
    componentFieldsInputNamesW1063.length = 18 :=
  componentFieldsInputNamesW1018_count

structure MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1063 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1063 :
    MetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1063
    where
  seed := "w1063-component-fields-to-w1062-current-full-data-route"
  declarations :=
    ["currentFullDataProviderOfComponentFieldsW1063",
      "branchFullDataProviderOfComponentFieldsW1063",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1063",
      "targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1063",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1063",
      "endpointLocalizedUnitDataProviderOfComponentFieldsW1063",
      "localizedUnitChoiceDataOfComponentFieldsW1063",
      "unitStrictExactIsoDataOfComponentFieldsW1063",
      "componentFieldsOfComponentFieldsW1063",
      "currentFullDataProviderOfCurrentFullDataOfComponentFieldsW1063",
      "branchFullDataProviderOfBranchFullDataOfComponentFieldsW1063",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfComponentFieldsW1063",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfComponentFieldsW1063",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfComponentFieldsW1063",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfComponentFieldsW1063",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfComponentFieldsW1063",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfComponentFieldsW1063",
      "componentFieldsOfComponentFieldsOfComponentFieldsW1063",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfComponentFieldsW1063",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfComponentFieldsW1063",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfComponentFieldsW1063",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsW1063",
      "currentFullDataOfComponentFieldsW1063",
      "branchFullDataOfComponentFieldsW1063",
      "targetSurjectiveCompactDataOfComponentFieldsW1063",
      "fullDataOfComponentFieldsW1063",
      "directBoundedLeftCalculusOfComponentFieldsW1063",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1063",
      "componentFieldsInputNamesW1063_count"]
  providerRepackagingResult :=
    "proved: W1063 constructs the W1062 W1008 current-full-data provider\
      surface from W1018 component fields and feeds W1062"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1063 inherits W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1018 constructs W1008"
  exactAtResult :=
    "proved: the W1063 W1018 component-field provider surface feeds\
      W1062/W1061/W1060/W1059/W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/W1045/W1044/\
      W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1063
  productSuccessClaimed := false

theorem currentW1063ComponentFieldsToCurrentFullDataDirectRoute_productSuccess :
    (let state :=
        currentMetrizableComponentFieldsToCurrentFullDataDirectRouteStateW1063;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
