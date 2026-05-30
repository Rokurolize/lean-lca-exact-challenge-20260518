import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessRoute

/-!
W1023 replaces W1022's W1004 normalized-source/endpoint-localized-unit provider
surface by the existing W1005 target/closed-embedding-closedness surface. W1005
already constructs W1004, and W1023 feeds that provider into W1022.
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

/-- W1023 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    targetClosedEmbeddingClosednessData

/-- W1023 constructs the W1003 endpoint-localized-unit surface from W1005 through W1022. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W982 localized-unit-choice surface from W1005 through W1022. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W981 provider surface from W1005 through W1022. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W971 component-field surface from W1005 through W1022. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W1008 current-full-data surface from W1005 through W1022. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W1007 branch-full-data surface from W1005 through W1022. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1005 through W1022. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs the W1005 target/closed-embedding-closedness surface from W1005 through W1022. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 exposes the rebuilt W982 localized-unit-choice surface after routing through W1022. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 exposes the rebuilt W971 component fields after routing through W1022. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs W977 current full data from W1005 through W1022. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 constructs W987 branch full data from W1005 through W1022. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 recovers W715 target surjective-compact data from W1005 through W1022. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

/-- W1023 returns the constructed W987 branch full data from W1005 through W1022. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1023
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1023 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1005

theorem targetClosedEmbeddingClosednessInputNamesW1023_count :
    targetClosedEmbeddingClosednessInputNamesW1023.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1005_count

structure MetrizableTargetClosedEmbeddingClosednessToComponentFieldsDirectRouteStateW1023 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessToComponentFieldsDirectRouteStateW1023 :
    MetrizableTargetClosedEmbeddingClosednessToComponentFieldsDirectRouteStateW1023
    where
  seed := "w1023-target-closed-embedding-closedness-to-w1022-component-fields-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1023",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1023",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1023",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1023",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1023",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1023",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1023",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1023",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1023",
      "fullDataOfTargetClosedEmbeddingClosednessW1023",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1023",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1023",
      "targetClosedEmbeddingClosednessInputNamesW1023_count"]
  providerRepackagingResult :=
    "proved: W1023 constructs the W1022 W1004 normalized-source/endpoint-localized-unit\
      provider surface from W1005 target/closed-embedding-closedness data and feeds W1022"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1023 inherits W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998 target surjective-compact recovery after W1005 constructs W1004"
  exactAtResult :=
    "proved: the W1023 W1005 target/closed-embedding-closedness provider\
      surface feeds W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/\
      W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1023
  productSuccessClaimed := false

theorem currentW1023TargetClosedEmbeddingClosednessToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessToComponentFieldsDirectRouteStateW1023;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
