import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceToUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1022 replaces W1021's W1003 endpoint-localized-unit provider surface by the
existing W1004 normalized-source/endpoint-localized-unit surface. W1004 already
constructs W1003, and W1022 feeds that provider into W1021.
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

/-- W1022 constructs the W1003 endpoint-localized-unit surface from W1004 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    normalizedSourceEndpointLocalizedUnitData

/-- W1022 constructs the W982 localized-unit-choice surface from W1004 through W1021. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W981 provider surface from W1004 through W1021. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W971 component-field surface from W1004 through W1021. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W1008 current-full-data surface from W1004 through W1021. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W1007 branch-full-data surface from W1004 through W1021. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1021. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1021. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1021. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 exposes the rebuilt W982 localized-unit-choice surface after routing through W1021. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 exposes the rebuilt W971 component fields after routing through W1021. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs W977 current full data from W1004 through W1021. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 constructs W987 branch full data from W1004 through W1021. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 recovers W715 target surjective-compact data from W1004 through W1021. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

/-- W1022 returns the constructed W987 branch full data from W1004 through W1021. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1022
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1022 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1022_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1022.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1022 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1022 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1022
    where
  seed := "w1022-normalized-source-endpoint-localized-unit-to-w1021-component-fields-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1022",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1022",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1022",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1022",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1022",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1022",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1022_count"]
  providerRepackagingResult :=
    "proved: W1022 constructs the W1021 W1003 endpoint-localized-unit\
      provider surface from W1004 normalized-source/endpoint-localized-unit\
      data and feeds W1021"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1022 inherits W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998 target surjective-compact recovery after W1004 constructs W1003"
  exactAtResult :=
    "proved: the W1022 W1004 normalized-source/endpoint-localized-unit\
      provider surface feeds W1021/W1020/W1019/W1018/W1017/W1016/W1015/\
      W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/\
      W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1022
  productSuccessClaimed := false

theorem currentW1022NormalizedSourceEndpointLocalizedUnitToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1022;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
