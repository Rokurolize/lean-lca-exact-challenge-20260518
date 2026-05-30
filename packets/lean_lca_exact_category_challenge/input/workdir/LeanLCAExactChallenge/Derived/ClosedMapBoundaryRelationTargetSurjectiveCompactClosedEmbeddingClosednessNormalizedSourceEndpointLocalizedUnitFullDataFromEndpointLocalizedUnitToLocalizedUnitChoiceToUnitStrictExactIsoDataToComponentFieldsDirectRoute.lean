import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceToUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitRoute

/-!
W1021 replaces W1020's W982 localized-unit-choice provider surface by the
existing W1003 endpoint-localized-unit surface. W1003 already constructs W982,
and W1021 feeds that provider into W1020.
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

/-- W1021 constructs the W982 localized-unit-choice surface from W1003 endpoint-localized-unit data. -/
def localizedUnitChoiceDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1003 endpointLocalizedUnitData

/-- W1021 constructs the W981 provider surface from W1003 through W1020. -/
noncomputable def unitStrictExactIsoDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W971 component-field surface from W1003 through W1020. -/
noncomputable def componentFieldsOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W1008 current-full-data surface from W1003 through W1020. -/
noncomputable def currentFullDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W1007 branch-full-data surface from W1003 through W1020. -/
noncomputable def branchFullDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1003 through W1020. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W1005 target/closed-embedding-closedness surface from W1003 through W1020. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1003 through W1020. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 exposes the rebuilt W982 localized-unit-choice surface after routing through W1020. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 exposes the rebuilt W971 component fields after routing through W1020. -/
noncomputable def componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs W977 current full data from W1003 through W1020. -/
noncomputable def currentFullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 constructs W987 branch full data from W1003 through W1020. -/
noncomputable def branchFullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 recovers W715 target surjective-compact data from W1003 through W1020. -/
noncomputable def targetSurjectiveCompactDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

/-- W1021 returns the constructed W987 branch full data from W1003 through W1020. -/
noncomputable def fullDataOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1021
    (endpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceDataOfEndpointLocalizedUnitW1021 endpointLocalizedUnitData)

def endpointLocalizedUnitInputNamesW1021 : List String :=
  endpointLocalizedUnitInputNamesW1003

theorem endpointLocalizedUnitInputNamesW1021_count :
    endpointLocalizedUnitInputNamesW1021.length = 5 :=
  endpointLocalizedUnitInputNamesW1003_count

structure MetrizableEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1021 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1021 :
    MetrizableEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1021
    where
  seed := "w1021-endpoint-localized-unit-to-w1020-component-fields-route"
  declarations :=
    ["localizedUnitChoiceDataOfEndpointLocalizedUnitW1021",
      "unitStrictExactIsoDataOfEndpointLocalizedUnitW1021",
      "componentFieldsOfEndpointLocalizedUnitW1021",
      "currentFullDataProviderOfEndpointLocalizedUnitW1021",
      "branchFullDataProviderOfEndpointLocalizedUnitW1021",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1021",
      "targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1021",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1021",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1021",
      "componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1021",
      "currentFullDataOfEndpointLocalizedUnitW1021",
      "branchFullDataOfEndpointLocalizedUnitW1021",
      "targetSurjectiveCompactDataOfEndpointLocalizedUnitW1021",
      "fullDataOfEndpointLocalizedUnitW1021",
      "directBoundedLeftCalculusOfEndpointLocalizedUnitW1021",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1021",
      "endpointLocalizedUnitInputNamesW1021_count"]
  providerRepackagingResult :=
    "proved: W1021 constructs the W1020 W982 localized-unit-choice provider\
      surface from W1003 endpoint-localized-unit data and feeds W1020"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1021 inherits W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998 target surjective-compact recovery after W1003 constructs W982"
  exactAtResult :=
    "proved: the W1021 W1003 endpoint-localized-unit provider surface feeds\
      W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/\
      W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointLocalizedUnitInputNamesW1021
  productSuccessClaimed := false

theorem currentW1021EndpointLocalizedUnitToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedUnitToComponentFieldsDirectRouteStateW1021;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
