import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataToComponentFieldsDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataRoute

/-!
W1020 replaces W1019's W981 endpoint/unit-strict-exact provider surface by the
existing W982 localized-unit-choice surface. W982 already constructs W981, and
W1020 feeds that provider into W1019.
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

/-- W1020 constructs the W981 provider surface from W982 localized-unit-choice data. -/
noncomputable def unitStrictExactIsoDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  fullDataOfLocalizedUnitChoiceW982 localizedUnitChoiceData

/-- W1020 constructs the W971 component-field surface from W982 through W1019. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W1008 current-full-data surface from W982 through W1019. -/
noncomputable def currentFullDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W1007 branch-full-data surface from W982 through W1019. -/
noncomputable def branchFullDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W1006 target/closedness/normalized-source/endpoint surface from W982 through W1019. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W1005 target/closed-embedding-closedness surface from W982 through W1019. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W1004 normalized-source/endpoint-localized-unit surface from W982 through W1019. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs the W982 localized-unit-choice surface from W982 through W1019. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 exposes the rebuilt W971 component fields after routing through W1019. -/
noncomputable def componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs W977 current full data from W982 through W1019. -/
noncomputable def currentFullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 constructs W987 branch full data from W982 through W1019. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 recovers W715 target surjective-compact data from W982 through W1019. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

/-- W1020 returns the constructed W987 branch full data from W982 through W1019. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1020
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoDataOfLocalizedUnitChoiceW1020 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1020 : List String :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982

theorem localizedUnitChoiceInputNamesW1020_count :
    localizedUnitChoiceInputNamesW1020.length = 6 :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count

structure MetrizableLocalizedUnitChoiceToComponentFieldsDirectRouteStateW1020 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceToComponentFieldsDirectRouteStateW1020 :
    MetrizableLocalizedUnitChoiceToComponentFieldsDirectRouteStateW1020
    where
  seed := "w1020-localized-unit-choice-to-w1019-component-fields-route"
  declarations :=
    ["unitStrictExactIsoDataOfLocalizedUnitChoiceW1020",
      "componentFieldsOfLocalizedUnitChoiceW1020",
      "currentFullDataProviderOfLocalizedUnitChoiceW1020",
      "branchFullDataProviderOfLocalizedUnitChoiceW1020",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfLocalizedUnitChoiceW1020",
      "targetClosedEmbeddingClosednessDataProviderOfLocalizedUnitChoiceW1020",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfLocalizedUnitChoiceW1020",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceW1020",
      "componentFieldsOfComponentFieldsOfLocalizedUnitChoiceW1020",
      "currentFullDataOfLocalizedUnitChoiceW1020",
      "branchFullDataOfLocalizedUnitChoiceW1020",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1020",
      "fullDataOfLocalizedUnitChoiceW1020",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1020",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1020",
      "localizedUnitChoiceInputNamesW1020_count"]
  providerRepackagingResult :=
    "proved: W1020 constructs the W1019 W981 endpoint/unit-strict-exact\
      provider surface from W982 localized-unit-choice data and feeds W1019"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1020 inherits W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W982 constructs W981"
  exactAtResult :=
    "proved: the W1020 W982 localized-unit-choice provider surface feeds\
      W1019/W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/\
      W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1020
  productSuccessClaimed := false

theorem currentW1020LocalizedUnitChoiceToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceToComponentFieldsDirectRouteStateW1020;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
