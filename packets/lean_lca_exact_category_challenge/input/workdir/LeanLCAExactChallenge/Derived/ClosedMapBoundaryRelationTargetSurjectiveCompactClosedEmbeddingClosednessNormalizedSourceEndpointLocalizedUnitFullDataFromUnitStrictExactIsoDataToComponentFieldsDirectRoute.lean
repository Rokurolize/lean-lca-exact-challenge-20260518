import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsToCurrentFullDataDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoDataDirectRoute

/-!
W1019 replaces W1018's W971 component-field surface by the existing W1010
endpoint/unit-strict-exact provider surface. W1010 already constructs W971
component fields from W981, and W1019 feeds those fields into W1018.
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

/-- W1019 constructs the W1018 component-field surface from W981 data through W1010. -/
def componentFieldsOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoDataW1010 unitStrictExactIsoData

/-- W1019 constructs the W1008 current-full-data surface from W981 data through W1018. -/
noncomputable def currentFullDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs the W1007 branch-full-data surface from W981 data through W1018. -/
noncomputable def branchFullDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs the W1006 target/closedness/normalized-source/endpoint surface from W981 data through W1018. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs the W1005 target/closed-embedding-closedness surface from W981 data through W1018. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs the W1004 normalized-source/endpoint-localized-unit surface from W981 data through W1018. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs the W982 localized-unit-choice surface from W981 data through W1018. -/
noncomputable def localizedUnitChoiceDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 exposes the rebuilt W971 component fields after routing through W1018. -/
noncomputable def componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs W977 current full data from W981 data through W1018. -/
noncomputable def currentFullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 constructs W987 branch full data from W981 data through W1018. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 recovers W715 target surjective-compact data from W981 data through W1018. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

/-- W1019 returns the constructed W987 branch full data from W981 data through W1018. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1019
    (unitStrictExactIsoData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1018
    (componentFieldsOfUnitStrictExactIsoDataW1019 unitStrictExactIsoData)

def unitStrictExactIsoDataInputNamesW1019 : List String :=
  unitStrictExactIsoDataInputNamesW1010

theorem unitStrictExactIsoDataInputNamesW1019_count :
    unitStrictExactIsoDataInputNamesW1019.length = 7 :=
  unitStrictExactIsoDataInputNamesW1010_count

structure MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1019 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1019 :
    MetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1019
    where
  seed := "w1019-unit-strict-exact-iso-data-to-w1018-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1019",
      "currentFullDataProviderOfUnitStrictExactIsoDataW1019",
      "branchFullDataProviderOfUnitStrictExactIsoDataW1019",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfUnitStrictExactIsoDataW1019",
      "targetClosedEmbeddingClosednessDataProviderOfUnitStrictExactIsoDataW1019",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfUnitStrictExactIsoDataW1019",
      "localizedUnitChoiceDataOfUnitStrictExactIsoDataW1019",
      "componentFieldsOfComponentFieldsOfUnitStrictExactIsoDataW1019",
      "currentFullDataOfUnitStrictExactIsoDataW1019",
      "branchFullDataOfUnitStrictExactIsoDataW1019",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1019",
      "fullDataOfUnitStrictExactIsoDataW1019",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1019",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1019",
      "unitStrictExactIsoDataInputNamesW1019_count"]
  providerRepackagingResult :=
    "proved: W1019 constructs the W1018 W971 component-field surface from\
      W981 endpoint/unit-strict-exact provider data through W1010 and feeds\
      W1018"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1019 inherits W1018/W1017/W1016/W1015/W1014/W1013/W1012/\
      W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998\
      target surjective-compact recovery after W1010 constructs W971 fields"
  exactAtResult :=
    "proved: the W1019 W981 endpoint/unit-strict-exact provider surface feeds\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1019
  productSuccessClaimed := false

theorem currentW1019UnitStrictExactIsoDataToComponentFieldsDirectRoute_productSuccess :
    (let state :=
        currentMetrizableUnitStrictExactIsoDataToComponentFieldsDirectRouteStateW1019;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
