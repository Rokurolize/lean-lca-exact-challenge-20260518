import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitDirectRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessRoute

/-!
W1014 replaces W1013's W1004 normalized-source/endpoint-localized-unit surface
by the existing W1005 target/closed-embedding-closedness surface. W1005 already
constructs W1004, and W1014 feeds that provider into W1013.
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

/-- W1014 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    targetClosedEmbeddingClosednessData

/-- W1014 constructs the W982 localized-unit-choice surface from W1005 through W1013. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 constructs the W971 component-field surface from W1005 through W1013. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 constructs W977 current full data from W1005 through W1013. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 builds the W1008 provider surface through W1013. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 constructs W987 branch full data through W1013. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 recovers W715 target surjective-compact data through W1013. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

/-- W1014 returns the constructed W987 branch full data through W1013. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1014
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1013
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1014 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1005

theorem targetClosedEmbeddingClosednessInputNamesW1014_count :
    targetClosedEmbeddingClosednessInputNamesW1014.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1005_count

structure MetrizableTargetClosedEmbeddingClosednessDirectRouteStateW1014 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessDirectRouteStateW1014 :
    MetrizableTargetClosedEmbeddingClosednessDirectRouteStateW1014
    where
  seed := "w1014-target-closed-embedding-closedness-to-w1013-normalized-source-endpoint-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1014",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1014",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1014",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1014",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1014",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1014",
      "fullDataOfTargetClosedEmbeddingClosednessW1014",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1014",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1014",
      "targetClosedEmbeddingClosednessInputNamesW1014_count"]
  providerRepackagingResult :=
    "proved: W1014 constructs the W1004 normalized-source/endpoint-localized\
      provider surface from W1005 target/closed-embedding-closedness data and feeds W1013"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1014 inherits W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact recovery\
      after W1005 constructs W1004"
  exactAtResult :=
    "proved: the W1014 W1005 target/closed-embedding-closedness provider\
      surface feeds W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/\
      W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1014
  productSuccessClaimed := false

theorem currentW1014TargetClosedEmbeddingClosednessDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessDirectRouteStateW1014;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
