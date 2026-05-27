import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromEndpointLocalizedUnitToLocalizedUnitChoiceDirectRouteW1039
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitRoute

/-!
W1040 replaces W1039's W1003 endpoint-localized-unit provider surface by the
existing W1004 normalized-source/endpoint-localized-unit surface. W1004 already
constructs W1003, and W1040 feeds that provider into W1039.
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

/-- W1040 constructs the W1003 endpoint-localized-unit surface from W1004 data. -/
def endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1004
    normalizedSourceEndpointLocalizedUnitData

/-- W1040 constructs the W982 localized-unit-choice surface from W1004 through W1039. -/
def localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W981 provider surface from W1004 through W1039. -/
noncomputable def unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W971 component-field surface from W1004 through W1039. -/
noncomputable def componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W1008 current-full-data surface from W1004 through W1039. -/
noncomputable def currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W1007 branch-full-data surface from W1004 through W1039. -/
noncomputable def branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1004 through W1039. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs the W1005 target/closed-embedding-closedness surface from W1004 through W1039. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1039. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1039. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W982 localized-unit-choice surface after routing through W1039. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W981 surface after routing through W1039. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W971 component fields after routing through W1039. -/
noncomputable def componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1008 current-full-data surface after routing through W1039. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1007 branch-full-data surface after routing through W1039. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1039. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1039. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1039. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1003 endpoint-localized-unit surface after the nested W1039 pass. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1039. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the twice-rebuilt W981 surface after routing through W1039. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the twice-rebuilt W971 component fields after routing through W1039. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1008 current-full-data surface after the nested W1039 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the rebuilt W1007 branch-full-data surface after the nested W1039 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1039. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 exposes the triply rebuilt W971 component fields after routing through W1039. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs W977 current full data from W1004 through W1039. -/
noncomputable def currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 constructs W987 branch full data from W1004 through W1039. -/
noncomputable def branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 recovers W715 target surjective-compact data from W1004 through W1039. -/
noncomputable def targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

/-- W1040 returns the constructed W987 branch full data from W1004 through W1039. -/
noncomputable def fullDataOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

theorem directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1040
    (normalizedSourceEndpointLocalizedUnitData :
      BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitW1039
    (endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040
      normalizedSourceEndpointLocalizedUnitData)

def normalizedSourceEndpointLocalizedUnitInputNamesW1040 : List String :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004

theorem normalizedSourceEndpointLocalizedUnitInputNamesW1040_count :
    normalizedSourceEndpointLocalizedUnitInputNamesW1040.length = 4 :=
  normalizedSourceEndpointLocalizedUnitInputNamesW1004_count

structure MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1040 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1040 :
    MetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1040
    where
  seed := "w1040-normalized-source-endpoint-localized-unit-to-w1039-endpoint-localized-unit-route"
  declarations :=
    ["endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040",
      "currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1040",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040",
      "currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1040",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1040",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1040",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1040",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1040",
      "currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "fullDataOfNormalizedSourceEndpointLocalizedUnitW1040",
      "directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1040",
      "boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1040",
      "normalizedSourceEndpointLocalizedUnitInputNamesW1040_count"]
  providerRepackagingResult :=
    "proved: W1040 constructs the W1039 W1003 endpoint-localized-unit\
      provider surface from W1004 normalized-source/endpoint-localized-unit\
      data and feeds W1039"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1040 inherits W1039/W1038/W1037/W1036/W1035/W1034/W1033/\
      W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/W1023/\
      W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/W1013/\
      W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/W1003/\
      W1002/W998 target surjective-compact recovery after W1004 constructs W1003"
  exactAtResult :=
    "proved: the W1040 W1004 normalized-source/endpoint-localized-unit\
      provider surface feeds W1039/W1038/W1037/W1036/W1035/W1034/\
      W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/W1025/W1024/\
      W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/W1015/W1014/\
      W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/W1005/W1004/\
      W1003/W1002/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := normalizedSourceEndpointLocalizedUnitInputNamesW1040
  productSuccessClaimed := false

theorem currentW1040NormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteStateW1040;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
