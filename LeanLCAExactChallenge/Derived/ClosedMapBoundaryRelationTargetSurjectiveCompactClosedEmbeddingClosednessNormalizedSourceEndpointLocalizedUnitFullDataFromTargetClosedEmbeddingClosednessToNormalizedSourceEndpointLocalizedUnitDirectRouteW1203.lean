import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteW1202
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessDirectRoute

/-!
W1203 replaces W1202's W1013 normalized-source/endpoint-localized-unit input
surface by the existing W1014 target/closed-embedding-closedness input surface.
W1014 already constructs W1004, and W1203 feeds that provider into W1202.
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

/-- W1203 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
    targetClosedEmbeddingClosednessData

/-- W1203 constructs the W1003 endpoint-localized-unit surface from W1005 through W1202. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W982 localized-unit-choice surface from W1005 through W1202. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W981 provider surface from W1005 through W1202. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W971 component-field surface from W1005 through W1202. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W1008 current-full-data surface from W1005 through W1202. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W1007 branch-full-data surface from W1005 through W1202. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1005 through W1202. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1202. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1202. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1202. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W982 localized-unit-choice surface after routing through W1202. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W981 surface after routing through W1202. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W971 component fields after routing through W1202. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1008 current-full-data surface after routing through W1202. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1007 branch-full-data surface after routing through W1202. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1202. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1202. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1202. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1202. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1202. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the twice-rebuilt W981 surface after routing through W1202. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the twice-rebuilt W971 component fields after routing through W1202. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1008 current-full-data surface after the nested W1202 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the rebuilt W1007 branch-full-data surface after the nested W1202 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1202. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 exposes the triply rebuilt W971 component fields after routing through W1202. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs W977 current full data from W1005 through W1202. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 constructs W987 branch full data from W1005 through W1202. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 recovers W715 target surjective-compact data from W1005 through W1202. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

/-- W1203 returns the constructed W987 branch full data from W1005 through W1202. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1202
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1203 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1014

theorem targetClosedEmbeddingClosednessInputNamesW1203_count :
    targetClosedEmbeddingClosednessInputNamesW1203.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1014_count

structure MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1203 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1203 :
    MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1203
    where
  seed := "w1203-target-closed-embedding-closedness-to-w1202-normalized-source-endpoint-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1203",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1203",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1203",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1203",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1203",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1203",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1203",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1203",
      "fullDataOfTargetClosedEmbeddingClosednessW1203",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1203",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1203",
      "targetClosedEmbeddingClosednessInputNamesW1203_count"]
  providerRepackagingResult :=
    "proved: W1203 constructs the W1202 W1013 normalized-source/endpoint\
      localized-unit input surface from W1014 target/closed-embedding\
      closedness data and feeds W1202"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1203 inherits W1202/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/\
      W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/\
      W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/\
      W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/\
      W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/\
      W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/\
      W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/\
      W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/\
      W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/\
      W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/\
      W1006/W1005/W1004/W1003/W1002/W998 target surjective-compact\
      recovery after W1014 constructs W1004"
  exactAtResult :=
    "proved: the W1203 W1014 target/closed-embedding-closedness input\
      surface feeds W1202/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
      W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/W1087/W1086/\
      W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/W1077/W1076/\
      W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/W1067/W1066/\
      W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/W1057/W1056/\
      W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/W1047/W1046/\
      W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/W1037/W1036/\
      W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/W1027/W1026/\
      W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/W1017/W1016/\
      W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/W1007/W1006/\
      W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1203
  productSuccessClaimed := false

theorem currentW1203TargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1203;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
