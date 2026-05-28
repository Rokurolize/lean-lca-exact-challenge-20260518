import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromNormalizedSourceEndpointLocalizedUnitToEndpointLocalizedUnitDirectRouteW1166
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessDirectRoute

/-!
W1167 replaces W1166's W1013 normalized-source/endpoint-localized-unit input
surface by the existing W1014 target/closed-embedding-closedness input surface.
W1014 already constructs W1004, and W1167 feeds that provider into W1166.
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

/-- W1167 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1005 data. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1014
    targetClosedEmbeddingClosednessData

/-- W1167 constructs the W1003 endpoint-localized-unit surface from W1005 through W1166. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W982 localized-unit-choice surface from W1005 through W1166. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W981 provider surface from W1005 through W1166. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W971 component-field surface from W1005 through W1166. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W1008 current-full-data surface from W1005 through W1166. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W1007 branch-full-data surface from W1005 through W1166. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs the W1006 target/closedness/normalized-source/endpoint surface from W1005 through W1166. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1166. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1166. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1166. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W982 localized-unit-choice surface after routing through W1166. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W981 surface after routing through W1166. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W971 component fields after routing through W1166. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1008 current-full-data surface after routing through W1166. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1007 branch-full-data surface after routing through W1166. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1166. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1166. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005 :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1166. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1166. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1166. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the twice-rebuilt W981 surface after routing through W1166. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the twice-rebuilt W971 component fields after routing through W1166. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1008 current-full-data surface after the nested W1166 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitCurrentFullDataProviderW1008 :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the rebuilt W1007 branch-full-data surface after the nested W1166 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007 :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1166. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 exposes the triply rebuilt W971 component fields after routing through W1166. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs W977 current full data from W1005 through W1166. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 constructs W987 branch full data from W1005 through W1166. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 recovers W715 target surjective-compact data from W1005 through W1166. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

/-- W1167 returns the constructed W987 branch full data from W1005 through W1166. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1167
    (targetClosedEmbeddingClosednessData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW1166
    (normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167
      targetClosedEmbeddingClosednessData)

def targetClosedEmbeddingClosednessInputNamesW1167 : List String :=
  targetClosedEmbeddingClosednessInputNamesW1014

theorem targetClosedEmbeddingClosednessInputNamesW1167_count :
    targetClosedEmbeddingClosednessInputNamesW1167.length = 3 :=
  targetClosedEmbeddingClosednessInputNamesW1014_count

structure MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1167 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1167 :
    MetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1167
    where
  seed := "w1167-target-closed-embedding-closedness-to-w1166-normalized-source-endpoint-route"
  declarations :=
    ["normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1167",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167",
      "componentFieldsOfTargetClosedEmbeddingClosednessW1167",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1167",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1167",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1167",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1167",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1167",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1167",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1167",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1167",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1167",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1167",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1167",
      "currentFullDataOfTargetClosedEmbeddingClosednessW1167",
      "branchFullDataOfTargetClosedEmbeddingClosednessW1167",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1167",
      "fullDataOfTargetClosedEmbeddingClosednessW1167",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1167",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1167",
      "targetClosedEmbeddingClosednessInputNamesW1167_count"]
  providerRepackagingResult :=
    "proved: W1167 constructs the W1166 W1013 normalized-source/endpoint\
      localized-unit input surface from W1014 target/closed-embedding\
      closedness data and feeds W1166"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1167 inherits W1166/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/\
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
    "proved: the W1167 W1014 target/closed-embedding-closedness input\
      surface feeds W1166/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/W1097/W1096/\
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
  remainingInputs := targetClosedEmbeddingClosednessInputNamesW1167
  productSuccessClaimed := false

theorem currentW1167TargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteStateW1167;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
