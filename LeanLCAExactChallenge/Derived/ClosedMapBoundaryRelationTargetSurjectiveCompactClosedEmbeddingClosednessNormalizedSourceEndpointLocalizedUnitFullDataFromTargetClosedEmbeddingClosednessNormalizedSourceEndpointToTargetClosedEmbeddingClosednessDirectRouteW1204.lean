import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessToNormalizedSourceEndpointLocalizedUnitDirectRouteW1203
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessNormalizedSourceEndpointDirectRoute

/-!
W1204 replaces W1203's W1014 target/closed-embedding-closedness input surface
by the existing W1015 target/closed-embedding-closedness/normalized-source
endpoint input surface. W1015 already constructs W1005, and W1204 feeds that
provider into W1203.
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

/-- W1204 constructs the W1005 target/closed-embedding-closedness surface from W1006 data. -/
def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1015
    targetClosedEmbeddingClosednessNormalizedSourceEndpointData

/-- W1204 constructs the W1004 normalized-source/endpoint-localized-unit surface from W1006 through W1203. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W1003 endpoint-localized-unit surface from W1006 through W1203. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W982 localized-unit-choice surface from W1006 through W1203. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W981 provider surface from W1006 through W1203. -/
noncomputable def unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W971 component-field surface from W1006 through W1203. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W1008 current-full-data surface from W1006 through W1203. -/
noncomputable def currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs the W1007 branch-full-data surface from W1006 through W1203. -/
noncomputable def branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface through W1203. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 returns the rebuilt W1005 target/closed-embedding-closedness surface through W1203. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1203. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1003 endpoint-localized-unit surface after routing through W1203. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W982 localized-unit-choice surface after routing through W1203. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W981 surface after routing through W1203. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W971 component fields after routing through W1203. -/
noncomputable def componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1008 current-full-data surface after routing through W1203. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1007 branch-full-data surface after routing through W1203. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1006 target/closedness/normalized-source/endpoint surface after routing through W1203. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 returns the nested rebuilt W1005 target/closed-embedding-closedness surface through W1203. -/
noncomputable def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the twice-rebuilt W1004 normalized-source/endpoint-localized-unit surface through W1203. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the nested rebuilt W1003 endpoint-localized-unit surface through W1203. -/
noncomputable def endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the twice-rebuilt W982 localized-unit-choice surface after routing through W1203. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the twice-rebuilt W981 surface after routing through W1203. -/
noncomputable def unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the twice-rebuilt W971 component fields after routing through W1203. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1008 current-full-data surface after the nested W1203 pass. -/
noncomputable def currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the rebuilt W1007 branch-full-data surface after the nested W1203 pass. -/
noncomputable def branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the triply rebuilt W982 localized-unit-choice surface after routing through W1203. -/
noncomputable def localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 exposes the triply rebuilt W971 component fields after routing through W1203. -/
noncomputable def componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs W977 current full data from W1006 through W1203. -/
noncomputable def currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  currentFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 constructs W987 branch full data from W1006 through W1203. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  branchFullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 recovers W715 target surjective-compact data from W1006 through W1203. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

/-- W1204 returns the constructed W987 branch full data from W1006 through W1203. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  fullDataOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
    (targetClosedEmbeddingClosednessNormalizedSourceEndpointData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1203
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204
      targetClosedEmbeddingClosednessNormalizedSourceEndpointData)

def targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1204 : List String :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1015

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1204_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1204.length =
      2 :=
  targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1015_count

structure MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1204 :
    Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1204 :
    MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1204
    where
  seed := "w1204-target-closed-embedding-closedness-normalized-source-endpoint-to-w1203-target-closed-embedding-closedness-route"
  declarations :=
    ["targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "unitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "currentFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "branchFullDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "componentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "currentFullDataProviderOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "branchFullDataProviderOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfNormalizedSourceEndpointLocalizedUnitOfNormalizedSourceEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "endpointLocalizedUnitDataProviderOfEndpointLocalizedUnitOfEndpointLocalizedUnitOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "unitStrictExactIsoDataOfUnitStrictExactIsoDataOfUnitStrictExactIsoDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "currentFullDataProviderOfCurrentFullDataOfCurrentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "branchFullDataProviderOfBranchFullDataOfBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "localizedUnitChoiceDataOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfLocalizedUnitChoiceOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "componentFieldsOfComponentFieldsOfComponentFieldsOfComponentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "currentFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1204",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1204_count"]
  providerRepackagingResult :=
    "proved: W1204 constructs the W1203 W1014 target/closed-embedding\
      closedness input surface from W1015 target/closedness/normalized-source/\
      endpoint data and feeds W1203"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1204 inherits W1203/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/\
      W1098/W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/\
      W1088/W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/\
      W1078/W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/\
      W1068/W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/\
      W1058/W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/\
      W1048/W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/\
      W1038/W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/\
      W1028/W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/\
      W1018/W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/\
      W1008/W1007/W1006/W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W1015 constructs W1005"
  exactAtResult :=
    "proved: the W1204 W1015 target/closedness/normalized-source/endpoint\
      input surface feeds W1203/W1112/W1111/W1110/W1109/W1108/W1107/W1106/W1105/W1104/W1103/W1102/W1101/W1100/W1099/W1098/\
      W1097/W1096/W1095/W1094/W1093/W1092/W1091/W1090/W1089/W1088/\
      W1087/W1086/W1085/W1084/W1083/W1082/W1081/W1080/W1079/W1078/\
      W1077/W1076/W1075/W1074/W1073/W1072/W1071/W1070/W1069/W1068/\
      W1067/W1066/W1065/W1064/W1063/W1062/W1061/W1060/W1059/W1058/\
      W1057/W1056/W1055/W1054/W1053/W1052/W1051/W1050/W1049/W1048/\
      W1047/W1046/W1045/W1044/W1043/W1042/W1041/W1040/W1039/W1038/\
      W1037/W1036/W1035/W1034/W1033/W1032/W1031/W1030/W1029/W1028/\
      W1027/W1026/W1025/W1024/W1023/W1022/W1021/W1020/W1019/W1018/\
      W1017/W1016/W1015/W1014/W1013/W1012/W1011/W1010/W1009/W1008/\
      W1007/W1006/W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/\
      W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/\
      W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1204
  productSuccessClaimed := false

theorem currentW1204TargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointToTargetClosedEmbeddingClosednessDirectRouteStateW1204;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
