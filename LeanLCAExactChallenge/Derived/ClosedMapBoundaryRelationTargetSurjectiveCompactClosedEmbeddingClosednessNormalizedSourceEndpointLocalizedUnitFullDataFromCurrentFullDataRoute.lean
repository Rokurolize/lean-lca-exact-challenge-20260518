import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoRoute

/-!
W999 replaces W998's remaining W987 branch-full-data input by the older W977
current full-data provider. The W977 provider already contains W944 target
no-univ data, W973 closed-embedding closedness data, W948 normalized-source
data, endpoint strict exactness through W977, and W976 unit mapping-cone data.
W999 repackages those fields into W987 and then feeds W998.
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

/-- W999 views a W977 current full-data provider as W977 leaves. -/
def leavesOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977
    where
  fullData := fullData

/--
W999 converts W977's W976 unit kernel/cokernel-top/isomorphism data into the
W981 strict-exact/isomorphism data surface.
-/
def unitStrictExactIsoDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfFullDataW977 fullData)
    where
  unitMappingConeModel :=
    unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
      (unitKernelCokernelTopIsoDataOfFullDataW977 fullData)
  unitMappingConeStrictExact := fun X i =>
    unitMappingConeStrictExactOfFullDataW977
      (leavesOfCurrentFullDataW999 fullData) X i
  unitMappingConeIso := fun X =>
    unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976
      (unitKernelCokernelTopIsoDataOfFullDataW977 fullData) X

/-- W999 constructs the W981 full-data surface from W977 current full data. -/
def unitStrictExactIsoFullDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981
    where
  boundaryRelationData := boundaryRelationDataOfFullDataW977 fullData
  targetNoUnivData := targetNoUnivDataOfFullDataW977 fullData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfFullDataW977 fullData
  endpointStrictExact :=
    endpointStrictExactOfFullDataW977
      (leavesOfCurrentFullDataW999 fullData)
  localizedAdjunctionData :=
    localizedAdjunctionDataOfFullDataW977 fullData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfFullDataW977 fullData
  unitStrictExactIsoData :=
    unitStrictExactIsoDataOfCurrentFullDataW999 fullData

/-- W999 constructs W945 localized-unit data from W977 via W989. -/
noncomputable def localizedUnitDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfCurrentFullDataW999 fullData)

/-- W999 packages W977 endpoint strict exactness with the recovered W945 data. -/
noncomputable def endpointLocalizedUnitDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    EndpointStrictExactLocalizedUnitDataProviderW949
    where
  endpointStrictExact :=
    endpointStrictExactOfFullDataW977
      (leavesOfCurrentFullDataW999 fullData)
  localizedUnitData :=
    localizedUnitDataOfCurrentFullDataW999 fullData

/-- W999 constructs the W950 normalized-source/endpoint-localized provider. -/
noncomputable def normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
    where
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfFullDataW977 fullData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfCurrentFullDataW999 fullData

/-- W999 constructs the W984 target/closed-embedding closedness data. -/
def targetClosedEmbeddingClosednessDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
    where
  targetNoUnivData := targetNoUnivDataOfFullDataW977 fullData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfFullDataW977 fullData

/-- W999 constructs the W986 target/closedness/normalized-source/endpoint data. -/
noncomputable def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfCurrentFullDataW999 fullData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999 fullData

/-- W999 constructs the W987 branch full-data provider from W977 current full data. -/
noncomputable def branchFullDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
    where
  boundaryRelationData := boundaryRelationDataOfFullDataW977 fullData
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999
      fullData

/-- W999 recovers W715 target surjective-compact data from W977 via W987/W998. -/
noncomputable def targetSurjectiveCompactDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 builds W997's branch-full-data surface from W977 current full data. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfCurrentFullDataW999 fullData
  branchFullData := branchFullDataOfCurrentFullDataW999 fullData

/-- W999 builds the W995 target-provider surface through W998. -/
noncomputable def targetProviderDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 builds the W994 normalized-source/endpoint route data through W998. -/
noncomputable def normalizedSourceEndpointDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 returns the constructed W987 branch full data through W998. -/
noncomputable def fullDataOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/- W999 exposes W981 leaves through the W998 route. -/
noncomputable def w981LeavesOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/- W999 exposes W971 component fields through the W998 route. -/
noncomputable def componentFieldsOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 reconstructs endpoint strict exactness through W998. -/
noncomputable def endpointStrictExactOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 derives unit mapping-cone algebraic exactness through W998. -/
noncomputable def unitMappingConeAlgebraicExactOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 reconstructs unit mapping-cone strict short exactness through W998. -/
noncomputable def unitMappingConeStrictExactOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

/-- W999 wraps the unit mapping-cone isomorphism through W998. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfCurrentFullDataW999 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfCurrentFullDataW999 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

theorem directBoundedLeftCalculusOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

noncomputable def boundedDerivedInfinityCategoryOfCurrentFullDataW999
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW998
    (branchFullDataOfCurrentFullDataW999 fullData)

def currentFullDataInputNamesW999 : List String :=
  ["W977 current full-data provider: W730 boundary/relation data, W944 target\
      no-univ data, W973 closed-embedding closedness data, W974 endpoint\
      kernel/cokernel-top data, W975 localized-adjunction data, W948\
      normalized-source-triangulation data, and W976 unit mapping-cone\
      kernel/cokernel-top iso data"]

theorem currentFullDataInputNamesW999_count :
    currentFullDataInputNamesW999.length = 1 :=
  rfl

structure MetrizableCurrentFullDataRouteStateW999 : Type where
  seed : String
  declarations : List String
  currentFullDataRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCurrentFullDataRouteStateW999 :
    MetrizableCurrentFullDataRouteStateW999
    where
  seed := "w999-current-full-data-to-branch-full-data-target-compact-route"
  declarations :=
    ["leavesOfCurrentFullDataW999",
      "unitStrictExactIsoDataOfCurrentFullDataW999",
      "unitStrictExactIsoFullDataOfCurrentFullDataW999",
      "localizedUnitDataOfCurrentFullDataW999",
      "endpointLocalizedUnitDataOfCurrentFullDataW999",
      "normalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999",
      "targetClosedEmbeddingClosednessDataOfCurrentFullDataW999",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfCurrentFullDataW999",
      "branchFullDataOfCurrentFullDataW999",
      "targetSurjectiveCompactDataOfCurrentFullDataW999",
      "targetSurjectiveCompactBranchFullDataOfCurrentFullDataW999",
      "targetProviderDataOfCurrentFullDataW999",
      "normalizedSourceEndpointDataOfCurrentFullDataW999",
      "fullDataOfCurrentFullDataW999",
      "w981LeavesOfCurrentFullDataW999",
      "componentFieldsOfCurrentFullDataW999",
      "endpointStrictExactOfCurrentFullDataW999",
      "unitMappingConeAlgebraicExactOfCurrentFullDataW999",
      "unitMappingConeStrictExactOfCurrentFullDataW999",
      "unitMappingConeIsoNonemptyOfCurrentFullDataW999",
      "directBoundedLeftCalculusOfCurrentFullDataW999",
      "boundedDerivedInfinityCategoryOfCurrentFullDataW999",
      "currentFullDataInputNamesW999_count"]
  currentFullDataRepackagingResult :=
    "proved: W999 constructs W987 branch full data from W977 current full\
      data by recovering W981 strict-exact/isomorphism data from W976,\
      constructing W945 localized-unit data through W989, and packaging W950,\
      W984, and W986"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W999 feeds W998 after the W977-to-W987 repackaging, so W715\
      target surjective-compact data is recovered from W977's W944 target\
      no-univ provider"
  exactAtResult :=
    "proved: the W999 W977 current-full-data surface feeds the W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := currentFullDataInputNamesW999
  productSuccessClaimed := false

theorem currentW999CurrentFullDataRoute_productSuccess :
    (let state := currentMetrizableCurrentFullDataRouteStateW999;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
