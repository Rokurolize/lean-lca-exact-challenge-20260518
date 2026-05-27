import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRoute

/-!
W977 feeds the W976 unit-mapping-cone-data route while replacing the remaining
seven provider leaves by one current full-data provider.
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

/--
W977 full-data provider: package the seven W976 leaves into one current
provider without claiming that any of those providers have been constructed.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointKernelCokernelTopData :
    EndpointKernelCokernelTopDataProviderW974
  localizedAdjunctionData :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  unitKernelCokernelTopIsoData :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      localizedAdjunctionData

/-- W977 projects W730 boundary/relation data. -/
def boundaryRelationDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  fullData.boundaryRelationData

/-- W977 projects W944 target no-univ data. -/
def targetNoUnivDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  fullData.targetNoUnivData

/-- W977 projects W973 closed-embedding closedness data. -/
def closedEmbeddingClosednessDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  fullData.closedEmbeddingClosednessData

/-- W977 projects W974 endpoint kernel/cokernel-top data. -/
def endpointKernelCokernelTopDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    EndpointKernelCokernelTopDataProviderW974 :=
  fullData.endpointKernelCokernelTopData

/-- W977 projects W975 localized-adjunction data. -/
def localizedAdjunctionDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975 :=
  fullData.localizedAdjunctionData

/-- W977 projects W948 normalized-source-triangulation data. -/
def normalizedSourceTriangulationDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  fullData.normalizedSourceTriangulationData

/-- W977 projects W976 unit mapping-cone kernel/cokernel-top iso data. -/
def unitKernelCokernelTopIsoDataOfFullDataW977
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      (localizedAdjunctionDataOfFullDataW977 fullData) :=
  fullData.unitKernelCokernelTopIsoData

/--
W977 preserves the W976 field surface while replacing all remaining provider
leaves by one current full-data provider.
-/
structure MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :
    Type 2 where
  fullData :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977

/- W977 builds the W976 leaves consumed by the unit-data route. -/
def w976LeavesOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976
    where
  boundaryRelationData :=
    boundaryRelationDataOfFullDataW977 leaves.fullData
  targetNoUnivData :=
    targetNoUnivDataOfFullDataW977 leaves.fullData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfFullDataW977 leaves.fullData
  endpointKernelCokernelTopData :=
    endpointKernelCokernelTopDataOfFullDataW977 leaves.fullData
  localizedAdjunctionData :=
    localizedAdjunctionDataOfFullDataW977 leaves.fullData
  normalizedSourceTriangulationData :=
    normalizedSourceTriangulationDataOfFullDataW977 leaves.fullData
  unitKernelCokernelTopIsoData :=
    unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData

/-- W977 reconstructs endpoint strict short exactness through W976. -/
def endpointStrictExactOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfUnitKernelCokernelTopIsoDataW976
    (w976LeavesOfFullDataW977 leaves)

/-- W977 derives unit mapping-cone algebraic exactness through W976. -/
def unitMappingConeAlgebraicExactOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
        (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData)) X).as.sc i).X₂),
        (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
          (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData)) X).as.sc i).g x₂ = 0 →
          ∃ x₁ : (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
            (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData)) X).as.sc i).X₁,
            (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
              (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData)) X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfUnitKernelCokernelTopIsoDataW976
    (w976LeavesOfFullDataW977 leaves)

/-- W977 reconstructs unit mapping-cone strict short exactness through W976. -/
def unitMappingConeStrictExactOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
          (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData)) X).as.sc i) :=
  unitMappingConeStrictExactOfUnitKernelCokernelTopIsoDataW976
    (w976LeavesOfFullDataW977 leaves)

/-- W977 wraps the chosen unit mapping-cone isomorphism through W976. -/
@[reducible]
def unitMappingConeIsoNonemptyOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                  (localizedAdjunctionDataOfFullDataW977 leaves.fullData)).unit.app X)))) ≅
          unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
            (unitKernelCokernelTopIsoDataOfFullDataW977 leaves.fullData) X) :=
  unitMappingConeIsoNonemptyOfUnitKernelCokernelTopIsoDataW976
    (w976LeavesOfFullDataW977 leaves)

theorem directBoundedLeftCalculusOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
    (w976LeavesOfFullDataW977 leaves)

noncomputable def boundedDerivedInfinityCategoryOfFullDataW977
    (leaves :
      MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
    (w976LeavesOfFullDataW977 leaves)

/--
W977 records the W976 surface with all seven remaining provider leaves
consolidated into one current full-data provider.
-/
def closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977 :
    List String :=
  ["W977 full data provider: W730 boundary/relation data, W944 target no-univ\
      data, W973 closed-embedding closedness data, W974 endpoint\
      kernel/cokernel-top data, W975 localized-adjunction data, W948\
      normalized-source-triangulation data, and W976 unit mapping-cone\
      kernel/cokernel-top iso data"]

theorem closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977_count :
    closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977.length =
      1 :=
  rfl

/-- Current checked W977 state. -/
structure MetrizableClosedEmbeddingEndpointLocalizedUnitFullDataRouteStateW977 :
    Type where
  seed : String
  declarations : List String
  fullDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingEndpointLocalizedUnitFullDataRouteStateW977 :
    MetrizableClosedEmbeddingEndpointLocalizedUnitFullDataRouteStateW977
    where
  seed :=
    "w977-closed-embedding-endpoint-localized-unit-full-data-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977",
      "boundaryRelationDataOfFullDataW977",
      "targetNoUnivDataOfFullDataW977",
      "closedEmbeddingClosednessDataOfFullDataW977",
      "endpointKernelCokernelTopDataOfFullDataW977",
      "localizedAdjunctionDataOfFullDataW977",
      "normalizedSourceTriangulationDataOfFullDataW977",
      "unitKernelCokernelTopIsoDataOfFullDataW977",
      "MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977",
      "w976LeavesOfFullDataW977",
      "endpointStrictExactOfFullDataW977",
      "unitMappingConeAlgebraicExactOfFullDataW977",
      "unitMappingConeStrictExactOfFullDataW977",
      "unitMappingConeIsoNonemptyOfFullDataW977",
      "directBoundedLeftCalculusOfFullDataW977",
      "boundedDerivedInfinityCategoryOfFullDataW977",
      "closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977",
      "closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977_count"]
  fullDataResult :=
    "proved: W977 projects one current full-data provider into the seven\
      provider leaves consumed by W976"
  exactAtResult :=
    "proved: the W977 full-data provider feeds the W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["W976 boundary/relation, target no-univ, closed-embedding closedness,\
      endpoint kernel/cokernel-top, localized-adjunction,\
      normalized-source-triangulation, and unit mapping-cone data provider\
      leaves replaced by W977 current full-data provider"]
  remainingInputs :=
    closedEmbeddingEndpointLocalizedUnitFullDataInputNamesW977
  productSuccessClaimed := false

theorem currentW977ClosedEmbeddingEndpointLocalizedUnitFullDataRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingEndpointLocalizedUnitFullDataRouteStateW977;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
