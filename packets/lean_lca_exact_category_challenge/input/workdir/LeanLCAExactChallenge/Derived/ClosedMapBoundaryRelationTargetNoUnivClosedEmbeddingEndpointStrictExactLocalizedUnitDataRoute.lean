import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitFullDataToComponentFieldsRoute

/-!
W980 replaces the W974 endpoint kernel/cokernel-top provider in the W977
full-data surface by a single endpoint strict-short-exact family.
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
W980 full-data provider with the endpoint surface expressed as strict short
exactness rather than the four W974 endpoint kernel/cokernel-top fields.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedAdjunctionData :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  unitKernelCokernelTopIsoData :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      localizedAdjunctionData

/-- W980 constructs W974 endpoint data from endpoint strict short exactness. -/
def endpointKernelCokernelTopDataOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    EndpointKernelCokernelTopDataProviderW974
    where
  endpointClosedEmbedding := fun K i =>
    (fullData.endpointStrictExact K i).closed_inclusion
  endpointOpenMap := fun K i =>
    (fullData.endpointStrictExact K i).open_map
  endpointCokernelTop := fun K i =>
    MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
      (K.sc i).g (fullData.endpointStrictExact K i).surjective
  endpointKernelEquality := fun K i =>
    (MetrizableLCA.algebraic_kernel_of_strict
      (fullData.endpointStrictExact K i)).2

/-- W980 constructs the W977 full-data provider from endpoint strict exactness. -/
def fullDataOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetNoUnivData := fullData.targetNoUnivData
  closedEmbeddingClosednessData := fullData.closedEmbeddingClosednessData
  endpointKernelCokernelTopData :=
    endpointKernelCokernelTopDataOfEndpointStrictExactW980 fullData
  localizedAdjunctionData := fullData.localizedAdjunctionData
  normalizedSourceTriangulationData :=
    fullData.normalizedSourceTriangulationData
  unitKernelCokernelTopIsoData :=
    fullData.unitKernelCokernelTopIsoData

/- W980 feeds W979 after constructing the W977 full-data provider. -/
def w977LeavesOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

/- W980 exposes the W971 component-field split obtained through W979. -/
def componentFieldsOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

/-- W980 reconstructs endpoint strict short exactness through W979/W978. -/
def endpointStrictExactOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

/-- W980 derives unit mapping-cone algebraic exactness through W979/W978. -/
def unitMappingConeAlgebraicExactOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

/-- W980 reconstructs unit mapping-cone strict short exactness through W979/W978. -/
def unitMappingConeStrictExactOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

/-- W980 wraps the unit mapping-cone isomorphism through W979/W978. -/
@[reducible]
def unitMappingConeIsoNonemptyOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfEndpointStrictExactW980 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfEndpointStrictExactW980 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

theorem directBoundedLeftCalculusOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

noncomputable def boundedDerivedInfinityCategoryOfEndpointStrictExactW980
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfSplitFullDataW979
    (fullDataOfEndpointStrictExactW980 fullData)

def endpointStrictExactLocalizedUnitFullDataInputNamesW980 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict short-exact family",
    "W975 localized-adjunction data provider",
    "W948 normalized-source-triangulation data provider",
    "W976 unit mapping-cone kernel/cokernel-top isomorphism data provider"]

theorem endpointStrictExactLocalizedUnitFullDataInputNamesW980_count :
    endpointStrictExactLocalizedUnitFullDataInputNamesW980.length = 7 :=
  rfl

structure MetrizableEndpointStrictExactLocalizedUnitFullDataRouteStateW980 :
    Type where
  seed : String
  declarations : List String
  endpointConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointStrictExactLocalizedUnitFullDataRouteStateW980 :
    MetrizableEndpointStrictExactLocalizedUnitFullDataRouteStateW980
    where
  seed := "w980-endpoint-strict-exact-localized-unit-full-data-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980",
      "endpointKernelCokernelTopDataOfEndpointStrictExactW980",
      "fullDataOfEndpointStrictExactW980",
      "w977LeavesOfEndpointStrictExactW980",
      "componentFieldsOfEndpointStrictExactW980",
      "endpointStrictExactOfEndpointStrictExactW980",
      "unitMappingConeAlgebraicExactOfEndpointStrictExactW980",
      "unitMappingConeStrictExactOfEndpointStrictExactW980",
      "unitMappingConeIsoNonemptyOfEndpointStrictExactW980",
      "directBoundedLeftCalculusOfEndpointStrictExactW980",
      "boundedDerivedInfinityCategoryOfEndpointStrictExactW980",
      "endpointStrictExactLocalizedUnitFullDataInputNamesW980",
      "endpointStrictExactLocalizedUnitFullDataInputNamesW980_count"]
  endpointConstructionResult :=
    "proved: W980 constructs the W974 endpoint kernel/cokernel-top provider\
      from one endpoint strict short-exact family"
  exactAtResult :=
    "proved: the W980 endpoint-strict full-data surface feeds the W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/\
      W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := endpointStrictExactLocalizedUnitFullDataInputNamesW980
  productSuccessClaimed := false

theorem currentW980EndpointStrictExactLocalizedUnitFullDataRoute_productSuccess :
    (let state := currentMetrizableEndpointStrictExactLocalizedUnitFullDataRouteStateW980;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
