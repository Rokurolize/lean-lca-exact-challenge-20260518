import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataRoute

/-!
W981 replaces the W976 unit mapping-cone kernel/cokernel-top provider surface
by a unit mapping-cone model, strict short exactness, and chosen isomorphism.
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
W981 unit mapping-cone data: keep the model and chosen isomorphism, but replace
the four W976 kernel/cokernel-top fields by strict short exactness.
-/
structure UnitMappingConeStrictExactIsoDataProviderW981
    (localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975) :
    Type 2 where
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeStrictExact :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((unitMappingConeModel X).as.sc i)
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                localizedAdjunctionData).unit.app X)))) ≅
        unitMappingConeModel X)

/-- W981 constructs the W976 unit provider from strict short exactness. -/
def unitKernelCokernelTopIsoDataOfUnitStrictExactIsoW981
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData) :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      localizedAdjunctionData
    where
  unitMappingConeModel := unitData.unitMappingConeModel
  unitMappingConeClosedEmbedding := fun X i =>
    (unitData.unitMappingConeStrictExact X i).closed_inclusion
  unitMappingConeOpenMap := fun X i =>
    (unitData.unitMappingConeStrictExact X i).open_map
  unitMappingConeCokernelTop := fun X i =>
    MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
      (((unitData.unitMappingConeModel X).as.sc i).g)
      (unitData.unitMappingConeStrictExact X i).surjective
  unitMappingConeKernelEquality := fun X i =>
    (MetrizableLCA.algebraic_kernel_of_strict
      (unitData.unitMappingConeStrictExact X i)).2
  unitMappingConeIso := unitData.unitMappingConeIso

/--
W981 full-data provider: W980 endpoint strict exactness plus W981 unit
mapping-cone strict-exact/isomorphism data.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981 :
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
  unitStrictExactIsoData :
    UnitMappingConeStrictExactIsoDataProviderW981 localizedAdjunctionData

/-- W981 constructs the W980 full-data provider. -/
def fullDataOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetNoUnivData := fullData.targetNoUnivData
  closedEmbeddingClosednessData := fullData.closedEmbeddingClosednessData
  endpointStrictExact := fullData.endpointStrictExact
  localizedAdjunctionData := fullData.localizedAdjunctionData
  normalizedSourceTriangulationData :=
    fullData.normalizedSourceTriangulationData
  unitKernelCokernelTopIsoData :=
    unitKernelCokernelTopIsoDataOfUnitStrictExactIsoW981
      fullData.unitStrictExactIsoData

/- W981 feeds W980 after constructing the W976 unit provider. -/
def w980LeavesOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

/- W981 exposes the W971 component-field split obtained through W980. -/
def componentFieldsOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

/-- W981 reconstructs endpoint strict short exactness through W980. -/
def endpointStrictExactOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

/-- W981 derives unit mapping-cone algebraic exactness through W980. -/
def unitMappingConeAlgebraicExactOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

/-- W981 reconstructs unit mapping-cone strict short exactness through W980. -/
def unitMappingConeStrictExactOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

/-- W981 wraps the unit mapping-cone isomorphism through W980. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfUnitStrictExactIsoW981 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfUnitStrictExactIsoW981 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoW981
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointStrictExactW980
    (fullDataOfUnitStrictExactIsoW981 fullData)

def unitStrictExactIsoDataInputNamesW981 : List String :=
  ["unit mapping-cone model",
    "unit mapping-cone strict short-exact family",
    "unit mapping-cone chosen isomorphism"]

theorem unitStrictExactIsoDataInputNamesW981_count :
    unitStrictExactIsoDataInputNamesW981.length = 3 :=
  rfl

def endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict short-exact family",
    "W975 localized-adjunction data provider",
    "W948 normalized-source-triangulation data provider",
    "W981 unit mapping-cone strict-exact/isomorphism data provider"]

theorem endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count :
    endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981.length = 7 :=
  rfl

structure MetrizableEndpointUnitStrictExactLocalizedUnitFullDataRouteStateW981 :
    Type where
  seed : String
  declarations : List String
  unitConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointUnitStrictExactLocalizedUnitFullDataRouteStateW981 :
    MetrizableEndpointUnitStrictExactLocalizedUnitFullDataRouteStateW981
    where
  seed := "w981-endpoint-unit-strict-exact-localized-unit-full-data-route"
  declarations :=
    ["UnitMappingConeStrictExactIsoDataProviderW981",
      "unitKernelCokernelTopIsoDataOfUnitStrictExactIsoW981",
      "BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981",
      "fullDataOfUnitStrictExactIsoW981",
      "w980LeavesOfUnitStrictExactIsoW981",
      "componentFieldsOfUnitStrictExactIsoW981",
      "endpointStrictExactOfUnitStrictExactIsoW981",
      "unitMappingConeAlgebraicExactOfUnitStrictExactIsoW981",
      "unitMappingConeStrictExactOfUnitStrictExactIsoW981",
      "unitMappingConeIsoNonemptyOfUnitStrictExactIsoW981",
      "directBoundedLeftCalculusOfUnitStrictExactIsoW981",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoW981",
      "unitStrictExactIsoDataInputNamesW981_count",
      "endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count"]
  unitConstructionResult :=
    "proved: W981 constructs the W976 unit mapping-cone kernel/cokernel-top\
      isomorphism provider from model, strict short exactness, and a chosen\
      isomorphism"
  exactAtResult :=
    "proved: the W981 endpoint/unit-strict full-data surface feeds the W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981
  productSuccessClaimed := false

theorem currentW981EndpointUnitStrictExactLocalizedUnitFullDataRoute_productSuccess :
    (let state := currentMetrizableEndpointUnitStrictExactLocalizedUnitFullDataRouteStateW981;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
