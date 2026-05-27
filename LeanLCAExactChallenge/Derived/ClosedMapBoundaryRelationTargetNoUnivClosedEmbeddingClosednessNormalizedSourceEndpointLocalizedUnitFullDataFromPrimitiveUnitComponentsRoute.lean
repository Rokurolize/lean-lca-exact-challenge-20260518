import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromUnitStrictExactIsoRoute

/-!
W990 opens W989's localized-adjunction and unit strict-exact/isomorphism
providers into explicit localized adjunction fields plus the W939 unit
component witness.
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
W990 primitive localized-unit surface: keep the W730/W944/W973 endpoint and
W948 fields while replacing W975/W981 opaque providers by a localized right
adjoint, its adjunction, and the W939 unit-component witness.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990 :
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
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948

/-- W990 builds the W975 localized-adjunction provider from explicit fields. -/
def localizedAdjunctionDataOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
    where
  boundedHomotopyLocalizedRightAdjoint :=
    primitiveData.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    primitiveData.boundedHomotopyLocalizedAdjunction

/--
W990 chooses W981's unit mapping-cone model, strict exactness, and isomorphism
from the W939 component witness.
-/
noncomputable def unitStrictExactIsoDataOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    UnitMappingConeStrictExactIsoDataProviderW981
      (localizedAdjunctionDataOfPrimitiveUnitComponentsW990 primitiveData)
    where
  unitMappingConeModel := fun X =>
    Classical.choose
      (primitiveData.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents
        X)
  unitMappingConeStrictExact := fun X i => by
    classical
    let hX :=
      Classical.choose_spec
        (primitiveData.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents
          X)
    exact
      { closed_inclusion := hX.1 i
        open_map := hX.2.1 i
        surjective := hX.2.2.1 i
        algebraic_exact := hX.2.2.2.1 i }
  unitMappingConeIso := fun X => by
    classical
    let hX :=
      Classical.choose_spec
        (primitiveData.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents
          X)
    exact Classical.choice hX.2.2.2.2

/-- W990 constructs the W981 full-data provider from primitive unit components. -/
noncomputable def unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981
    where
  boundaryRelationData := primitiveData.boundaryRelationData
  targetNoUnivData := primitiveData.targetNoUnivData
  closedEmbeddingClosednessData :=
    primitiveData.closedEmbeddingClosednessData
  endpointStrictExact := primitiveData.endpointStrictExact
  localizedAdjunctionData :=
    localizedAdjunctionDataOfPrimitiveUnitComponentsW990 primitiveData
  normalizedSourceTriangulationData :=
    primitiveData.normalizedSourceTriangulationData
  unitStrictExactIsoData :=
    unitStrictExactIsoDataOfPrimitiveUnitComponentsW990 primitiveData

/-- W990 constructs W987 full data through the W989 route. -/
noncomputable def fullDataOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/- W990 feeds W989 after constructing W981 data. -/
noncomputable def w981LeavesOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/- W990 exposes the W971 component-field split obtained through W989. -/
noncomputable def componentFieldsOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/-- W990 reconstructs endpoint strict short exactness through W989. -/
noncomputable def endpointStrictExactOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/-- W990 derives unit mapping-cone algebraic exactness through W989. -/
noncomputable def unitMappingConeAlgebraicExactOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/-- W990 reconstructs unit mapping-cone strict short exactness through W989. -/
noncomputable def unitMappingConeStrictExactOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

/-- W990 wraps the unit mapping-cone isomorphism through W989. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfPrimitiveUnitComponentsW990 primitiveData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

theorem directBoundedLeftCalculusOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

noncomputable def boundedDerivedInfinityCategoryOfPrimitiveUnitComponentsW990
    (primitiveData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitStrictExactIsoW989
    (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990 primitiveData)

def primitiveUnitComponentsInputNamesW990 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict-exact family",
    "bounded homotopy localized right adjoint",
    "bounded homotopy localized adjunction",
    "W939 unit mapping-cone component witness",
    "W948 normalized-source-triangulation data provider"]

theorem primitiveUnitComponentsInputNamesW990_count :
    primitiveUnitComponentsInputNamesW990.length = 8 :=
  rfl

structure MetrizablePrimitiveUnitComponentsRouteStateW990 : Type where
  seed : String
  declarations : List String
  primitiveUnitConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizablePrimitiveUnitComponentsRouteStateW990 :
    MetrizablePrimitiveUnitComponentsRouteStateW990
    where
  seed := "w990-primitive-unit-components-to-w989-unit-strict-exact-iso-route"
  declarations :=
    ["BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990",
      "localizedAdjunctionDataOfPrimitiveUnitComponentsW990",
      "unitStrictExactIsoDataOfPrimitiveUnitComponentsW990",
      "unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990",
      "fullDataOfPrimitiveUnitComponentsW990",
      "w981LeavesOfPrimitiveUnitComponentsW990",
      "componentFieldsOfPrimitiveUnitComponentsW990",
      "endpointStrictExactOfPrimitiveUnitComponentsW990",
      "unitMappingConeAlgebraicExactOfPrimitiveUnitComponentsW990",
      "unitMappingConeStrictExactOfPrimitiveUnitComponentsW990",
      "unitMappingConeIsoNonemptyOfPrimitiveUnitComponentsW990",
      "directBoundedLeftCalculusOfPrimitiveUnitComponentsW990",
      "boundedDerivedInfinityCategoryOfPrimitiveUnitComponentsW990",
      "primitiveUnitComponentsInputNamesW990_count"]
  primitiveUnitConstructionResult :=
    "proved: W990 constructs W975 localized-adjunction data and W981 unit\
      strict-exact/isomorphism data from explicit localized adjunction fields\
      plus the W939 unit-component witness"
  exactAtResult :=
    "proved: the W990 primitive-unit-component surface feeds the W989/W988/\
      W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := primitiveUnitComponentsInputNamesW990
  productSuccessClaimed := false

theorem currentW990PrimitiveUnitComponentsRoute_productSuccess :
    (let state := currentMetrizablePrimitiveUnitComponentsRouteStateW990;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
