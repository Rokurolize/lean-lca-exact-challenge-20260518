import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W988 constructs the W987 full-data provider from the existing W982
localized-unit-choice surface.
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

/-- W988 constructs W984 target/closed-embedding closedness data from W982 fields. -/
def targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
    where
  targetNoUnivData := localizedUnitChoiceData.targetNoUnivData
  closedEmbeddingClosednessData :=
    localizedUnitChoiceData.closedEmbeddingClosednessData

/-- W988 constructs W949 endpoint-localized-unit data from W982 fields. -/
def endpointLocalizedUnitDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    EndpointStrictExactLocalizedUnitDataProviderW949
    where
  endpointStrictExact := localizedUnitChoiceData.endpointStrictExact
  localizedUnitData := localizedUnitChoiceData.localizedUnitData

/-- W988 constructs W950 normalized-source/endpoint-localized data from W982 fields. -/
def normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950
    where
  normalizedSourceTriangulationData :=
    localizedUnitChoiceData.normalizedSourceTriangulationData
  endpointLocalizedUnitData :=
    endpointLocalizedUnitDataOfLocalizedUnitChoiceW988
      localizedUnitChoiceData

/-- W988 constructs W986 target/closedness/normalized-source/endpoint data from W982 fields. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988
      localizedUnitChoiceData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
      localizedUnitChoiceData

/-- W988 constructs the W987 full-data provider from W982 localized-unit-choice data. -/
def fullDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
    where
  boundaryRelationData := localizedUnitChoiceData.boundaryRelationData
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988
      localizedUnitChoiceData

/- W988 feeds W987 after constructing the full-data provider from W982 fields. -/
noncomputable def w981LeavesOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

/- W988 exposes the W971 component-field split obtained through W987. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

/-- W988 reconstructs endpoint strict short exactness through W987. -/
noncomputable def endpointStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

/-- W988 derives unit mapping-cone algebraic exactness through W987. -/
noncomputable def unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

/-- W988 reconstructs unit mapping-cone strict short exactness through W987. -/
noncomputable def unitMappingConeStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

/-- W988 wraps the unit mapping-cone isomorphism through W987. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfLocalizedUnitChoiceW988 localizedUnitChoiceData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW988
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfFullDataW987
    (fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW988 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict-exact family",
    "W945 localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem localizedUnitChoiceInputNamesW988_count :
    localizedUnitChoiceInputNamesW988.length = 6 :=
  rfl

structure MetrizableLocalizedUnitChoiceRouteStateW988 : Type where
  seed : String
  declarations : List String
  fullDataConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceRouteStateW988 :
    MetrizableLocalizedUnitChoiceRouteStateW988
    where
  seed := "w988-localized-unit-choice-to-w987-full-data-route"
  declarations :=
    ["targetClosedEmbeddingClosednessDataOfLocalizedUnitChoiceW988",
      "endpointLocalizedUnitDataOfLocalizedUnitChoiceW988",
      "normalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfLocalizedUnitChoiceW988",
      "fullDataOfLocalizedUnitChoiceW988",
      "w981LeavesOfLocalizedUnitChoiceW988",
      "componentFieldsOfLocalizedUnitChoiceW988",
      "endpointStrictExactOfLocalizedUnitChoiceW988",
      "unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW988",
      "unitMappingConeStrictExactOfLocalizedUnitChoiceW988",
      "unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW988",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW988",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW988",
      "localizedUnitChoiceInputNamesW988_count"]
  fullDataConstructionResult :=
    "proved: W988 constructs the W987 full-data provider from W982\
      localized-unit-choice fields"
  exactAtResult :=
    "proved: the W988 W982 field surface feeds the W987/W986/W985/W984/W983/\
      W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW988
  productSuccessClaimed := false

theorem currentW988LocalizedUnitChoiceRoute_productSuccess :
    (let state := currentMetrizableLocalizedUnitChoiceRouteStateW988;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
