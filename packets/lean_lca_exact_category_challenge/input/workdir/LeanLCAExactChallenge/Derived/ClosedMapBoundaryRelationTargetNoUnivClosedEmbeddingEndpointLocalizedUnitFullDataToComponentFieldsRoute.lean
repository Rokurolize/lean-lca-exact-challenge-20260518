import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataNormalizedSourceTriangulationDataClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRoute

/-!
W979 splits the W977 full-data provider back into the W971 component-field
surface, then feeds the W978 component-fields-to-full-data route.
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

/- W979 splits the W977 provider into the W971 component-field record. -/
def componentFieldsOfFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  let targetData := targetNoUnivDataOfFullDataW977 fullData
  let closednessData := closedEmbeddingClosednessDataOfFullDataW977 fullData
  let endpointData := endpointKernelCokernelTopDataOfFullDataW977 fullData
  let localizedAdjunctionData := localizedAdjunctionDataOfFullDataW977 fullData
  let unitData := unitKernelCokernelTopIsoDataOfFullDataW977 fullData
  { boundaryRelationData :=
      boundaryRelationDataOfFullDataW977 fullData
    targetDifferenceSurjectiveForTargetProvider :=
      targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944 targetData
    targetCodomainCompactNoUnivMembershipProvider :=
      targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944
        targetData
    globalClosedEmbeddingComponents :=
      globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        closednessData
    mappedCokernelClosedEmbeddingProvider :=
      mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        closednessData
    normalizedSourceTriangulationData :=
      normalizedSourceTriangulationDataOfFullDataW977 fullData
    endpointClosedEmbedding :=
      endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974
        endpointData
    endpointOpenMap :=
      endpointOpenMapOfEndpointKernelCokernelTopDataW974 endpointData
    endpointCokernelTop :=
      endpointCokernelTopOfEndpointKernelCokernelTopDataW974 endpointData
    endpointKernelEquality :=
      endpointKernelEqualityOfEndpointKernelCokernelTopDataW974 endpointData
    boundedHomotopyLocalizedRightAdjoint :=
      boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
        localizedAdjunctionData
    boundedHomotopyLocalizedAdjunction :=
      boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
        localizedAdjunctionData
    unitMappingConeModel :=
      unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData
    unitMappingConeClosedEmbedding :=
      unitMappingConeClosedEmbeddingOfUnitKernelCokernelTopIsoDataW976
        unitData
    unitMappingConeOpenMap :=
      unitMappingConeOpenMapOfUnitKernelCokernelTopIsoDataW976 unitData
    unitMappingConeCokernelTop :=
      unitMappingConeCokernelTopOfUnitKernelCokernelTopIsoDataW976
        unitData
    unitMappingConeKernelEquality :=
      unitMappingConeKernelEqualityOfUnitKernelCokernelTopIsoDataW976
        unitData
    unitMappingConeIso :=
      unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976 unitData }

/- W979 rebuilds W977 data from its split W971 component fields via W978. -/
def fullDataFromSplitComponentFieldsW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  fullDataOfComponentFieldsW978 (componentFieldsOfFullDataW979 fullData)

/- W979 builds W977 leaves through the split-and-rebuild path. -/
def w977LeavesOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977
    where
  fullData := fullDataFromSplitComponentFieldsW979 fullData

/-- W979 reconstructs endpoint strict short exactness through W978. -/
def endpointStrictExactOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

/-- W979 derives unit mapping-cone algebraic exactness through W978. -/
def unitMappingConeAlgebraicExactOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : (((componentFieldsOfFullDataW979 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfFullDataW979 fullData).unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : (((componentFieldsOfFullDataW979 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfFullDataW979 fullData).unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

/-- W979 reconstructs unit mapping-cone strict short exactness through W978. -/
def unitMappingConeStrictExactOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfFullDataW979 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

/-- W979 wraps the split full-data unit mapping-cone isomorphism through W978. -/
@[reducible]
def unitMappingConeIsoNonemptyOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfFullDataW979 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfFullDataW979 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

theorem directBoundedLeftCalculusOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

noncomputable def boundedDerivedInfinityCategoryOfSplitFullDataW979
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW978
    (componentFieldsOfFullDataW979 fullData)

def fullDataToComponentFieldsInputNamesW979 : List String :=
  ["W977 full-data provider split into W971 component fields and rebuilt by\
      the W978 route"]

theorem fullDataToComponentFieldsInputNamesW979_count :
    fullDataToComponentFieldsInputNamesW979.length = 1 :=
  rfl

structure MetrizableFullDataToComponentFieldsRouteStateW979 : Type where
  seed : String
  declarations : List String
  splitResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableFullDataToComponentFieldsRouteStateW979 :
    MetrizableFullDataToComponentFieldsRouteStateW979
    where
  seed := "w979-full-data-to-component-fields-route"
  declarations :=
    ["componentFieldsOfFullDataW979",
      "fullDataFromSplitComponentFieldsW979",
      "w977LeavesOfSplitFullDataW979",
      "endpointStrictExactOfSplitFullDataW979",
      "unitMappingConeAlgebraicExactOfSplitFullDataW979",
      "unitMappingConeStrictExactOfSplitFullDataW979",
      "unitMappingConeIsoNonemptyOfSplitFullDataW979",
      "directBoundedLeftCalculusOfSplitFullDataW979",
      "boundedDerivedInfinityCategoryOfSplitFullDataW979",
      "fullDataToComponentFieldsInputNamesW979",
      "fullDataToComponentFieldsInputNamesW979_count"]
  splitResult :=
    "proved: W979 splits the W977 full-data provider into the concrete W971\
      component-field record and rebuilds W977 data through W978"
  exactAtResult :=
    "proved: the W979 split full-data surface feeds the W978/W977/W976/W975/\
      W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/\
      W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := fullDataToComponentFieldsInputNamesW979
  productSuccessClaimed := false

theorem currentW979FullDataToComponentFieldsRoute_productSuccess :
    (let state := currentMetrizableFullDataToComponentFieldsRouteStateW979;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
