import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitFullDataRoute

/-!
W978 feeds the W977 full-data route by constructing its full-data provider from
the W971 boundary/relation, normalized-source, endpoint, localized-adjunction,
and unit component field surface.
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

/-- W978 constructs W944 target no-univ data from W971 split target fields. -/
def targetNoUnivDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  fun Y =>
    ⟨leaves.targetDifferenceSurjectiveForTargetProvider Y,
      leaves.targetCodomainCompactNoUnivMembershipProvider Y⟩

/-- W978 constructs W973 closed-embedding closedness data from W971 fields. -/
def closedEmbeddingClosednessDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ClosedEmbeddingClosednessDataProviderW973
    where
  globalClosedEmbeddingComponents := leaves.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    leaves.mappedCokernelClosedEmbeddingProvider

/-- W978 constructs W974 endpoint kernel/cokernel-top data from W971 fields. -/
def endpointKernelCokernelTopDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    EndpointKernelCokernelTopDataProviderW974
    where
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointCokernelTop := leaves.endpointCokernelTop
  endpointKernelEquality := leaves.endpointKernelEquality

/-- W978 constructs W975 localized-adjunction data from W971 fields. -/
def localizedAdjunctionDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
    where
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction

/--
W978 constructs W976 unit mapping-cone kernel/cokernel-top iso data from W971
unit component fields, relative to the W978 localized-adjunction data.
-/
def unitKernelCokernelTopIsoDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      (localizedAdjunctionDataOfComponentFieldsW978 leaves)
    where
  unitMappingConeModel := leaves.unitMappingConeModel
  unitMappingConeClosedEmbedding := leaves.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := leaves.unitMappingConeOpenMap
  unitMappingConeCokernelTop := leaves.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := leaves.unitMappingConeKernelEquality
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W978 constructs the W977 current full-data provider from W971 fields. -/
def fullDataOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfComponentFieldsW978 leaves
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfComponentFieldsW978 leaves
  endpointKernelCokernelTopData :=
    endpointKernelCokernelTopDataOfComponentFieldsW978 leaves
  localizedAdjunctionData :=
    localizedAdjunctionDataOfComponentFieldsW978 leaves
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
  unitKernelCokernelTopIsoData :=
    unitKernelCokernelTopIsoDataOfComponentFieldsW978 leaves

/- W978 builds the W977 leaves consumed by the full-data route. -/
def w977LeavesOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977
    where
  fullData := fullDataOfComponentFieldsW978 leaves

/-- W978 reconstructs endpoint strict short exactness through W977. -/
def endpointStrictExactOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

/-- W978 derives unit mapping-cone algebraic exactness through W977. -/
def unitMappingConeAlgebraicExactOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

/-- W978 reconstructs unit mapping-cone strict short exactness through W977. -/
def unitMappingConeStrictExactOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

/-- W978 wraps the chosen unit mapping-cone isomorphism through W977. -/
@[reducible]
def unitMappingConeIsoNonemptyOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

theorem directBoundedLeftCalculusOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW978
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfFullDataW977
    (w977LeavesOfComponentFieldsW978 leaves)

/--
W978 records the W977 full-data provider constructed from the W971 component
field surface.
-/
def closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978 :
    List String :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971

theorem closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978_count :
    closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978.length =
      18 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971_count

/-- Current checked W978 state. -/
structure MetrizableClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRouteStateW978 :
    Type where
  seed : String
  declarations : List String
  fullDataConstructionResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRouteStateW978 :
    MetrizableClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRouteStateW978
    where
  seed :=
    "w978-full-data-from-w971-component-fields-route"
  declarations :=
    ["targetNoUnivDataOfComponentFieldsW978",
      "closedEmbeddingClosednessDataOfComponentFieldsW978",
      "endpointKernelCokernelTopDataOfComponentFieldsW978",
      "localizedAdjunctionDataOfComponentFieldsW978",
      "unitKernelCokernelTopIsoDataOfComponentFieldsW978",
      "fullDataOfComponentFieldsW978",
      "w977LeavesOfComponentFieldsW978",
      "endpointStrictExactOfComponentFieldsW978",
      "unitMappingConeAlgebraicExactOfComponentFieldsW978",
      "unitMappingConeStrictExactOfComponentFieldsW978",
      "unitMappingConeIsoNonemptyOfComponentFieldsW978",
      "directBoundedLeftCalculusOfComponentFieldsW978",
      "boundedDerivedInfinityCategoryOfComponentFieldsW978",
      "closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978",
      "closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978_count"]
  fullDataConstructionResult :=
    "proved: W978 constructs the W977 full-data provider from W971 component\
      fields by assembling W944 target no-univ data, W973 closed-embedding\
      closedness data, W974 endpoint data, W975 localized-adjunction data,\
      W948 normalized-source-triangulation data, and W976 unit data"
  exactAtResult :=
    "proved: the W978 component-field surface feeds the W977/W976/W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["W977 full-data provider constructed from the established W971 component\
      field surface",
      "the W971 component fields remain explicit, so this is a nonterminal\
      provider-construction route rather than a product-success witness"]
  remainingInputs :=
    closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978
  productSuccessClaimed := false

theorem currentW978ClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRouteStateW978;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
