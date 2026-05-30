import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W987 replaces W986's remaining separate W730 boundary/relation data and W986
target/closed-embedding-closedness/normalized-source/endpoint-localized data by
one branch-specific full-data provider.
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
W987 full-data provider: package W730 boundary/relation data with the W986
branch-specific target/closedness/normalized-source/endpoint provider.
-/
structure BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986

/-- W987 projects W730 boundary/relation data. -/
def boundaryRelationDataOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    MetrizableWppBoundaryRelationDataProviderW730 :=
  fullData.boundaryRelationData

/-- W987 projects W986 target/closedness/normalized-source/endpoint data. -/
def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :=
  fullData.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W987 constructs the W986 full-data provider from one full-data provider. -/
noncomputable def w986FullDataOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986
    where
  boundaryRelationData :=
    boundaryRelationDataOfFullDataW987 fullData
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
      fullData

/- W987 feeds W986 after unpacking full data. -/
noncomputable def w981LeavesOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

/- W987 exposes the W971 component-field split obtained through W986. -/
noncomputable def componentFieldsOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

/-- W987 reconstructs endpoint strict short exactness through W986. -/
noncomputable def endpointStrictExactOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

/-- W987 derives unit mapping-cone algebraic exactness through W986. -/
noncomputable def unitMappingConeAlgebraicExactOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfFullDataW987 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfFullDataW987 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfFullDataW987 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfFullDataW987 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

/-- W987 reconstructs unit mapping-cone strict short exactness through W986. -/
noncomputable def unitMappingConeStrictExactOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfFullDataW987 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

/-- W987 wraps the unit mapping-cone isomorphism through W986. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfFullDataW987 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfFullDataW987 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

theorem directBoundedLeftCalculusOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

noncomputable def boundedDerivedInfinityCategoryOfFullDataW987
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (w986FullDataOfFullDataW987 fullData)

def fullDataInputNamesW987 : List String :=
  ["W987 boundary-relation/target-closed-embedding-closedness/normalized-source/endpoint-localized full-data provider"]

theorem fullDataInputNamesW987_count :
    fullDataInputNamesW987.length = 1 :=
  rfl

structure MetrizableFullDataRouteStateW987 : Type where
  seed : String
  declarations : List String
  fullDataProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableFullDataRouteStateW987 :
    MetrizableFullDataRouteStateW987
    where
  seed := "w987-full-data-route"
  declarations :=
    ["BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987",
      "boundaryRelationDataOfFullDataW987",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987",
      "w986FullDataOfFullDataW987",
      "w981LeavesOfFullDataW987",
      "componentFieldsOfFullDataW987",
      "endpointStrictExactOfFullDataW987",
      "unitMappingConeAlgebraicExactOfFullDataW987",
      "unitMappingConeStrictExactOfFullDataW987",
      "unitMappingConeIsoNonemptyOfFullDataW987",
      "directBoundedLeftCalculusOfFullDataW987",
      "boundedDerivedInfinityCategoryOfFullDataW987",
      "fullDataInputNamesW987_count"]
  fullDataProjectionResult :=
    "proved: W987 extracts W730 boundary/relation data and W986\
      target/closed-embedding-closedness/normalized-source/endpoint-localized\
      data from one branch-specific full-data provider"
  exactAtResult :=
    "proved: the W987 branch-specific full-data surface feeds the W986/W985/\
      W984/W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/\
      W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := fullDataInputNamesW987
  productSuccessClaimed := false

theorem currentW987FullDataRoute_productSuccess :
    (let state := currentMetrizableFullDataRouteStateW987;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
