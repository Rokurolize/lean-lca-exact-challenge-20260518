import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataRoute

/-!
W986 replaces W985's separate W984 target/closed-embedding-closedness data and
W950 normalized-source/endpoint-localized-unit data by one branch-specific
target/closedness/normalized-source/endpoint provider.
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
W986 target/closed-embedding/normalized-source/endpoint provider: package the
branch-specific W984 target/closedness data with W950 normalized-source/endpoint
data.
-/
structure TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :
    Type 2 where
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  normalizedSourceEndpointLocalizedUnitData :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950

/-- W986 projects W984 target/closed-embedding closedness data. -/
def targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    (targetNormalizedEndpointData :
      TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetNormalizedEndpointData.targetClosedEmbeddingClosednessData

/-- W986 projects W950 normalized-source/endpoint-localized-unit data. -/
def normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    (targetNormalizedEndpointData :
      TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  targetNormalizedEndpointData.normalizedSourceEndpointLocalizedUnitData

/--
W986 full-data provider: W985's surface with W984 target/closedness and W950
normalized-source/endpoint data supplied by one provider.
-/
structure BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986

/-- W986 constructs the W985 full-data provider from target/normalized/endpoint data. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitChoiceDataProviderW985
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
      fullData.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
      fullData.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/- W986 feeds W985 after unpacking target/normalized/endpoint data. -/
noncomputable def w981LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

/- W986 exposes the W971 component-field split obtained through W985. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

/-- W986 reconstructs endpoint strict short exactness through W985. -/
noncomputable def endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

/-- W986 derives unit mapping-cone algebraic exactness through W985. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

/-- W986 reconstructs unit mapping-cone strict short exactness through W985. -/
noncomputable def unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

/-- W986 wraps the unit mapping-cone isomorphism through W985. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceEndpointLocalizedUnitW985
    (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
      fullData)

def targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986 :
    List String :=
  ["W730 boundary/relation data provider",
    "W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data provider"]

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986.length =
      2 :=
  rfl

structure MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitRouteStateW986 :
    Type where
  seed : String
  declarations : List String
  targetNormalizedEndpointProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitRouteStateW986 :
    MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitRouteStateW986
    where
  seed := "w986-target-closed-embedding-closedness-normalized-source-endpoint-route"
  declarations :=
    ["TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986",
      "targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986",
      "normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986",
      "BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986",
      "fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "w981LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986_count"]
  targetNormalizedEndpointProjectionResult :=
    "proved: W986 extracts W984 target/closed-embedding closedness data and\
      W950 normalized-source/endpoint-localized-unit data from one\
      branch-specific provider"
  exactAtResult :=
    "proved: the W986 target/closed-embedding-closedness/normalized-source/\
      endpoint-localized full-data surface feeds the W985/W984/W983/W982/\
      W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/\
      W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/\
      W954/W953/W952 stable ExactAt route"
  remainingInputs :=
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitInputNamesW986
  productSuccessClaimed := false

theorem currentW986TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitRouteStateW986;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
