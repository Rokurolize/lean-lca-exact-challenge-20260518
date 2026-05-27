import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataRoute

/-!
W984 replaces W983's separate target no-univ and closed-embedding closedness
inputs by a branch-specific target/closed-embedding closedness provider.
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
W984 target/closed-embedding provider: package W944 target no-univ data with
the W973 branch-specific closed-embedding closedness data.
-/
structure TargetNoUnivClosedEmbeddingClosednessDataProviderW984 : Type 2 where
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973

/-- W984 projects W944 target no-univ data. -/
def targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
    (targetClosedEmbeddingClosednessData :
      TargetNoUnivClosedEmbeddingClosednessDataProviderW984) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetClosedEmbeddingClosednessData.targetNoUnivData

/-- W984 projects W973 closed-embedding closedness data. -/
def closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
    (targetClosedEmbeddingClosednessData :
      TargetNoUnivClosedEmbeddingClosednessDataProviderW984) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  targetClosedEmbeddingClosednessData.closedEmbeddingClosednessData

/--
W984 full-data provider: W983's surface with target no-univ and
closed-embedding closedness supplied by one branch-specific provider.
-/
structure BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessData :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984
  endpointLocalizedUnitData :
    EndpointStrictExactLocalizedUnitDataProviderW949
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948

/-- W984 constructs the W983 full-data provider from branch-specific target/closedness data. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitChoiceDataProviderW983
    where
  boundaryRelationData := fullData.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984
      fullData.targetClosedEmbeddingClosednessData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984
      fullData.targetClosedEmbeddingClosednessData
  endpointLocalizedUnitData := fullData.endpointLocalizedUnitData
  normalizedSourceTriangulationData :=
    fullData.normalizedSourceTriangulationData

/- W984 feeds W983 after unpacking target/closed-embedding closedness data. -/
noncomputable def w981LeavesOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

/- W984 exposes the W971 component-field split obtained through W983. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

/-- W984 reconstructs endpoint strict short exactness through W983. -/
noncomputable def endpointStrictExactOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

/-- W984 derives unit mapping-cone algebraic exactness through W983. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

/-- W984 reconstructs unit mapping-cone strict short exactness through W983. -/
noncomputable def unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

/-- W984 wraps the unit mapping-cone isomorphism through W983. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetClosedEmbeddingClosednessW984 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW984
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointLocalizedUnitChoiceW983
    (fullDataOfTargetClosedEmbeddingClosednessW984 fullData)

def targetClosedEmbeddingClosednessDataInputNamesW984 : List String :=
  ["W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider"]

theorem targetClosedEmbeddingClosednessDataInputNamesW984_count :
    targetClosedEmbeddingClosednessDataInputNamesW984.length = 2 :=
  rfl

def targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984 :
    List String :=
  ["W730 boundary/relation data provider",
    "W984 target no-univ plus closed-embedding closedness data provider",
    "W949 endpoint-localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984_count :
    targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984.length =
      4 :=
  rfl

structure MetrizableTargetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataRouteStateW984 :
    Type where
  seed : String
  declarations : List String
  targetClosednessProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataRouteStateW984 :
    MetrizableTargetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataRouteStateW984
    where
  seed := "w984-target-closed-embedding-closedness-endpoint-localized-unit-choice-route"
  declarations :=
    ["TargetNoUnivClosedEmbeddingClosednessDataProviderW984",
      "targetNoUnivDataOfTargetClosedEmbeddingClosednessDataW984",
      "closedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessDataW984",
      "BoundaryRelationTargetNoUnivClosedEmbeddingClosednessEndpointLocalizedUnitChoiceDataProviderW984",
      "fullDataOfTargetClosedEmbeddingClosednessW984",
      "w981LeavesOfTargetClosedEmbeddingClosednessW984",
      "componentFieldsOfTargetClosedEmbeddingClosednessW984",
      "endpointStrictExactOfTargetClosedEmbeddingClosednessW984",
      "unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW984",
      "unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW984",
      "unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW984",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW984",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW984",
      "targetClosedEmbeddingClosednessDataInputNamesW984_count",
      "targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984_count"]
  targetClosednessProjectionResult :=
    "proved: W984 extracts W944 target no-univ data and W973 closed-embedding\
      closedness data from a branch-specific target/closedness provider"
  exactAtResult :=
    "proved: the W984 target/closed-embedding-closedness full-data surface\
      feeds the W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/\
      W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs :=
    targetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataInputNamesW984
  productSuccessClaimed := false

theorem currentW984TargetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessEndpointLocalizedUnitChoiceFullDataRouteStateW984;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
