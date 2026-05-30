import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromTargetClosedEmbeddingClosednessRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataRoute

/-!
W1006 replaces W1005's separate W984 target/closed-embedding closedness data
and W950 normalized-source/endpoint-localized-unit data by the existing W986
target/closedness/normalized-source/endpoint-localized provider. It builds the
W1005 target-closedness surface and feeds W1005.
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
W1006 provider: W1005 target-closedness data with W984 target/closed-embedding
closedness data and W950 normalized-source/endpoint-localized-unit data
packaged into one W986 target/closedness/normalized-source/endpoint provider.
-/
structure BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData :
    TargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW986

/-- W1006 projects W984 target/closed-embedding closedness data from W986. -/
def targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    TargetNoUnivClosedEmbeddingClosednessDataProviderW984 :=
  targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W1006 projects W950 normalized-source/endpoint-localized-unit data from W986. -/
def normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    NormalizedSourceTriangulationEndpointLocalizedUnitDataProviderW950 :=
  normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataW986
    data.targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitData

/-- W1006 builds the W1005 target-closedness surface from W986. -/
def targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1005
    where
  boundaryRelationData := data.boundaryRelationData
  targetClosedEmbeddingClosednessData :=
    targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data
  normalizedSourceEndpointLocalizedUnitData :=
    normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data

/-- W1006 constructs W1004 normalized-source/endpoint-localized data through W1005. -/
def normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetNoUnivClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW1004 :=
  normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 constructs W1003 endpoint-localized-unit data through W1005. -/
def endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW1003 :=
  endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 constructs W982 localized-unit-choice data through W1005. -/
def localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982 :=
  localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 constructs W987 branch full data through W1005. -/
noncomputable def branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 recovers W715 target surjective-compact data through W1005. -/
noncomputable def targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 builds W997's branch-full-data surface through W1005. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data
  branchFullData :=
    branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data

/-- W1006 builds the W995 target-provider surface through W1005. -/
noncomputable def targetProviderDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 builds the W994 normalized-source/endpoint route data through W1005. -/
noncomputable def normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 returns the constructed W987 branch full data through W1005. -/
noncomputable def fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/- W1006 exposes W977 leaves through W1005. -/
noncomputable def w977LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w977LeavesOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/- W1006 exposes W971 component fields through W1005. -/
noncomputable def componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 reconstructs endpoint strict exactness through W1005. -/
noncomputable def endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 derives unit mapping-cone algebraic exactness through W1005. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 reconstructs unit mapping-cone strict short exactness through W1005. -/
noncomputable def unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

/-- W1006 wraps the unit mapping-cone isomorphism through W1005. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

theorem directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

noncomputable def boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
    (data :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessW1005
    (targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006
      data)

def targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006 : List String :=
  ["W730 boundary/relation data provider",
    "W986 target/closed-embedding-closedness/normalized-source/endpoint-localized data provider"]

theorem targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006_count :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006.length =
      2 :=
  rfl

structure MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointTargetSurjectiveCompactRouteStateW1006 :
    Type where
  seed : String
  declarations : List String
  targetNormalizedEndpointRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointTargetSurjectiveCompactRouteStateW1006 :
    MetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointTargetSurjectiveCompactRouteStateW1006
    where
  seed := "w1006-target-closed-embedding-closedness-normalized-source-endpoint-to-target-surjective-compact-route"
  declarations :=
    ["BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataProviderW1006",
      "targetClosedEmbeddingClosednessDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "normalizedSourceEndpointLocalizedUnitDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "targetClosedEmbeddingClosednessDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "normalizedSourceEndpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "endpointLocalizedUnitDataProviderOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "localizedUnitChoiceDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "branchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "targetSurjectiveCompactDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "targetSurjectiveCompactBranchFullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "targetProviderDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "normalizedSourceEndpointDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "w977LeavesOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "componentFieldsOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "endpointStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "unitMappingConeAlgebraicExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "unitMappingConeStrictExactOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "unitMappingConeIsoNonemptyOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "directBoundedLeftCalculusOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "boundedDerivedInfinityCategoryOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointW1006",
      "targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006_count"]
  targetNormalizedEndpointRepackagingResult :=
    "proved: W1006 constructs the W1005 target-closedness surface from W986\
      target/closedness/normalized-source/endpoint-localized data"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1006 inherits W1005/W1004/W1003/W1002/W998 target\
      surjective-compact recovery after W986 supplies W984 target/closedness\
      data and W950 normalized-source/endpoint-localized-unit data"
  exactAtResult :=
    "proved: the W1006 W986 target/closedness/normalized-source/endpoint\
      surface feeds W1005/W1004/W1003/W1002/W998/W997/W996/W995/W994/W993/\
      W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetClosedEmbeddingClosednessNormalizedSourceEndpointInputNamesW1006
  productSuccessClaimed := false

theorem currentW1006TargetClosedEmbeddingClosednessNormalizedSourceEndpointRoute_productSuccess :
    (let state :=
        currentMetrizableTargetClosedEmbeddingClosednessNormalizedSourceEndpointTargetSurjectiveCompactRouteStateW1006;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
