import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute

/-!
W993 combines the W992 W715-to-W944 target compactness bridge with the W988
localized-unit-choice surface. This keeps the W973 branch-specific closed
embedding closedness provider while replacing W992's endpoint
kernel/cokernel-top and unit component-field surface by endpoint strict
exactness plus W945 localized-unit data.
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
W993 data surface: W988 localized-unit-choice data with W944 target no-univ
data replaced by W715 target surjective-compact data.
-/
structure BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948

/--
W993 constructs W982 localized-unit-choice data, deriving the target no-univ
field from W715 and leaving W973 as the only closed-embedding closedness branch.
-/
def localizedUnitChoiceDataOfTargetSurjectiveCompactW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982
    where
  boundaryRelationData := data.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfTargetSurjectiveCompactW992
      data.targetSurjectiveCompactData
  closedEmbeddingClosednessData := data.closedEmbeddingClosednessData
  endpointStrictExact := data.endpointStrictExact
  localizedUnitData := data.localizedUnitData
  normalizedSourceTriangulationData :=
    data.normalizedSourceTriangulationData

/-- W993 constructs W987 full data through W988 after deriving W944 from W715. -/
def fullDataOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/- W993 exposes W981 leaves through W988/W987. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/- W993 exposes W971 component fields through W988/W987. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/-- W993 reconstructs endpoint strict exactness through W988/W987. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/-- W993 derives unit mapping-cone algebraic exactness through W988/W987. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/-- W993 reconstructs unit mapping-cone strict short exactness through W988/W987. -/
noncomputable def unitMappingConeStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

/-- W993 wraps the unit mapping-cone isomorphism through W988/W987. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactLocalizedUnitChoiceW993
    (data :
      BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW988
    (localizedUnitChoiceDataOfTargetSurjectiveCompactW993 data)

def targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993 :
    List String :=
  ["W730 boundary/relation data provider",
    "W715 target surjective-compact data provider",
    "W973 closed-embedding closedness data provider",
    "endpoint strict-exact family",
    "W945 localized-unit data provider",
    "W948 normalized-source-triangulation data provider"]

theorem targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993_count :
    targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993.length = 6 :=
  rfl

structure MetrizableTargetSurjectiveCompactLocalizedUnitChoiceRouteStateW993 :
    Type where
  seed : String
  declarations : List String
  targetCompactnessResult : String
  localizedUnitResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactLocalizedUnitChoiceRouteStateW993 :
    MetrizableTargetSurjectiveCompactLocalizedUnitChoiceRouteStateW993
    where
  seed := "w993-target-surjective-compact-localized-unit-choice-route"
  declarations :=
    ["BoundaryRelationTargetSurjectiveCompactClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW993",
      "localizedUnitChoiceDataOfTargetSurjectiveCompactW993",
      "fullDataOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "w981LeavesOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "componentFieldsOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "endpointStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "unitMappingConeAlgebraicExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "unitMappingConeStrictExactOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "unitMappingConeIsoNonemptyOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactLocalizedUnitChoiceW993",
      "targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993_count"]
  targetCompactnessResult :=
    "proved: W993 reuses W992 to derive W982 target no-univ data from W715\
      target surjective-compact data"
  localizedUnitResult :=
    "proved: the W945 localized-unit provider supplies W982's localized\
      adjunction and unit strict-exact/isomorphism data through W982"
  exactAtResult :=
    "proved: the W993 target-surjective-compact localized-unit-choice surface\
      feeds the W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/\
      W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := targetSurjectiveCompactLocalizedUnitChoiceInputNamesW993
  productSuccessClaimed := false

theorem currentW993TargetSurjectiveCompactLocalizedUnitChoiceRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactLocalizedUnitChoiceRouteStateW993;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
