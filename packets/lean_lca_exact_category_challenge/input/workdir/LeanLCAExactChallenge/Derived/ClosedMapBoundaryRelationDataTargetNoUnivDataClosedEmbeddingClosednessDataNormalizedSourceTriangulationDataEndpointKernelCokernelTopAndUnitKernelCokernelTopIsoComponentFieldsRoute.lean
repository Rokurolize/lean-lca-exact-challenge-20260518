import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataNormalizedSourceTriangulationDataClosedEmbeddingClosednessFieldsEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W973 feeds the W972 target-no-univ-data route while replacing the two
closed-embedding closedness fields by a branch-specific closed-embedding
closedness data provider.
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
W973 closed-embedding closedness provider: keep the W961 closed-embedding
branch explicit without widening back to W725's closed-map-or-closed-embedding
sum.
-/
structure ClosedEmbeddingClosednessDataProviderW973 : Type 2 where
  globalClosedEmbeddingComponents :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
  mappedCokernelClosedEmbeddingProvider :
    MappedExplicitCokernelClosedEmbeddingProviderW519

/-- W973 projects the selected-difference closed-embedding components. -/
def globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
    (closednessData : ClosedEmbeddingClosednessDataProviderW973) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718 :=
  closednessData.globalClosedEmbeddingComponents

/-- W973 projects the mapped-cokernel closed-embedding provider. -/
def mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
    (closednessData : ClosedEmbeddingClosednessDataProviderW973) :
    MappedExplicitCokernelClosedEmbeddingProviderW519 :=
  closednessData.mappedCokernelClosedEmbeddingProvider

/--
W973 preserves the W972 field surface while replacing the two W961
closed-embedding fields by one branch-specific closedness provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointCokernelTop :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤
  endpointKernelEquality :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 ↔
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeClosedEmbedding :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosedEmbedding (((unitMappingConeModel X).as.sc i).f :
        ((unitMappingConeModel X).as.sc i).X₁ →
          ((unitMappingConeModel X).as.sc i).X₂)
  unitMappingConeOpenMap :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
  unitMappingConeCokernelTop :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (((unitMappingConeModel X).as.sc i).g) =
        ⊤
  unitMappingConeKernelEquality :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 ↔
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              (boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
        unitMappingConeModel X)

/- W973 builds the W972 leaves consumed by the target-no-univ-data route. -/
def w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData := leaves.targetNoUnivData
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
      leaves.closedEmbeddingClosednessData
  mappedCokernelClosedEmbeddingProvider :=
    mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
      leaves.closedEmbeddingClosednessData
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointCokernelTop := leaves.endpointCokernelTop
  endpointKernelEquality := leaves.endpointKernelEquality
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  unitMappingConeModel := leaves.unitMappingConeModel
  unitMappingConeClosedEmbedding := leaves.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := leaves.unitMappingConeOpenMap
  unitMappingConeCokernelTop := leaves.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := leaves.unitMappingConeKernelEquality
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W973 derives unit mapping-cone algebraic exactness through W972. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfUnitKernelEqualityW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
      leaves)

/-- W973 reconstructs unit mapping-cone strict short exactness through W972. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitKernelCokernelTopW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
      leaves)

/-- W973 wraps a chosen unit mapping-cone isomorphism through W972. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitIsoChoiceW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
      leaves)

/-- W973 builds the W971 leaves through W972. -/
def w971LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

/-- W973 builds the W970 leaves through W972. -/
def w970LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970 :=
  w970LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

/-- W973 builds the W969 leaves through W972. -/
def w969LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969 :=
  w969LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

/-- W973 builds the W968 leaves through W972. -/
def w968LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968 :=
  w968LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

theorem directBoundedLeftCalculusOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

noncomputable def boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973 leaves)

/--
W973 records the W972 surface with the two closed-embedding closedness fields
consolidated into one branch-specific provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W944 target no-univ data provider: target-difference preimage surjectivity\
      and target-codomain compact no-univ membership data for every target\
      diagram",
    "W973 closed-embedding closedness data provider: W718 selected-difference\
      closed-embedding components and W519 mapped explicit cokernel\
      closed-embedding provider",
    "W948 normalized-source-triangulation data provider: W719 normalized\
      fixed-target data and W722 source-side triangulation data",
    "endpoint degreewise closed-embedding witnesses",
    "endpoint degreewise open-map witnesses",
    "endpoint degreewise cokernel-subgroup-top witnesses",
    "endpoint degreewise kernel-equality witnesses",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise cokernel-subgroup-top components",
    "unit mapping-cone degreewise kernel-equality components",
    "chosen unit mapping-cone isomorphism from the adjunction-unit mapping cone\
      to the chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973.length =
      16 :=
  rfl

/-- Current checked W973 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW973 :
    Type where
  seed : String
  declarations : List String
  closedEmbeddingClosednessDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW973 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW973
    where
  seed :=
    "w973-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-boundary-relation-target-no-univ-data-closed-embedding-\
      closedness-data-normalized-source-triangulation-data-iso-component-fields"
  declarations :=
    ["ClosedEmbeddingClosednessDataProviderW973",
      "globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973",
      "mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973",
      "MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973",
      "w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW973",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW973",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW973",
      "directBoundedLeftCalculusOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973_count"]
  closedEmbeddingClosednessDataResult :=
    "proved: W973 projects a branch-specific closed-embedding closedness data\
      provider into the W718 selected-difference closed-embedding components\
      and W519 mapped explicit cokernel closed-embedding provider consumed by\
      the W972 route"
  exactAtResult :=
    "proved: the W973 closed-embedding-closedness-data target-no-univ-data\
      boundary-relation normalized-source endpoint-kernel/cokernel-top and\
      unit-kernel/cokernel-top iso component field surface feeds the W972/W971/\
      W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["W961 closed-embedding closedness fields replaced by W973\
      closed-embedding closedness data",
      "endpoint closed/open/cokernel-top/kernel-equality fields,\
      bounded-homotopy localized right-adjoint/adjunction fields, and the\
      remaining unit mapping-cone model/component/isomorphism fields remain\
      explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW973
  productSuccessClaimed := false

theorem currentW973ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW973;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
