import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedSourceTriangulationDataClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W971 feeds the W970 normalized-source-triangulation route while replacing raw
W716 boundary fields and raw W717 relation fields by the W730 boundary/relation
data provider.
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
W971 preserves the W970 field surface while replacing two raw W716 boundary
propositions and two raw W717 relation providers by the W730 boundary/relation
data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactNoUnivMembershipProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  globalClosedEmbeddingComponents :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718
  mappedCokernelClosedEmbeddingProvider :
    MappedExplicitCokernelClosedEmbeddingProviderW519
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

/-- W971 derives unit mapping-cone algebraic exactness from unit kernel equality. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ := by
  intro X i x₂ hx₂
  exact (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂

/- W971 reconstructs unit mapping-cone strict short exactness directly. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) := by
  intro X i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.unitMappingConeKernelEquality X i)
      (leaves.unitMappingConeClosedEmbedding X i)
      (leaves.unitMappingConeOpenMap X i)
      (leaves.unitMappingConeCokernelTop X i)

/- W971 wraps a chosen unit mapping-cone isomorphism as the W967 Nonempty witness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  fun X => ⟨leaves.unitMappingConeIso X⟩

/- W971 builds the W970 leaves consumed by the normalized-source route. -/
def w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970
    where
  rightOpenBoundary :=
    rightOpenBoundary_of_boundaryDataW716
      (boundaryData_of_boundaryRelationDataW730 leaves.boundaryRelationData)
  sourcePiZeroBoundary :=
    sourcePiZeroBoundary_of_boundaryDataW716
      (boundaryData_of_boundaryRelationDataW730 leaves.boundaryRelationData)
  relationPullbackProvider :=
    relationPullbackProvider_of_relationDataW717
      (relationData_of_boundaryRelationDataW730 leaves.boundaryRelationData)
  targetRelationLiftsProvider :=
    targetRelationLiftsProvider_of_relationDataW717
      (relationData_of_boundaryRelationDataW730 leaves.boundaryRelationData)
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    leaves.targetCodomainCompactNoUnivMembershipProvider
  globalClosedEmbeddingComponents := leaves.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    leaves.mappedCokernelClosedEmbeddingProvider
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

/-- W971 builds the W969 leaves through W970. -/
def w969LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969 :=
  w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971 leaves)

/-- W971 builds the W968 leaves through W970. -/
def w968LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968 :=
  w968LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971 leaves)

/-- W971 builds the W967 leaves through W970. -/
def w967LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967 :=
  w967LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971 leaves)

theorem directBoundedLeftCalculusOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971 leaves)

noncomputable def boundedDerivedInfinityCategoryOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971 leaves)

/--
W971 records the W970 surface with raw W716/W717 fields consolidated into one
W730 boundary/relation data provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "W718 selected-difference closed-embedding diagram component provider",
    "W519 mapped explicit cokernel closed-embedding provider",
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

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971.length =
      18 :=
  rfl

/-- Current checked W971 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW971 :
    Type where
  seed : String
  declarations : List String
  boundaryRelationDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW971 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW971
    where
  seed :=
    "w971-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-boundary-relation-data-normalized-source-triangulation-data-\
      iso-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW971",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW971",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW971",
      "w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "w969LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "w968LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "w967LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "directBoundedLeftCalculusOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "boundedDerivedInfinityCategoryOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971_count"]
  boundaryRelationDataResult :=
    "proved: W971 projects W730 boundary/relation data into W716 right-open\
      boundary/source-pi-zero boundary data and W717 relation-pullback/\
      target-relation-lifts data for the W970 route"
  exactAtResult :=
    "proved: the W971 boundary-relation-data normalized-source-triangulation\
      endpoint-kernel/cokernel-top and unit-kernel/cokernel-top iso component\
      field surface feeds the W970/W969/W968/W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["raw W716 boundary propositions and raw W717 relation providers replaced\
      by W730 boundary/relation data",
      "split target primitives, W961 closed-embedding closedness fields,\
      W948 normalized-source-triangulation data, endpoint closed/open/\
      cokernel-top/kernel-equality fields, bounded-homotopy localized\
      right-adjoint/adjunction fields, and the remaining unit mapping-cone\
      model/component/isomorphism fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW971
  productSuccessClaimed := false

theorem currentW971ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW971;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
