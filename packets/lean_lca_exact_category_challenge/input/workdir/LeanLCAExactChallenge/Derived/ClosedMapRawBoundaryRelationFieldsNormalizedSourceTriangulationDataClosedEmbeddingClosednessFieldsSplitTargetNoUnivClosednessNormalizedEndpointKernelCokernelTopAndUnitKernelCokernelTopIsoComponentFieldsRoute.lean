import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationDataClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute

/-!
W970 feeds the W969 source-triangulation-data route while replacing the
separate W719 normalized fixed-target data fields and W722 source triangulation
provider by the W948 normalized-source-triangulation provider.
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
W970 preserves the W969 field surface while replacing W719 normalized
fixed-target data projections plus W722 source-triangulation data by the W948
normalized-source-triangulation provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970 :
    Type 2 where
  rightOpenBoundary :
    Dbounded.MetrizableWppLimitRightOpenClosedQuotientCoverBoundary
  sourcePiZeroBoundary :
    Dbounded.MetrizableWppLimitSourceDifferenceCokernelPiZeroBoundary
  relationPullbackProvider :
    ClosedNatTransOrdinaryRelationPullbackProviderW712
  targetRelationLiftsProvider :
    ClosedNatTransOrdinaryTargetRelationLiftsProviderW712
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

/-- W970 derives unit mapping-cone algebraic exactness from unit kernel equality. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ := by
  intro X i x₂ hx₂
  exact (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂

/- W970 reconstructs unit mapping-cone strict short exactness directly. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) := by
  intro X i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.unitMappingConeKernelEquality X i)
      (leaves.unitMappingConeClosedEmbedding X i)
      (leaves.unitMappingConeOpenMap X i)
      (leaves.unitMappingConeCokernelTop X i)

/- W970 wraps a chosen unit mapping-cone isomorphism as the W967 Nonempty witness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  fun X => ⟨leaves.unitMappingConeIso X⟩

/- W970 builds the W969 leaves consumed by the source-triangulation-data route. -/
def w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactNoUnivMembershipProvider :=
    leaves.targetCodomainCompactNoUnivMembershipProvider
  globalClosedEmbeddingComponents := leaves.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    leaves.mappedCokernelClosedEmbeddingProvider
  normalizedLiftBlueprint :=
    normalizedLiftBlueprint_of_normalizedFixedTargetDataW719
      (normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        leaves.normalizedSourceTriangulationData)
  targetFixedTargetUniq :=
    targetFixedTargetUniq_of_normalizedFixedTargetDataW719
      (normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        leaves.normalizedSourceTriangulationData)
  localizationModelFixedTargetUniq :=
    localizationModelFixedTargetUniq_of_normalizedFixedTargetDataW719
      (normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
        leaves.normalizedSourceTriangulationData)
  sourceTriangulationData :=
    sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
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

/-- W970 builds the W968 leaves through W969. -/
def w968LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968 :=
  w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970 leaves)

/-- W970 builds the W967 leaves through W969. -/
def w967LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967 :=
  w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970 leaves)

/-- W970 builds the W966 leaves through W969. -/
def w966LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966 :=
  w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970 leaves)

theorem directBoundedLeftCalculusOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970 leaves)

noncomputable def boundedDerivedInfinityCategoryOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970 leaves)

/--
W970 records the W969 surface with W719 normalized fixed-target fields and W722
source-triangulation data consolidated into one W948 provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary proposition",
    "raw source-difference cokernel-pi-zero WPP-limit boundary proposition",
    "raw closed-natural-transformation relation-pullback provider",
    "raw closed-natural-transformation target-relation-lifts provider",
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

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970.length =
      21 :=
  rfl

/-- Current checked W970 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW970 :
    Type where
  seed : String
  declarations : List String
  normalizedSourceDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW970 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW970
    where
  seed :=
    "w970-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-normalized-source-triangulation-data-iso-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW970",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW970",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW970",
      "w969LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "w968LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "w967LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "w966LeavesOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "directBoundedLeftCalculusOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "boundedDerivedInfinityCategoryOfNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW970",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970_count"]
  normalizedSourceDataResult :=
    "proved: W970 projects W948 normalized-source-triangulation data into W719\
      normalized fixed-target fields and W722 source-triangulation data for the\
      W969 route"
  exactAtResult :=
    "proved: the W970 normalized-source-triangulation endpoint-kernel/\
      cokernel-top and unit-kernel/cokernel-top iso component field surface\
      feeds the W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["W719 normalized fixed-target fields plus W722 source-triangulation data\
      replaced by W948 normalized-source-triangulation data",
      "raw W716 boundary propositions, raw W717 relation providers, split\
      target primitives, W961 closed-embedding closedness fields, endpoint\
      closed/open/cokernel-top/kernel-equality fields, bounded-homotopy\
      localized right-adjoint/adjunction fields, and the remaining unit\
      mapping-cone model/component/isomorphism fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW970
  productSuccessClaimed := false

theorem currentW970ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW970;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
