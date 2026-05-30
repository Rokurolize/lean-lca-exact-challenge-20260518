import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataNormalizedSourceTriangulationDataClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W972 feeds the W971 boundary/relation-data route while replacing the split
target-difference and target-codomain no-univ primitives by the W944 target
no-univ data provider.
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
W972 preserves the W971 field surface while replacing the two split target
primitives by the W944 target no-univ data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
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

/-- W972 derives unit mapping-cone algebraic exactness from unit kernel equality. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ := by
  intro X i x₂ hx₂
  exact (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂

/- W972 reconstructs unit mapping-cone strict short exactness directly. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) := by
  intro X i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.unitMappingConeKernelEquality X i)
      (leaves.unitMappingConeClosedEmbedding X i)
      (leaves.unitMappingConeOpenMap X i)
      (leaves.unitMappingConeCokernelTop X i)

/- W972 wraps a chosen unit mapping-cone isomorphism as the W967 Nonempty witness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  fun X => ⟨leaves.unitMappingConeIso X⟩

/- W972 builds the W971 leaves consumed by the boundary/relation-data route. -/
def w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetDifferenceSurjectiveForTargetProvider :=
    targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944
      leaves.targetNoUnivData
  targetCodomainCompactNoUnivMembershipProvider :=
    targetCodomainCompactNoUnivMembershipPrimitiveOfTargetNoUnivDataW944
      leaves.targetNoUnivData
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

/-- W972 builds the W970 leaves through W971. -/
def w970LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopNormalizedSourceTriangulationDataIsoComponentFieldLeavesW970 :=
  w970LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972 leaves)

/-- W972 builds the W969 leaves through W971. -/
def w969LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969 :=
  w969LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972 leaves)

/-- W972 builds the W968 leaves through W971. -/
def w968LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968 :=
  w968LeavesOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972 leaves)

theorem directBoundedLeftCalculusOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972 leaves)

noncomputable def boundedDerivedInfinityCategoryOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBoundaryRelationDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW971
    (w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972 leaves)

/--
W972 records the W971 surface with split target primitives consolidated into
one W944 target no-univ provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W944 target no-univ data provider: target-difference preimage surjectivity\
      and target-codomain compact no-univ membership data for every target\
      diagram",
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

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972.length =
      17 :=
  rfl

/-- Current checked W972 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW972 :
    Type where
  seed : String
  declarations : List String
  targetNoUnivDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW972 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW972
    where
  seed :=
    "w972-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-boundary-relation-target-no-univ-data-normalized-source-\
      triangulation-data-iso-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW972",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW972",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW972",
      "w971LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "w970LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "w969LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "w968LeavesOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "directBoundedLeftCalculusOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "boundedDerivedInfinityCategoryOfBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW972",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972_count"]
  targetNoUnivDataResult :=
    "proved: W972 projects W944 target no-univ data into target-difference\
      surjectivity and target-codomain compact no-univ membership primitives\
      for the W971 route"
  exactAtResult :=
    "proved: the W972 boundary-relation target-no-univ-data normalized-source\
      endpoint-kernel/cokernel-top and unit-kernel/cokernel-top iso component\
      field surface feeds the W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["split target-difference and target-codomain no-univ primitives replaced\
      by W944 target no-univ data",
      "W961 closed-embedding closedness fields, W948 normalized-source-\
      triangulation data, endpoint closed/open/cokernel-top/kernel-equality\
      fields, bounded-homotopy localized right-adjoint/adjunction fields, and\
      the remaining unit mapping-cone model/component/isomorphism fields remain\
      explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW972
  productSuccessClaimed := false

theorem currentW972ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW972;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
