import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W969 feeds the W968 chosen unit-isomorphism route while replacing the three raw
source-triangulation fields by the existing W722 source-triangulation data
provider.
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
W969 preserves the W968 field surface while replacing raw source
pretriangulated, source triangulated, and triangle-completion fields by the
W722 source-triangulation data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969 :
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
  normalizedLiftBlueprint :
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  targetFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  localizationModelFixedTargetUniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
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

/-- W969 derives unit mapping-cone algebraic exactness from unit kernel equality. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ := by
  intro X i x₂ hx₂
  exact (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂

/--
W969 directly reconstructs unit mapping-cone strict short exactness from unit
kernel equality, closed embedding, open map, and cokernel top.
-/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) := by
  intro X i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.unitMappingConeKernelEquality X i)
      (leaves.unitMappingConeClosedEmbedding X i)
      (leaves.unitMappingConeOpenMap X i)
      (leaves.unitMappingConeCokernelTop X i)

/-- W969 wraps a chosen unit mapping-cone isomorphism as the W967 Nonempty witness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  fun X => ⟨leaves.unitMappingConeIso X⟩

/-- W969 builds the W968 leaves consumed by the chosen unit-isomorphism route. -/
def w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968
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
  normalizedLiftBlueprint := leaves.normalizedLiftBlueprint
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      leaves.sourceTriangulationData
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

/-- W969 builds the W967 leaves through W968. -/
def w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967 :=
  w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/-- W969 builds the W966 leaves through W967. -/
def w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966 :=
  w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
    (w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/-- W969 constructs W965 leaves through W966. -/
def w965LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965 :=
  w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/-- W969 constructs W964 leaves through W966/W965. -/
def w964LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964 :=
  w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/-- W969 constructs W963 leaves through W966/W965/W964. -/
def w963LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963 :=
  w963LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/-- W969 constructs W962 leaves through W966/W965/W964/W963. -/
def w962LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :=
  w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

theorem directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969 leaves)

/--
W969 records the W968 surface with raw source-triangulation fields replaced by
the W722 source-triangulation data provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969 :
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
    "normalized strict-representative lift blueprint for WPP diagrams and maps",
    "target fixed-target uniqueness for the WPP objectwise localization functor",
    "localization-model fixed-target uniqueness for the WPP objectwise\
      localization functor",
    "W722 source-triangulation data provider for BoundedComplexCategory\
      MetrizableLCA",
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

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969.length =
      24 :=
  rfl

/-- Current checked W969 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsRouteStateW969 :
    Type where
  seed : String
  declarations : List String
  unitKernelResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsRouteStateW969 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsRouteStateW969
    where
  seed :=
    "w969-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-source-triangulation-data-iso-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldLeavesW969",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW969",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW969",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW969",
      "w968LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w965LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w964LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w963LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "w962LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsW969",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969_count"]
  unitKernelResult :=
    "proved: W969 derives unit mapping-cone degreewise algebraic exactness from\
      unit mapping-cone kernel-equality witnesses and directly reconstructs unit\
      mapping-cone strictShortExact from closed-embedding, open-map,\
      cokernel-top, and kernel-equality witnesses"
  exactAtResult :=
    "proved: the W969 endpoint-kernel/cokernel-top and unit-kernel/cokernel-top\
      source-triangulation-data iso component field surface feeds the W968/\
      W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  refinedInputs :=
    ["raw source pretriangulated, source triangulated, and triangle-completion\
      fields replaced by W722 source-triangulation data",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, W961\
      closed-embedding closedness fields, endpoint closed/open/cokernel-top/\
      kernel-equality fields, bounded-homotopy localized right-adjoint/\
      adjunction fields, and the remaining unit mapping-cone model/component/\
      isomorphism fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsInputNamesW969
  productSuccessClaimed := false

theorem currentW969ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopSourceTriangulationDataIsoComponentFieldsRouteStateW969;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
