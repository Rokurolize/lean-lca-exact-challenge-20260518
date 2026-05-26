import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitWitnessComponentFieldsRoute

/-!
W966 feeds the W965 endpoint-kernel/cokernel-top and unit component route while
replacing the unit mapping-cone surjectivity field by a unit mapping-cone
cokernel-top field.
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
W966 preserves the W965 field surface while replacing unit mapping-cone
surjectivity by a unit mapping-cone cokernel-subgroup-top condition. The already
explicit unit mapping-cone open-map field then reconstructs surjectivity.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966 :
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
  sourcePretriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
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
  unitMappingConeAlgebraicExact :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          unitMappingConeModel X)

/--
W966 derives unit mapping-cone degreewise surjectivity from unit cokernel-top
witnesses and unit open-map witnesses.
-/
def unitMappingConeSurjectiveOfUnitCokernelTopW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      Function.Surjective (((leaves.unitMappingConeModel X).as.sc i).g :
        ((leaves.unitMappingConeModel X).as.sc i).X₂ →
          ((leaves.unitMappingConeModel X).as.sc i).X₃) := by
  intro X i
  exact
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
      (((leaves.unitMappingConeModel X).as.sc i).g)
      (leaves.unitMappingConeCokernelTop X i)
      (leaves.unitMappingConeOpenMap X i)

/-- W966 builds the W965 leaves consumed by the endpoint-kernel/cokernel route. -/
def w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965
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
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
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
  unitMappingConeSurjective :=
    unitMappingConeSurjectiveOfUnitCokernelTopW966 leaves
  unitMappingConeAlgebraicExact := leaves.unitMappingConeAlgebraicExact
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W966 constructs W964 leaves through W965. -/
def w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964 :=
  w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966 leaves)

/-- W966 constructs W963 leaves through W965/W964. -/
def w963LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963 :=
  w963LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966 leaves)

/-- W966 constructs W962 leaves through W965/W964/W963. -/
def w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :=
  w962LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966 leaves)

theorem directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966 leaves)

/--
W966 records the W965 surface with unit mapping-cone surjectivity replaced by a
unit mapping-cone cokernel-subgroup-top field.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966 :
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
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
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
    "unit mapping-cone degreewise algebraic exactness components",
    "unit mapping-cone isomorphism from the adjunction-unit mapping cone to the\
      chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966.length =
      26 :=
  rfl

/-- Current checked W966 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsRouteStateW966 :
    Type where
  seed : String
  declarations : List String
  unitCokernelTopResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsRouteStateW966 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsRouteStateW966
    where
  seed :=
    "w966-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-cokernel-\
      top-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966",
      "unitMappingConeSurjectiveOfUnitCokernelTopW966",
      "w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "w963LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966_count"]
  unitCokernelTopResult :=
    "proved: W966 derives unit mapping-cone degreewise surjectivity from unit\
      mapping-cone cokernel-subgroup-top witnesses plus unit open-map witnesses"
  exactAtResult :=
    "proved: the W966 endpoint-kernel/cokernel-top and unit-cokernel-top\
      component field surface feeds the W965/W964/W963/W962/W961/W959/W958/\
      W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["unit mapping-cone degreewise surjectivity witnesses replaced by unit\
      mapping-cone cokernel-subgroup-top witnesses",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, raw W722\
      source-triangulation fields, W961 closed-embedding closedness fields,\
      endpoint closed/open/cokernel-top/kernel-equality fields, bounded-homotopy\
      localized right-adjoint/adjunction fields, and the remaining unit\
      mapping-cone component fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966
  productSuccessClaimed := false

theorem currentW966ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsRouteStateW966;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
