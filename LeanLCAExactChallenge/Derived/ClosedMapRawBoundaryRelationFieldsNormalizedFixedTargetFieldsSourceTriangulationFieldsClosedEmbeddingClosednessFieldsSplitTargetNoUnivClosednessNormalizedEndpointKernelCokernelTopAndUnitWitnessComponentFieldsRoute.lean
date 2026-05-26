import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointCokernelTopAndUnitWitnessComponentFieldsRoute

/-!
W965 feeds the W964 endpoint-cokernel-top and unit-witness component route
while replacing endpoint algebraic exactness by endpoint kernel equality.
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
W965 preserves the W964 field surface while replacing endpoint algebraic
exactness by a bidirectional endpoint kernel-equality field.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965 :
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
  unitMappingConeSurjective :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      Function.Surjective (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
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

/-- W965 derives endpoint algebraic exactness from endpoint kernel equality. -/
def endpointAlgebraicExactOfEndpointKernelEqualityW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 →
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂ := by
  intro K i x₂ hx₂
  exact (leaves.endpointKernelEquality K i x₂).mp hx₂

/--
W965 directly reconstructs endpoint strict short exactness from kernel
equality, endpoint closed embedding, endpoint open map, and endpoint cokernel
top.
-/
def endpointStrictExactOfEndpointKernelCokernelTopW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) := by
  intro K i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.endpointKernelEquality K i)
      (leaves.endpointClosedEmbedding K i)
      (leaves.endpointOpenMap K i)
      (leaves.endpointCokernelTop K i)

/-- W965 builds the W964 leaves consumed by the endpoint-cokernel-top route. -/
def w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964
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
  endpointAlgebraicExact :=
    endpointAlgebraicExactOfEndpointKernelEqualityW965 leaves
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  unitMappingConeModel := leaves.unitMappingConeModel
  unitMappingConeClosedEmbedding := leaves.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := leaves.unitMappingConeOpenMap
  unitMappingConeSurjective := leaves.unitMappingConeSurjective
  unitMappingConeAlgebraicExact := leaves.unitMappingConeAlgebraicExact
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W965 constructs W963 leaves through W964. -/
def w963LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963 :=
  w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965 leaves)

/-- W965 constructs W962 leaves through W964/W963. -/
def w962LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :=
  w962LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965 leaves)

theorem directBoundedLeftCalculusOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965 leaves)

/--
W965 records the W964 endpoint component surface with endpoint algebraic
exactness replaced by endpoint kernel equality.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965 :
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
    "unit mapping-cone degreewise surjectivity components",
    "unit mapping-cone degreewise algebraic exactness components",
    "unit mapping-cone isomorphism from the adjunction-unit mapping cone to the\
      chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965.length =
      26 :=
  rfl

/-- Current checked W965 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsRouteStateW965 :
    Type where
  seed : String
  declarations : List String
  endpointKernelResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsRouteStateW965 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsRouteStateW965
    where
  seed :=
    "w965-closed-embedding-closedness-endpoint-kernel-cokernel-top-and-unit-\
      mapping-cone-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965",
      "endpointAlgebraicExactOfEndpointKernelEqualityW965",
      "endpointStrictExactOfEndpointKernelCokernelTopW965",
      "w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965",
      "w963LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965",
      "w962LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965",
      "directBoundedLeftCalculusOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965",
      "closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965",
      "closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965_count"]
  endpointKernelResult :=
    "proved: W965 derives endpoint degreewise algebraic exactness from\
      endpoint kernel-equality witnesses and directly reconstructs endpoint\
      strictShortExact from closed-embedding, open-map, cokernel-top, and\
      kernel-equality witnesses"
  exactAtResult :=
    "proved: the W965 endpoint-kernel/cokernel-top and unit-mapping-cone\
      component field surface feeds the W964/W963/W962/W961/W959/W958/W957/\
      W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["endpoint degreewise algebraic-exactness witnesses replaced by endpoint\
      kernel-equality witnesses",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, raw W722\
      source-triangulation fields, W961 closed-embedding closedness fields,\
      bounded-homotopy localized right-adjoint/adjunction fields, and W962\
      unit mapping-cone component fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965
  productSuccessClaimed := false

theorem currentW965ClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsRouteStateW965;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
