import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointStrictAndUnitWitnessComponentFieldsRoute

/-!
W964 feeds the W963 endpoint-strict and unit-witness component route while
replacing the endpoint surjectivity field by an endpoint cokernel-top field.
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
W964 preserves the W963 field surface while replacing endpoint surjectivity by
the endpoint cokernel-subgroup-top condition. Surjectivity is then derived from
the already explicit endpoint open-map field.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964 :
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
  endpointAlgebraicExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 →
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

/--
W964 derives endpoint surjectivity from the endpoint cokernel-top field and
the endpoint open-map field.
-/
def endpointSurjectiveOfEndpointCokernelTopW964
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Function.Surjective ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) := by
  intro K i
  exact
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
      (K.sc i).g (leaves.endpointCokernelTop K i) (leaves.endpointOpenMap K i)

/-- W964 builds the W963 leaves consumed by the endpoint-strict route. -/
def w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964) :
    MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963
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
  endpointSurjective := endpointSurjectiveOfEndpointCokernelTopW964 leaves
  endpointAlgebraicExact := leaves.endpointAlgebraicExact
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

/-- W964 constructs W962 leaves through W963. -/
def w962LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :=
  w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964 leaves)

theorem directBoundedLeftCalculusOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964 leaves)

/--
W964 records the W963 endpoint component surface with endpoint surjectivity
replaced by a cokernel-subgroup-top field.
-/
def closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964 :
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
    "endpoint degreewise algebraic exactness witnesses",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise surjectivity components",
    "unit mapping-cone degreewise algebraic exactness components",
    "unit mapping-cone isomorphism from the adjunction-unit mapping cone to the\
      chosen model"]

theorem closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964_count :
    closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964.length =
      26 :=
  rfl

/-- Current checked W964 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsRouteStateW964 :
    Type where
  seed : String
  declarations : List String
  endpointSurjectivityResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsRouteStateW964 :
    MetrizableClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsRouteStateW964
    where
  seed :=
    "w964-closed-embedding-closedness-endpoint-cokernel-top-and-unit-mapping-cone-\
      component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964",
      "endpointSurjectiveOfEndpointCokernelTopW964",
      "w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964",
      "w962LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964",
      "directBoundedLeftCalculusOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964",
      "boundedDerivedInfinityCategoryOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964",
      "closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964",
      "closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964_count"]
  endpointSurjectivityResult :=
    "proved: W964 derives endpoint degreewise surjectivity from endpoint\
      cokernel-subgroup-top witnesses plus endpoint open-map witnesses"
  exactAtResult :=
    "proved: the W964 endpoint-cokernel-top and unit-mapping-cone component\
      field surface feeds the W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  refinedInputs :=
    ["endpoint degreewise surjectivity witnesses replaced by endpoint\
      cokernel-subgroup-top witnesses",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, raw W722\
      source-triangulation fields, W961 closed-embedding closedness fields,\
      bounded-homotopy localized right-adjoint/adjunction fields, and W962\
      unit mapping-cone component fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsInputNamesW964
  productSuccessClaimed := false

theorem currentW964ClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldsRouteStateW964;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
