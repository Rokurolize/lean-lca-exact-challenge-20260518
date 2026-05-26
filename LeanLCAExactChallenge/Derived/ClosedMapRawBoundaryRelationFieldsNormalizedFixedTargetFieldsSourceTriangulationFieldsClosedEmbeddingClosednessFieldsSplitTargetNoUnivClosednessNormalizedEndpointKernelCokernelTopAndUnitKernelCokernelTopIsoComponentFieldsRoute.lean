import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopComponentFieldsRoute

/-!
W968 feeds the W967 endpoint-kernel/cokernel-top and unit-kernel/cokernel-top
component route while replacing the unit mapping-cone Nonempty isomorphism
witness by a chosen isomorphism.
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
W968 preserves the W967 field surface while replacing the unit mapping-cone
Nonempty isomorphism witness by a chosen unit mapping-cone isomorphism field.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968 :
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

/-- W968 derives unit mapping-cone algebraic exactness from unit kernel equality. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ := by
  intro X i x₂ hx₂
  exact (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂

/--
W968 directly reconstructs unit mapping-cone strict short exactness from unit
kernel equality, closed embedding, open map, and cokernel top.
-/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) := by
  intro X i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (leaves.unitMappingConeKernelEquality X i)
      (leaves.unitMappingConeClosedEmbedding X i)
      (leaves.unitMappingConeOpenMap X i)
      (leaves.unitMappingConeCokernelTop X i)

/-- W968 wraps a chosen unit mapping-cone isomorphism as the W967 Nonempty witness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  fun X => ⟨leaves.unitMappingConeIso X⟩

/-- W968 builds the W967 leaves consumed by the unit-kernel/cokernel-top route. -/
def w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967
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
  unitMappingConeCokernelTop := leaves.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := leaves.unitMappingConeKernelEquality
  unitMappingConeIso := unitMappingConeIsoNonemptyOfUnitIsoChoiceW968 leaves

/-- W968 builds the W966 leaves through W967. -/
def w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966 :=
  w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
    (w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

/-- W968 constructs W965 leaves through W966. -/
def w965LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965 :=
  w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

/-- W968 constructs W964 leaves through W966/W965. -/
def w964LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessEndpointCokernelTopAndUnitMappingConeComponentFieldLeavesW964 :=
  w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

/-- W968 constructs W963 leaves through W966/W965/W964. -/
def w963LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963 :=
  w963LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

/-- W968 constructs W962 leaves through W966/W965/W964/W963. -/
def w962LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :=
  w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

theorem directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
    (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968 leaves)

/--
W968 records the W967 surface with the unit mapping-cone Nonempty isomorphism
replaced by a chosen unit mapping-cone isomorphism field.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968 :
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
    "unit mapping-cone degreewise kernel-equality components",
    "chosen unit mapping-cone isomorphism from the adjunction-unit mapping cone\
      to the chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968.length =
      26 :=
  rfl

/-- Current checked W968 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsRouteStateW968 :
    Type where
  seed : String
  declarations : List String
  unitKernelResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsRouteStateW968 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsRouteStateW968
    where
  seed :=
    "w968-closed-embedding-closedness-endpoint-kernel-cokernel-top-unit-kernel-\
      cokernel-top-iso-component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldLeavesW968",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW968",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW968",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW968",
      "w967LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "w965LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "w964LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "w963LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "w962LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW968",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968_count"]
  unitKernelResult :=
    "proved: W968 derives unit mapping-cone degreewise algebraic exactness from\
      unit mapping-cone kernel-equality witnesses and directly reconstructs unit\
      mapping-cone strictShortExact from closed-embedding, open-map,\
      cokernel-top, and kernel-equality witnesses"
  exactAtResult :=
    "proved: the W968 endpoint-kernel/cokernel-top and unit-kernel/cokernel-top\
      iso component field surface feeds the W967/W966/W965/W964/W963/W962/\
      W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["unit mapping-cone Nonempty isomorphism witnesses replaced by chosen unit\
      mapping-cone isomorphism witnesses",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, raw W722\
      source-triangulation fields, W961 closed-embedding closedness fields,\
      endpoint closed/open/cokernel-top/kernel-equality fields, bounded-homotopy\
      localized right-adjoint/adjunction fields, and the remaining unit\
      mapping-cone model/component/isomorphism fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsInputNamesW968
  productSuccessClaimed := false

theorem currentW968ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsRouteStateW968;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
