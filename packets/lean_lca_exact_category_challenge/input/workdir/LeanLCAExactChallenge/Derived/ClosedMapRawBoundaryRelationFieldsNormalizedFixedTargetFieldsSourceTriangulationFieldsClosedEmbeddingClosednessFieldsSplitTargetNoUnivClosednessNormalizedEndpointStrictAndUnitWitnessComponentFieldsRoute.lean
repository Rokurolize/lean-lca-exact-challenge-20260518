import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitWitnessComponentFieldsRoute

/-!
W963 feeds the W962 unit-witness component route while replacing the endpoint
strict-short-exact witness field by explicit endpoint closed-embedding,
open-map, surjectivity, and algebraic-exactness component fields.
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
W963 preserves the W962 field surface while splitting endpoint
`MetrizableLCA.strictShortExact` witnesses into their four component fields.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963 :
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
  endpointSurjective :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Function.Surjective ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
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
W963 assembles endpoint strict short-exact witnesses from explicit endpoint
closed-embedding, open-map, surjectivity, and algebraic-exactness fields.
-/
def endpointStrictExactOfEndpointComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) := by
  intro K i
  exact
    { closed_inclusion := leaves.endpointClosedEmbedding K i
      open_map := leaves.endpointOpenMap K i
      surjective := leaves.endpointSurjective K i
      algebraic_exact := leaves.endpointAlgebraicExact K i }

/-- W963 builds the W962 leaves consumed by the unit-witness component route. -/
def w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962
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
  endpointStrictExact :=
    endpointStrictExactOfEndpointComponentFieldsW963 leaves
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

/-- W963 constructs W961 leaves through W962. -/
def w961LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW961 :=
  w961LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W959 leaves through W962/W961. -/
def w959LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959 :=
  w959LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W958 leaves through W962/W961/W959. -/
def w958LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958 :=
  w958LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W957 leaves through W962/W961/W959/W958. -/
def w957LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW957 :=
  w957LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W956 leaves through W962/W961/W959/W958/W957. -/
def w956LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW956 :=
  w956LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W955 leaves through W962/W961/W959/W958/W957/W956. -/
def w955LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :=
  w955LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W954 leaves through W962/W961/W959/W958/W957/W956/W955. -/
def w954LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :=
  w954LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W953 primitive leaves through W962/W961/W959/W958/W957/W956/W955/W954. -/
def w953PrimitiveLeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 constructs W952 leaves through W962/W961/W959/W958/W957/W956/W955/W954/W953. -/
def w952LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 W733 concrete leaves after constructing W962 leaves. -/
def concreteLeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/-- W963 W732 route data after constructing W962 leaves. -/
def routeDataProviderOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

theorem directBoundedLeftCalculusOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointStrictAndUnitMappingConeComponentFieldsW963
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfUnitMappingConeComponentFieldsW962
    (w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963 leaves)

/--
W963 records the W962 unit-witness component surface with endpoint
strict-short-exact data split into closed embedding, open map, surjectivity,
and algebraic exactness.
-/
def closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963 :
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
    "endpoint degreewise surjectivity witnesses",
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

theorem closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963_count :
    closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963.length =
      26 :=
  rfl

/-- Current checked W963 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsRouteStateW963 :
    Type where
  seed : String
  declarations : List String
  endpointStrictSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsRouteStateW963 :
    MetrizableClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsRouteStateW963
    where
  seed :=
    "w963-closed-embedding-closedness-endpoint-strict-and-unit-mapping-cone-\
      component-fields-route"
  declarations :=
    ["MetrizableWppClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldLeavesW963",
      "endpointStrictExactOfEndpointComponentFieldsW963",
      "w962LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w961LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w959LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w958LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w957LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w956LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w955LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w954LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w953PrimitiveLeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "w952LeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "concreteLeavesOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "routeDataProviderOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "directBoundedLeftCalculusOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "boundedDerivedInfinityCategoryOfEndpointStrictAndUnitMappingConeComponentFieldsW963",
      "closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963",
      "closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963_count"]
  endpointStrictSplitResult :=
    "proved: W963 assembles endpoint MetrizableLCA.strictShortExact witnesses\
      from degreewise closed-embedding, open-map, surjectivity, and algebraic\
      exactness component families"
  exactAtResult :=
    "proved: the W963 endpoint-strict and unit-mapping-cone component field\
      surface feeds the W962/W961/W959/W958/W957/W956/W955/W954/W953/W952/\
      W951/W950/W949/W948/W947/W946/W945/W944/W943/W942/W941/W940/W937/W936/\
      W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["endpoint strictShortExact witnesses replaced by explicit degreewise\
      closed-embedding, open-map, surjectivity, and algebraic-exactness fields",
      "split target primitives, raw W716 boundary propositions, raw W717\
      relation providers, raw W719 normalized fixed-target fields, raw W722\
      source-triangulation fields, W961 closed-embedding closedness fields,\
      bounded-homotopy localized right-adjoint/adjunction fields, and W962\
      unit mapping-cone component fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsInputNamesW963
  productSuccessClaimed := false

theorem currentW963ClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointStrictAndUnitMappingConeComponentFieldsRouteStateW963;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
