import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute

/-!
W962 feeds the W961 closed-embedding closedness route while replacing its single
W939 unit mapping-cone component witness with explicit model, degreewise
component, and mapping-cone isomorphism fields.
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

/-- W962 names the explicit model chosen for each unit mapping cone. -/
abbrev UnitMappingConeModelW962 :=
  BoundedComplexCategory MetrizableLCA.{0} →
    HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)

/--
W962 preserves the W961 field surface while splitting the W939 unit
mapping-cone strict-exact component witness into its concrete model and
component witnesses.
-/
structure MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962 :
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
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
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

/-- W962 assembles the W939 unit component witness from explicit component fields. -/
def boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      leaves.boundedHomotopyLocalizedRightAdjoint
      leaves.boundedHomotopyLocalizedAdjunction := by
  intro X
  exact
    ⟨leaves.unitMappingConeModel X,
      leaves.unitMappingConeClosedEmbedding X,
      leaves.unitMappingConeOpenMap X,
      leaves.unitMappingConeSurjective X,
      leaves.unitMappingConeAlgebraicExact X,
      leaves.unitMappingConeIso X⟩

/-- W962 builds the W961 leaves consumed by the closed-embedding closedness route. -/
def w961LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW961
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
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfUnitMappingConeComponentFieldsW962
      leaves

/-- W962 constructs W959 leaves through W961. -/
def w959LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW959 :=
  w959LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W958 leaves through W961/W959. -/
def w958LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW958 :=
  w958LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W957 leaves through W961/W959/W958. -/
def w957LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapRawBoundaryRelationFieldsSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW957 :=
  w957LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W956 leaves through W961/W959/W958/W957. -/
def w956LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapRawBoundarySplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW956 :=
  w956LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W955 leaves through W961/W959/W958/W957/W956. -/
def w955LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapBoundaryRelationSplitTargetNoUnivClosednessNormalizedSourceEndpointUnitComponentsPrimitiveFieldLeavesW955 :=
  w955LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W954 leaves through W961/W959/W958/W957/W956/W955. -/
def w954LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944 :=
  w954LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W953 primitive leaves through W961/W959/W958/W957/W956/W955/W954. -/
def w953PrimitiveLeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :=
  w953PrimitiveLeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 constructs W952 leaves through W961/W959/W958/W957/W956/W955/W954/W953. -/
def w952LeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFieldLeavesW952 :=
  w952LeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 W733 concrete leaves after constructing W961 leaves. -/
def concreteLeavesOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/-- W962 W732 route data after constructing W961 leaves. -/
def routeDataProviderOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

theorem directBoundedLeftCalculusOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

noncomputable def boundedDerivedInfinityCategoryOfUnitMappingConeComponentFieldsW962
    (leaves :
      MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsW961
    (w961LeavesOfUnitMappingConeComponentFieldsW962 leaves)

/--
W962 records the W961 closed-embedding closedness surface with the W939 unit
mapping-cone witness split into an explicit model, four component witnesses,
and the mapping-cone isomorphism witness.
-/
def closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962 :
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
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise surjectivity components",
    "unit mapping-cone degreewise algebraic exactness components",
    "unit mapping-cone isomorphism from the adjunction-unit mapping cone to the\
      chosen model"]

theorem closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962_count :
    closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962.length =
      23 :=
  rfl

/-- Current checked W962 state. -/
structure MetrizableClosedEmbeddingClosednessUnitMappingConeComponentFieldsRouteStateW962 :
    Type where
  seed : String
  declarations : List String
  unitWitnessSplitResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessUnitMappingConeComponentFieldsRouteStateW962 :
    MetrizableClosedEmbeddingClosednessUnitMappingConeComponentFieldsRouteStateW962
    where
  seed :=
    "w962-closed-embedding-closedness-unit-mapping-cone-component-fields-route"
  declarations :=
    ["UnitMappingConeModelW962",
      "MetrizableWppClosedEmbeddingClosednessUnitMappingConeComponentFieldLeavesW962",
      "boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfUnitMappingConeComponentFieldsW962",
      "w961LeavesOfUnitMappingConeComponentFieldsW962",
      "w959LeavesOfUnitMappingConeComponentFieldsW962",
      "w958LeavesOfUnitMappingConeComponentFieldsW962",
      "w957LeavesOfUnitMappingConeComponentFieldsW962",
      "w956LeavesOfUnitMappingConeComponentFieldsW962",
      "w955LeavesOfUnitMappingConeComponentFieldsW962",
      "w954LeavesOfUnitMappingConeComponentFieldsW962",
      "w953PrimitiveLeavesOfUnitMappingConeComponentFieldsW962",
      "w952LeavesOfUnitMappingConeComponentFieldsW962",
      "concreteLeavesOfUnitMappingConeComponentFieldsW962",
      "routeDataProviderOfUnitMappingConeComponentFieldsW962",
      "directBoundedLeftCalculusOfUnitMappingConeComponentFieldsW962",
      "boundedDerivedInfinityCategoryOfUnitMappingConeComponentFieldsW962",
      "closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962",
      "closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962_count"]
  unitWitnessSplitResult :=
    "proved: W962 assembles the W939 unit mapping-cone component witness from\
      an explicit homotopy-category model, closed-embedding/open-map/\
      surjectivity/algebraic-exactness component families, and the mapping-cone\
      isomorphism family"
  exactAtResult :=
    "proved: the W962 unit-mapping-cone component field surface feeds the\
      W961/W959/W958/W957/W956/W955/W954/W953/W952/W951/W950/W949/W948/W947/\
      W946/W945/W944/W943/W942/W941/W940/W937/W936/W935/W934/W933/W932/W931/\
      W930 stable ExactAt route"
  refinedInputs :=
    ["W939 unit mapping-cone component witness replaced by explicit model,\
      degreewise closed-embedding, open-map, surjectivity, algebraic exactness,\
      and isomorphism fields",
      "endpoint strict-exact witnesses, split target primitives, raw W716\
      boundary propositions, raw W717 relation providers, raw W719 normalized\
      fixed-target fields, raw W722 source-triangulation fields, W961\
      closed-embedding closedness fields, and bounded-homotopy localized\
      right-adjoint/adjunction fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessUnitMappingConeComponentFieldsInputNamesW962
  productSuccessClaimed := false

theorem currentW962ClosedEmbeddingClosednessUnitMappingConeComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessUnitMappingConeComponentFieldsRouteStateW962;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
