import LeanLCAExactChallenge.Derived.ClosedMapEndpointHomologyFreeComparisonStableExactAtRoute

/-!
W900 feeds the W899 closed-map endpoint-homology-free comparison stable-ExactAt
route while bundling the endpoint ExactAt facts and bounded-homotopy localized
right-adjoint data through the existing W856 and W721 providers.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W900 projects endpoint closed-embedding facts from the W856 endpoint-facts provider. -/
def endpointClosedEmbeddingOfEndpointFactsW900
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂) :=
  endpointFacts.endpointClosedEmbedding

/-- W900 projects endpoint open-map facts from the W856 endpoint-facts provider. -/
def endpointOpenMapOfEndpointFactsW900
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) :=
  endpointFacts.endpointOpenMap

/-- W900 projects endpoint epi facts from the W856 endpoint-facts provider. -/
@[reducible]
def endpointEpiOfExactAtOfEndpointFactsW900
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g) :=
  endpointFacts.endpointEpiOfExactAt

/-- W900 projects the bounded homotopy localized right adjoint from W721 data. -/
def boundedHomotopyLocalizedRightAdjointOfLocalizedRightAdjointW900
    (localizedData : MetrizableWppLocalizedRightAdjointDataProviderW721) :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  boundedHomotopyLocalizedRightAdjoint_of_localizedRightAdjointDataW721
    localizedData

/-- W900 projects the bounded homotopy localized adjunction from W721 data. -/
def boundedHomotopyLocalizedAdjunctionOfLocalizedRightAdjointW900
    (localizedData : MetrizableWppLocalizedRightAdjointDataProviderW721) :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjointOfLocalizedRightAdjointW900
        localizedData :=
  boundedHomotopyLocalizedAdjunction_of_localizedRightAdjointDataW721
    localizedData

/-- W900 projects bounded-homotopy unit membership from W721 data. -/
def boundedHomotopyLocalizedUnitMemOfLocalizedRightAdjointW900
    (localizedData : MetrizableWppLocalizedRightAdjointDataProviderW721) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      (boundedHomotopyLocalizedAdjunctionOfLocalizedRightAdjointW900
        localizedData).unit :=
  boundedHomotopyLocalizedUnitMem_of_localizedRightAdjointDataW721
    localizedData

/--
W900 replaces W899's three endpoint topology fact leaves and three
bounded-homotopy localized-right-adjoint leaves with the existing homology-free
W856 endpoint-facts provider and W721 localized-right-adjoint provider.
-/
structure MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900 :
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
    TargetDifferenceSurjectiveForTargetProviderW713
  targetCodomainCompactSpaceProvider :
    TargetCodomainCompactSpaceProviderW601
  globalClosedMapComponents :
    SelectedDifferenceClosedMapDiagramComponentProviderW718
  mappedCokernelClosedMapProvider :
    MappedExplicitCokernelClosedMapProviderW519
  strictPreimageZeroSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  strictPreimageOneSrc :
    ∀ (_Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      BoundedComplexCategory MetrizableLCA.{0}
  strictPreimageZeroIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (strictPreimageZeroSrc Y) ≅
        Y.obj WalkingParallelPair.zero
  strictPreimageOneIso :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).obj (strictPreimageOneSrc Y) ≅
        Y.obj WalkingParallelPair.one
  strictPreimageLeftSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      strictPreimageZeroSrc Y ⟶ strictPreimageOneSrc Y
  strictPreimageRightSrc :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      strictPreimageZeroSrc Y ⟶ strictPreimageOneSrc Y
  strictPreimageLeftFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageLeftSrc Y) =
        (strictPreimageZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.left ≫
            (strictPreimageOneIso Y).inv
  strictPreimageRightFac :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageRightSrc Y) =
        (strictPreimageZeroIso Y).hom ≫
          Y.map WalkingParallelPairHom.right ≫
            (strictPreimageOneIso Y).inv
  strictPreimageZeroMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      strictPreimageZeroSrc Y ⟶ strictPreimageZeroSrc Z
  strictPreimageOneMap :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (_τ : Y ⟶ Z),
      strictPreimageOneSrc Y ⟶ strictPreimageOneSrc Z
  strictPreimageZeroMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageZeroMap τ) =
        (strictPreimageZeroIso Y).hom ≫
          τ.app WalkingParallelPair.zero ≫
            (strictPreimageZeroIso Z).inv
  strictPreimageOneMapFac :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      (Dbounded.localization MetrizableLCA.{0}).map
          (strictPreimageOneMap τ) =
        (strictPreimageOneIso Y).hom ≫
          τ.app WalkingParallelPair.one ≫
            (strictPreimageOneIso Z).inv
  strictPreimageLeftNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      strictPreimageLeftSrc Y ≫ strictPreimageOneMap τ =
        strictPreimageZeroMap τ ≫ strictPreimageLeftSrc Z
  strictPreimageRightNaturality :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      strictPreimageRightSrc Y ≫ strictPreimageOneMap τ =
        strictPreimageZeroMap τ ≫ strictPreimageRightSrc Z
  strictRepresentativeMapId :
    ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality (𝟙 Y)).natTrans =
        𝟙 (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac Y).diagram
  strictRepresentativeMapComp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality (τ ≫ σ)).natTrans =
        (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality τ).natTrans ≫
            (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
              strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
              strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
              strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
              strictPreimageZeroMapFac strictPreimageOneMapFac
              strictPreimageLeftNaturality strictPreimageRightNaturality σ).natTrans
  sourceImageObjectNormalization :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (strictPreimageObjectDataOfFieldsW891 strictPreimageZeroSrc
        strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
        strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
        strictPreimageRightFac
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  sourceImageMapNormalization :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (strictPreimageMapDataOfFieldsW892 strictPreimageZeroSrc
          strictPreimageOneSrc strictPreimageZeroIso strictPreimageOneIso
          strictPreimageLeftSrc strictPreimageRightSrc strictPreimageLeftFac
          strictPreimageRightFac strictPreimageZeroMap strictPreimageOneMap
          strictPreimageZeroMapFac strictPreimageOneMapFac
          strictPreimageLeftNaturality strictPreimageRightNaturality
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (sourceImageObjectNormalization Y) =
      eqToHom (sourceImageObjectNormalization X) ≫ τ
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
  endpointTopologyFacts :
    MetrizableWppEndpointTopologyFactsProviderW856
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W900 projects W899 leaves from the W856 and W721 provider bundles. -/
def closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    MetrizableWppClosedMapEndpointHomologyFreeLeavesW899
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  globalClosedMapComponents := leaves.globalClosedMapComponents
  mappedCokernelClosedMapProvider :=
    leaves.mappedCokernelClosedMapProvider
  strictPreimageZeroSrc := leaves.strictPreimageZeroSrc
  strictPreimageOneSrc := leaves.strictPreimageOneSrc
  strictPreimageZeroIso := leaves.strictPreimageZeroIso
  strictPreimageOneIso := leaves.strictPreimageOneIso
  strictPreimageLeftSrc := leaves.strictPreimageLeftSrc
  strictPreimageRightSrc := leaves.strictPreimageRightSrc
  strictPreimageLeftFac := leaves.strictPreimageLeftFac
  strictPreimageRightFac := leaves.strictPreimageRightFac
  strictPreimageZeroMap := leaves.strictPreimageZeroMap
  strictPreimageOneMap := leaves.strictPreimageOneMap
  strictPreimageZeroMapFac := leaves.strictPreimageZeroMapFac
  strictPreimageOneMapFac := leaves.strictPreimageOneMapFac
  strictPreimageLeftNaturality := leaves.strictPreimageLeftNaturality
  strictPreimageRightNaturality := leaves.strictPreimageRightNaturality
  strictRepresentativeMapId := leaves.strictRepresentativeMapId
  strictRepresentativeMapComp := leaves.strictRepresentativeMapComp
  sourceImageObjectNormalization :=
    leaves.sourceImageObjectNormalization
  sourceImageMapNormalization :=
    leaves.sourceImageMapNormalization
  targetFixedTargetUniq := leaves.targetFixedTargetUniq
  localizationModelFixedTargetUniq :=
    leaves.localizationModelFixedTargetUniq
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointClosedEmbedding :=
    endpointClosedEmbeddingOfEndpointFactsW900 leaves.endpointTopologyFacts
  endpointOpenMap :=
    endpointOpenMapOfEndpointFactsW900 leaves.endpointTopologyFacts
  endpointEpiOfExactAt :=
    endpointEpiOfExactAtOfEndpointFactsW900 leaves.endpointTopologyFacts
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedRightAdjointW900
      leaves.localizedRightAdjointData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedRightAdjointW900
      leaves.localizedRightAdjointData
  boundedHomotopyLocalizedUnitMem :=
    boundedHomotopyLocalizedUnitMemOfLocalizedRightAdjointW900
      leaves.localizedRightAdjointData

/-- W900 W733 concrete leaves after projecting W899 leaves. -/
def concreteLeavesOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapEndpointHomologyFreeComparisonW899
    (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
      leaves)

/-- W900 W732 route data after projecting W899 leaves. -/
def routeDataProviderOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapEndpointHomologyFreeComparisonW899
    (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
      leaves)

/--
W900 direct bounded left calculus through the latest W899 comparison stable
ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfClosedMapEndpointLocalizedAdjointW900
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
    (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
      leaves)

/--
W900 bounded derived infinity-category package through the latest W899
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapEndpointLocalizedAdjointW900
    (leaves : MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapEndpointHomologyFreeComparisonStableExactAtW899
    (closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900
      leaves)

/-- W900 exposes W899's fields with endpoint facts and localized-right-adjoint data bundled. -/
def closedMapEndpointLocalizedAdjointInputNamesW900 :
    List String :=
  ["WPP right-open quotient-cover boundary data",
    "WPP source-pi-zero boundary data",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "target-difference surjectivity provider",
    "target-codomain compactness provider",
    "selected-difference closed-map diagram component provider",
    "W519 mapped explicit cokernel closed-map provider",
    "strict preimage zero object source for every WalkingParallelPair diagram",
    "strict preimage one object source for every WalkingParallelPair diagram",
    "strict preimage zero object localization isomorphism",
    "strict preimage one object localization isomorphism",
    "strict preimage left source map",
    "strict preimage right source map",
    "strict preimage left localization factorization",
    "strict preimage right localization factorization",
    "strict preimage zero component map for every WalkingParallelPair morphism",
    "strict preimage one component map for every WalkingParallelPair morphism",
    "strict preimage zero component map factorization",
    "strict preimage one component map factorization",
    "strict preimage left naturality square",
    "strict preimage right naturality square",
    "strict-representative lift identity coherence",
    "strict-representative lift composition coherence",
    "source-image object normalization for the strict-representative lift",
    "source-image map normalization for the strict-representative lift",
    "target fixed-target uniqueness obligation",
    "localization-model fixed-target uniqueness obligation",
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "W856 endpoint topology facts provider",
    "W721 bounded homotopy localized right-adjoint data provider"]

theorem closedMapEndpointLocalizedAdjointInputNamesW900_count :
    closedMapEndpointLocalizedAdjointInputNamesW900.length =
      33 :=
  rfl

/-- Current checked W900 state. -/
structure
    MetrizableClosedMapEndpointLocalizedAdjointRouteStateW900 :
    Type where
  seed : String
  declarations : List String
  endpointFactsResult : String
  localizedRightAdjointResult : String
  exactAtResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def
    currentMetrizableClosedMapEndpointLocalizedAdjointRouteStateW900 :
    MetrizableClosedMapEndpointLocalizedAdjointRouteStateW900
    where
  seed :=
    "w900-closed-map-endpoint-facts-localized-right-adjoint-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppClosedMapEndpointFactsLocalizedRightAdjointLeavesW900",
      "endpointClosedEmbeddingOfEndpointFactsW900",
      "endpointOpenMapOfEndpointFactsW900",
      "endpointEpiOfExactAtOfEndpointFactsW900",
      "boundedHomotopyLocalizedRightAdjointOfLocalizedRightAdjointW900",
      "boundedHomotopyLocalizedAdjunctionOfLocalizedRightAdjointW900",
      "boundedHomotopyLocalizedUnitMemOfLocalizedRightAdjointW900",
      "closedMapEndpointHomologyFreeLeavesOfEndpointFactsLocalizedRightAdjointW900",
      "concreteLeavesOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900",
      "routeDataProviderOfClosedMapEndpointFactsLocalizedRightAdjointComparisonW900",
      "directBoundedLeftCalculusOfClosedMapEndpointLocalizedAdjointW900",
      "boundedDerivedInfinityCategoryOfClosedMapEndpointLocalizedAdjointW900",
      "closedMapEndpointLocalizedAdjointInputNamesW900",
      "closedMapEndpointLocalizedAdjointInputNamesW900_count"]
  endpointFactsResult :=
    "proved: W856 endpoint topology facts provider supplies the three W899 endpoint\
      ExactAt fact fields without adding endpoint forgetful homology preservation"
  localizedRightAdjointResult :=
    "proved: W721 localized-right-adjoint data supplies the three W899 bounded\
      homotopy localized-right-adjoint fields"
  exactAtResult :=
    "proved: closed-map endpoint-facts localized-right-adjoint fields feed the\
      W899 stable ExactAt route"
  removedInputs :=
    ["endpoint ExactAt incoming maps are closed embeddings",
      "endpoint ExactAt outgoing maps are open",
      "endpoint ExactAt outgoing maps are epis",
      "right adjoint to the bounded homotopy localized Verdier functor",
      "adjunction for the bounded homotopy localized Verdier functor",
      "unit membership in boundedHomotopyExactWeakEquivalence"]
  remainingInputs :=
    closedMapEndpointLocalizedAdjointInputNamesW900
  productSuccessClaimed := false

theorem
    currentW900ClosedMapEndpointLocalizedAdjointRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapEndpointLocalizedAdjointRouteStateW900;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
