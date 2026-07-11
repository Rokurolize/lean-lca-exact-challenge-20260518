import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipEndpointShortExactUnitConflationWitnessPrimitiveFieldRoute

/-!
W936 feeds the W935 closed-map target-compact endpoint-short-exact route while
exposing the unit mapping-cone iso-closure witness through degreewise strict
short exact sequences in `MetrizableLCA`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

namespace Dbounded

/--
W936 primitive strict short-exact witness form of the bounded-homotopy
localized adjunction unit iso-closure witness field.
-/
abbrev boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitnessPrimitiveW936
    (boundedHomotopyLocalizedRightAdjoint :
      MorphismProperty.Localization
          ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
        BoundedComplexCategory MetrizableLCA.{0})
    (boundedHomotopyLocalizedAdjunction :
      boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
        boundedHomotopyLocalizedRightAdjoint) : Prop :=
  ∀ X : BoundedComplexCategory MetrizableLCA.{0},
    ∃ K : HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ),
      (∀ i : ℤ, MetrizableLCA.strictShortExact (K.as.sc i)) ∧
        Nonempty
          (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
              (CochainComplex.mappingCone
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                  (boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅ K)

/--
W936 converts strict short-exact unit witness data into W935's degreewise
Quillen conflation witness through the metrizable LCA exact-category instance.
-/
abbrev boundedHomotopyLocalizedEndpointShortExactUnitConflationWitnessOfStrictExactPrimitiveW936
    (boundedHomotopyLocalizedRightAdjoint :
      MorphismProperty.Localization
          ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
        BoundedComplexCategory MetrizableLCA.{0})
    (boundedHomotopyLocalizedAdjunction :
      boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
        boundedHomotopyLocalizedRightAdjoint)
    (boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitness :
      boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitnessPrimitiveW936
        boundedHomotopyLocalizedRightAdjoint
        boundedHomotopyLocalizedAdjunction) :
    boundedHomotopyLocalizedEndpointShortExactUnitConflationWitnessPrimitiveW935
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction := by
  intro X
  rcases boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitness X with ⟨K, hK, hIso⟩
  exact ⟨K, by
    intro i
    exact MetrizableLCA.quillenConflation_of_strictShortExact (hK i), hIso⟩

/--
W936 preserves W935's endpoint short-exact field while requiring the unit
mapping-cone witness as degreewise strict short exact sequences.
-/
structure MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936 :
    Type 2 where
  rightOpenBoundary :
    ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
      (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
        IsLimit cx →
          IsLimit cy →
            (∀ j : WalkingParallelPair,
              IsOpenMap (α.app j : X.obj j → Y.obj j)) →
              (∀ j : WalkingParallelPair,
                φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
                Nonempty
                  (WppLimitLcaClosedQuotientCoverData X Y α cx cy φ)
  sourcePiZeroBoundary :
    ∀ (X : WalkingParallelPair ⥤ MetrizableLCA.{0}) (cx : Cone X),
      IsLimit cx →
        let δ : X.obj WalkingParallelPair.zero ⟶ X.obj WalkingParallelPair.one :=
          X.map WalkingParallelPairHom.left - X.map WalkingParallelPairHom.right
        IsOpenMap (δ : X.obj WalkingParallelPair.zero → X.obj WalkingParallelPair.one) ∧
          MetrizableLCA.cokernelπ δ = 0
  relationPullbackProvider :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y),
      (∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
        relationPullbackPrimitiveW920 α
  targetRelationLiftsProvider :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y),
      (∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
        targetRelationLiftsPrimitiveW920 α
  targetDifferenceSurjectiveForTargetProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y
  targetCodomainCompactSpaceProvider :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y
  closedMapPi1 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi1PrimitiveW922 S
  closedMapPi2 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi2PrimitiveW922 S
  closedMapPi3 :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}),
      selectedDifferenceClosedMapPi3PrimitiveW922 S
  mappedCokernelClosedMap :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      mappedCokernelClosedMapPrimitiveW921 f
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
    ∀ (F₁ F₂ :
        (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤
          (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂
  localizationModelFixedTargetUniq :
    ∀ (F₁ F₂ :
        (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤
          (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
            WalkingParallelPair).Localization)),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂
  sourcePretriangulated :
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    ∀ (T₁ T₂ : Pretriangulated.Triangle
        (BoundedComplexCategory MetrizableLCA.{0})),
      T₁ ∈ distTriang (BoundedComplexCategory MetrizableLCA.{0}) →
      T₂ ∈ distTriang (BoundedComplexCategory MetrizableLCA.{0}) →
      ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂),
        boundedExactWeakEquivalence MetrizableLCA.{0} a →
        boundedExactWeakEquivalence MetrizableLCA.{0} b →
        T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
        ∃ (c : T₁.obj₃ ⟶ T₂.obj₃),
          ∃ (_ : boundedExactWeakEquivalence MetrizableLCA.{0} c),
            (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧
              (T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃)
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointShortExactOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → (K.sc i).ShortExact
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitness :
    boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitnessPrimitiveW936
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/-- W936 projects W935 leaves from the strict unit-witness field. -/
def w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936
    (leaves :
      MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936) :
    MetrizableWppClosedMapTargetCompactEndpointShortExactFieldLeavesW935
    where
  rightOpenBoundary := leaves.rightOpenBoundary
  sourcePiZeroBoundary := leaves.sourcePiZeroBoundary
  relationPullbackProvider := leaves.relationPullbackProvider
  targetRelationLiftsProvider := leaves.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    leaves.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider :=
    leaves.targetCodomainCompactSpaceProvider
  closedMapPi1 := leaves.closedMapPi1
  closedMapPi2 := leaves.closedMapPi2
  closedMapPi3 := leaves.closedMapPi3
  mappedCokernelClosedMap := leaves.mappedCokernelClosedMap
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
  localizationModelFixedTargetUniq := leaves.localizationModelFixedTargetUniq
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointShortExactOfExactAt := leaves.endpointShortExactOfExactAt
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointShortExactUnitConflationWitness :=
    boundedHomotopyLocalizedEndpointShortExactUnitConflationWitnessOfStrictExactPrimitiveW936
      leaves.boundedHomotopyLocalizedRightAdjoint
      leaves.boundedHomotopyLocalizedAdjunction
      leaves.boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitness

/-- W936 W733 concrete leaves after projecting W935 leaves. -/
def concreteLeavesOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936
    (leaves :
      MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetCompactEndpointShortExactFieldsW935
    (w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936 leaves)

/-- W936 W732 route data after projecting W935 leaves. -/
def routeDataProviderOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936
    (leaves :
      MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetCompactEndpointShortExactFieldsW935
    (w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936 leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936
    (leaves :
      MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetCompactEndpointShortExactFieldsW935
    (w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936 leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936
    (leaves :
      MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetCompactEndpointShortExactFieldsW935
    (w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936 leaves)

/-- W936 exposes W935's unit conflation witness as strict short-exact data. -/
def closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936 :
    List String :=
  ["raw right-open closed-quotient-cover WPP-limit boundary proposition",
    "raw source-difference cokernel-pi-zero WPP-limit boundary proposition",
    "primitive relation-pullback AddSubgroup comap equality",
    "primitive target-relation lift quantifier through the codomain component",
    "primitive target-difference preimage quantifier for every target diagram",
    "primitive target-codomain compactness filter nonbottom and point meet nonbottom\
      for every target diagram",
    "primitive selected-difference pi1 closed-set image condition",
    "primitive selected-difference pi2 closed-set image condition",
    "primitive selected-difference pi3 closed-set image condition",
    "primitive mapped explicit cokernel closed-set image condition for every morphism",
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
    "target fixed-target uniqueness quantifier for objectwise localization",
    "localization-model fixed-target uniqueness quantifier for objectwise localization",
    "raw Pretriangulated proposition on BoundedComplexCategory MetrizableLCA",
    "raw IsTriangulated proposition on BoundedComplexCategory MetrizableLCA",
    "raw bounded exact weak equivalence source-side triangle-completion proposition",
    "endpoint ExactAt incoming maps are closed embeddings",
    "endpoint ExactAt outgoing maps are open",
    "endpoint ExactAt short-exact witnesses for outgoing epi data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone iso-closure witness: degreewise strict MetrizableLCA\
      short exact sequences plus isomorphism"]

theorem closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936_count :
    closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936.length =
      39 :=
  rfl

/-- Current checked W936 state. -/
structure MetrizableClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsRouteStateW936 :
    Type where
  seed : String
  declarations : List String
  endpointShortExactFieldResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsRouteStateW936 :
    MetrizableClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsRouteStateW936
    where
  seed :=
    "w936-closed-map-target-compact-no-univ-membership-endpoint-short-exact-\
      unit-strict-exact-witness-primitive-field-route"
  declarations :=
    ["MetrizableWppClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldLeavesW936",
      "boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitnessPrimitiveW936",
      "boundedHomotopyLocalizedEndpointShortExactUnitConflationWitnessOfStrictExactPrimitiveW936",
      "w935LeavesOfEndpointShortExactUnitStrictExactWitnessFieldsW936",
      "concreteLeavesOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936",
      "routeDataProviderOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936",
      "directBoundedLeftCalculusOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936",
      "boundedDerivedInfinityCategoryOfClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsW936",
      "closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936",
      "closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936_count"]
  endpointShortExactFieldResult :=
    "proved: degreewise strict MetrizableLCA short exact sequences supply W935's\
      Quillen-conflation unit mapping-cone witness through the strict exact\
      category instance"
  exactAtResult :=
    "proved: closed-map target-compact-no-univ-membership-endpoint-short-exact-\
      unit-strict-exact-witness-primitive-field\
      endpoint-short-exact-unit-conflation-witness-primitive-field\
      target-compact-no-univ-membership-primitive-field\
      target-compact-no-principal-primitive-field\
      target-compact-outer-nonbottom-primitive-field\
      target-compact-nonbottom-primitive-field\
      target-compact-cluster-primitive-field\
      target-compact-filter-primitive-field\
      target-compact-primitive-field\
      target-surjective-primitive-field\
      selected-difference-primitive-fields\
      mapped-cokernel-primitive-fields source-raw-fields\
      triangle-completion-raw-field boundary-raw-fields relation-raw-fields\
      target-raw-fields selected-difference-fields\
      fixed-target-uniqueness-fields localized-right-adjoint-fields\
      endpoint-fields source-fields relation-fields boundary-fields\
      component-fields mapped-cokernel-field fields feed the W935/W934/W933/W932/W931/W930\
      stable ExactAt route"
  refinedInputs :=
    ["unit mapping-cone degreewise Quillen conflation witness exposed as\
      degreewise strict MetrizableLCA short exact sequence data"]
  remainingInputs :=
    closedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsInputNamesW936
  productSuccessClaimed := false

theorem currentW936ClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetCompactEndpointShortExactUnitStrictExactWitnessFieldsRouteStateW936;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
