import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonProductRoute

/-!
W1617 feeds W1616 after replacing the W719, W722, and W720 bundled providers
with their structural fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-!
W1617 closed-map branch data with normalized fixed-target, source
triangulation, and endpoint strict-topology providers split into fields.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617 :
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
  endpointForgetPreservesHomology :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointEpiOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedUnitMem :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      boundedHomotopyLocalizedAdjunction.unit

/-!
W1617 closed-embedding branch data with normalized fixed-target, source
triangulation, and endpoint strict-topology providers split into fields.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617 :
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
  endpointForgetPreservesHomology :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointEpiOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedUnitMem :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      boundedHomotopyLocalizedAdjunction.unit

/-! W1617 closed-map structural fields converted to W1616 split-field data. -/
def closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616
    where
  rightOpenBoundary := data.rightOpenBoundary
  sourcePiZeroBoundary := data.sourcePiZeroBoundary
  relationPullbackProvider := data.relationPullbackProvider
  targetRelationLiftsProvider := data.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    data.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider := data.targetCodomainCompactSpaceProvider
  globalClosedMapComponents := data.globalClosedMapComponents
  mappedCokernelClosedMapProvider := data.mappedCokernelClosedMapProvider
  normalizedFixedTargetData :=
    { normalizedLiftBlueprint := data.normalizedLiftBlueprint
      targetFixedTargetUniq := data.targetFixedTargetUniq
      localizationModelFixedTargetUniq := data.localizationModelFixedTargetUniq }
  sourceTriangulationData :=
    { sourcePretriangulated := data.sourcePretriangulated
      sourceTriangulated := data.sourceTriangulated
      triangleCompletion := data.triangleCompletion }
  endpointStrictTopologyData :=
    { endpointForgetPreservesHomology := data.endpointForgetPreservesHomology
      endpointClosedEmbedding := data.endpointClosedEmbedding
      endpointOpenMap := data.endpointOpenMap
      endpointEpiOfExactAt := data.endpointEpiOfExactAt }
  boundedHomotopyLocalizedRightAdjoint :=
    data.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    data.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedUnitMem :=
    data.boundedHomotopyLocalizedUnitMem

/-!
W1617 closed-embedding structural fields converted to W1616 split-field data.
-/
def closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616
    where
  rightOpenBoundary := data.rightOpenBoundary
  sourcePiZeroBoundary := data.sourcePiZeroBoundary
  relationPullbackProvider := data.relationPullbackProvider
  targetRelationLiftsProvider := data.targetRelationLiftsProvider
  targetDifferenceSurjectiveForTargetProvider :=
    data.targetDifferenceSurjectiveForTargetProvider
  targetCodomainCompactSpaceProvider := data.targetCodomainCompactSpaceProvider
  globalClosedEmbeddingComponents := data.globalClosedEmbeddingComponents
  mappedCokernelClosedEmbeddingProvider :=
    data.mappedCokernelClosedEmbeddingProvider
  normalizedFixedTargetData :=
    { normalizedLiftBlueprint := data.normalizedLiftBlueprint
      targetFixedTargetUniq := data.targetFixedTargetUniq
      localizationModelFixedTargetUniq := data.localizationModelFixedTargetUniq }
  sourceTriangulationData :=
    { sourcePretriangulated := data.sourcePretriangulated
      sourceTriangulated := data.sourceTriangulated
      triangleCompletion := data.triangleCompletion }
  endpointStrictTopologyData :=
    { endpointForgetPreservesHomology := data.endpointForgetPreservesHomology
      endpointClosedEmbedding := data.endpointClosedEmbedding
      endpointOpenMap := data.endpointOpenMap
      endpointEpiOfExactAt := data.endpointEpiOfExactAt }
  boundedHomotopyLocalizedRightAdjoint :=
    data.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    data.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedUnitMem :=
    data.boundedHomotopyLocalizedUnitMem

/-! W1617 closed-map product evidence through W1616. -/
noncomputable def
    productEvidenceOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617 data)

/-! W1617 closed-embedding product evidence through W1616. -/
noncomputable def
    productEvidenceOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

/-! W1617 closed-map direct finite-shape stable data through W1616. -/
noncomputable def
    directFiniteShapeStableDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617 data)

/-! W1617 closed-embedding direct finite-shape stable data through W1616. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

/-! W1617 closed-map stable-boundary inputs through W1616. -/
noncomputable def
    stableBoundaryInputsOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617 data)

/-! W1617 closed-embedding stable-boundary inputs through W1616. -/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

/-! W1617 closed-map accepted stable evidence through W1616. -/
noncomputable def
    acceptedStableOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617 data)

/-! W1617 closed-embedding accepted stable evidence through W1616. -/
noncomputable def
    acceptedStableOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

/-! W1617 closed-map bounded derived package through W1616. -/
noncomputable def boundedDerivedOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617 data)

/-! W1617 closed-embedding bounded derived package through W1616. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

/-!
Top-level input names for the W1617 structural-field selected-cochain
comparison route.
-/
def boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617 :
    List String :=
  ["right-open closed-quotient-cover boundary field",
    "source-difference cokernel pi-zero boundary field",
    "closed natural transformation relation-pullback provider",
    "closed natural transformation target-relation-lift provider",
    "target-difference surjectivity for every target diagram",
    "target-codomain compactness for every target diagram",
    "selected-difference closed-map or closed-embedding component provider",
    "matching mapped explicit cokernel closedness provider",
    "normalized strict-representative lift blueprint",
    "target fixed-target uniqueness obligation",
    "localization-model fixed-target uniqueness obligation",
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "forgetful functor preserves homology for MetrizableLCA",
    "endpoint ExactAt incoming maps are closed embeddings",
    "endpoint ExactAt outgoing maps are open",
    "endpoint ExactAt outgoing maps are epis",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit membership in boundedHomotopyExactWeakEquivalence"]

theorem
    boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617_count :
    boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617.length =
      21 :=
  rfl

/-!
Current checked W1617 structural-field selected-cochain comparison route state.
-/
structure
    MetrizableBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRouteStateW1617 :
    Type where
  seed : String
  declarations : List String
  structuralFieldAssemblyResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1617 state: structural fields assemble W719, W722, and W720
providers before feeding W1616.
-/
def currentMetrizableBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRouteStateW1617 :
    MetrizableBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRouteStateW1617
    where
  seed :=
    "w1617-boundary-source-pi-zero-structural-fields-selected-cochain-comparison-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617",
      "closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617",
      "closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617",
      "productEvidenceOfClosedMapStructuralFieldsSelectedCochainComparisonW1617",
      "productEvidenceOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617",
      "directFiniteShapeStableDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617",
      "directFiniteShapeStableDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617",
      "stableBoundaryInputsOfClosedMapStructuralFieldsSelectedCochainComparisonW1617",
      "stableBoundaryInputsOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617",
      "acceptedStableOfClosedMapStructuralFieldsSelectedCochainComparisonW1617",
      "acceptedStableOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617",
      "boundedDerivedOfClosedMapStructuralFieldsSelectedCochainComparisonW1617",
      "boundedDerivedOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617",
      "boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617",
      "boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617_count"]
  structuralFieldAssemblyResult :=
    "proved: W719 normalized fixed-target data, W722 source triangulation data,\
      and W720 endpoint strict-topology data are assembled from structural\
      fields before feeding W1616"
  closedMapResult :=
    "proved: closed-map structural-field branch data feeds the W1616 selected\
      cochain comparison surface"
  closedEmbeddingResult :=
    "proved: closed-embedding structural-field branch data feeds the W1616\
      selected cochain comparison surface"
  replacedInputs :=
    ["W719 normalized fixed-target data provider",
      "W722 source triangulation and triangle-completion data provider",
      "W720 endpoint strict-topology data provider"]
  remainingInputs :=
    boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617 ++
      ["construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem
    currentW1617BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRouteStateW1617;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
