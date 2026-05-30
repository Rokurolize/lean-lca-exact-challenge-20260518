import LeanLCAExactChallenge.Derived.EndpointStrictTopologyFieldsComparisonStableExactAtRoute

/-!
W887 feeds the W886 endpoint-fields comparison stable-ExactAt route from
explicit localized-right-adjoint fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W887 replaces the bundled W721 localized-right-adjoint data provider by its
three explicit fields.
-/
structure MetrizableWppLocalizedRightAdjointFieldLeavesW887 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
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

/-- W887 assembles the W721 localized-right-adjoint provider from fields. -/
def localizedRightAdjointDataOfFieldsW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    MetrizableWppLocalizedRightAdjointDataProviderW721
    where
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedUnitMem :=
    leaves.boundedHomotopyLocalizedUnitMem

/-- W887 assembles the W886 leaves from explicit localized-right-adjoint fields. -/
def endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    MetrizableWppEndpointStrictTopologyFieldLeavesW886
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointForgetPreservesHomology :=
    leaves.endpointForgetPreservesHomology
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointEpiOfExactAt := leaves.endpointEpiOfExactAt
  localizedRightAdjointData :=
    localizedRightAdjointDataOfFieldsW887 leaves

/-- W887 W733 concrete leaves from explicit localized-right-adjoint fields. -/
def concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfEndpointFieldsComparisonW886
    (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887 leaves)

/-- W887 W732 route data from explicit localized-right-adjoint fields. -/
def routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfEndpointFieldsComparisonW886
    (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887 leaves)

/--
W887 direct bounded left calculus through the latest W886 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
    (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887 leaves)

/--
W887 bounded derived infinity-category package through the latest W886
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887
    (leaves : MetrizableWppLocalizedRightAdjointFieldLeavesW887) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
    (endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887 leaves)

/-- W887 exposes localized-right-adjoint fields needed by W886. -/
def localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
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

theorem localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887_count :
    localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887.length =
      15 :=
  rfl

/-- Current checked W887 state. -/
structure MetrizableLocalizedRightAdjointFieldsComparisonStableExactAtRouteStateW887 :
    Type where
  seed : String
  declarations : List String
  localizedRightAdjointAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedRightAdjointFieldsComparisonStableExactAtRouteStateW887 :
    MetrizableLocalizedRightAdjointFieldsComparisonStableExactAtRouteStateW887
    where
  seed :=
    "w887-localized-right-adjoint-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppLocalizedRightAdjointFieldLeavesW887",
      "localizedRightAdjointDataOfFieldsW887",
      "endpointStrictTopologyFieldLeavesOfLocalizedRightAdjointFieldsW887",
      "concreteLeavesOfLocalizedRightAdjointFieldsComparisonW887",
      "routeDataProviderOfLocalizedRightAdjointFieldsComparisonW887",
      "directBoundedLeftCalculusOfLocalizedRightAdjointFieldsComparisonStableExactAtW887",
      "boundedDerivedInfinityCategoryOfLocalizedRightAdjointFieldsComparisonStableExactAtW887",
      "localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887",
      "localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887_count"]
  localizedRightAdjointAssemblyResult :=
    "proved: explicit localized-right-adjoint fields assemble the W721 provider\
      consumed by the W886 comparison stable ExactAt route"
  exactAtResult :=
    "proved: explicit localized-right-adjoint fields feed the W886 stable\
      ExactAt route"
  replacedInputs :=
    ["W721 localized-right-adjoint data provider"]
  remainingInputs :=
    localizedRightAdjointFieldsComparisonStableExactAtInputNamesW887
  productSuccessClaimed := false

theorem currentW887LocalizedRightAdjointFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedRightAdjointFieldsComparisonStableExactAtRouteStateW887;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
