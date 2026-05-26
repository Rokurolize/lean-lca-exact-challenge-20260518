import LeanLCAExactChallenge.Derived.SourceTriangulationComparisonStableExactAtRoute

/-!
W885 feeds the W884 source-triangulation comparison stable-ExactAt route from
explicit source-triangulation fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W885 replaces the bundled W722 source-triangulation provider by its three
explicit fields.
-/
structure MetrizableWppSourceTriangulationFieldComparisonLeavesW885 :
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
  endpointStrictTopologyData :
    MetrizableWppEndpointStrictTopologyDataProviderW720
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W885 assembles the W722 source-triangulation provider from explicit fields. -/
def sourceTriangulationDataOfFieldsW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    MetrizableWppSourceTriangulationDataProviderW722
    where
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion

/-- W885 assembles the W884 leaves from explicit source-triangulation fields. -/
def sourceTriangulationLeavesOfFieldsW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    MetrizableWppSourceTriangulationComparisonLeavesW884
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := sourceTriangulationDataOfFieldsW885 leaves
  endpointStrictTopologyData := leaves.endpointStrictTopologyData
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W885 W733 concrete leaves from explicit source-triangulation fields. -/
def concreteLeavesOfSourceTriangulationFieldsComparisonW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfSourceTriangulationComparisonW884
    (sourceTriangulationLeavesOfFieldsW885 leaves)

/-- W885 W732 route data from explicit source-triangulation fields. -/
def routeDataProviderOfSourceTriangulationFieldsComparisonW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfSourceTriangulationComparisonW884
    (sourceTriangulationLeavesOfFieldsW885 leaves)

/--
W885 direct bounded left calculus through the latest W884 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
    (sourceTriangulationLeavesOfFieldsW885 leaves)

/--
W885 bounded derived infinity-category package through the latest W884
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
    (leaves : MetrizableWppSourceTriangulationFieldComparisonLeavesW885) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
    (sourceTriangulationLeavesOfFieldsW885 leaves)

/-- W885 exposes the explicit fields needed by W884. -/
def sourceTriangulationFieldsComparisonStableExactAtInputNamesW885 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "endpoint strict-topology data provider",
    "bounded homotopy localized-right-adjoint data provider"]

theorem sourceTriangulationFieldsComparisonStableExactAtInputNamesW885_count :
    sourceTriangulationFieldsComparisonStableExactAtInputNamesW885.length =
      10 :=
  rfl

/-- Current checked W885 state. -/
structure MetrizableSourceTriangulationFieldsComparisonStableExactAtRouteStateW885 :
    Type where
  seed : String
  declarations : List String
  sourceTriangulationAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSourceTriangulationFieldsComparisonStableExactAtRouteStateW885 :
    MetrizableSourceTriangulationFieldsComparisonStableExactAtRouteStateW885
    where
  seed := "w885-source-triangulation-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppSourceTriangulationFieldComparisonLeavesW885",
      "sourceTriangulationDataOfFieldsW885",
      "sourceTriangulationLeavesOfFieldsW885",
      "concreteLeavesOfSourceTriangulationFieldsComparisonW885",
      "routeDataProviderOfSourceTriangulationFieldsComparisonW885",
      "directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885",
      "boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885",
      "sourceTriangulationFieldsComparisonStableExactAtInputNamesW885",
      "sourceTriangulationFieldsComparisonStableExactAtInputNamesW885_count"]
  sourceTriangulationAssemblyResult :=
    "proved: explicit source pretriangulated, triangulated, and triangle\
      completion fields assemble the W722 provider consumed by W884"
  exactAtResult :=
    "proved: explicit source-triangulation fields feed the W884 stable ExactAt route"
  replacedInputs :=
    ["W722 source triangulation and triangle-completion data provider"]
  remainingInputs :=
    sourceTriangulationFieldsComparisonStableExactAtInputNamesW885
  productSuccessClaimed := false

theorem
    currentW885SourceTriangulationFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableSourceTriangulationFieldsComparisonStableExactAtRouteStateW885;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
