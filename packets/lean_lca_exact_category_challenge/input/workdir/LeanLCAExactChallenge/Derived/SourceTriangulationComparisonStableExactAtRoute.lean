import LeanLCAExactChallenge.Derived.W733ConcreteLeavesComparisonConcreteLeavesStableExactAtRoute
import LeanLCAExactChallenge.Derived.RouteDataProviderFromComparisonBijectivity

/-!
W884 feeds the W883 comparison concrete-leaves stable-ExactAt route from
source-triangulation leaves.  The W821/W855 homology theorem supplies the
category-homology part of the W733 source-homological leaf.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W884 replaces the W733 source-homological-triangulation leaf by the strictly
smaller source-triangulation leaf; W855 supplies the homology provider.
-/
structure MetrizableWppSourceTriangulationComparisonLeavesW884 :
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
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictTopologyData :
    MetrizableWppEndpointStrictTopologyDataProviderW720
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W884 constructs the W733 source-homological leaf from source triangulation. -/
def sourceHomologicalTriangulationDataOfSourceTriangulationW884
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    MetrizableWppSourceHomologicalTriangulationDataProviderW724 :=
  sourceHomologicalTriangulationDataOfComparisonBijectivityW855
    leaves.sourceTriangulationData

/-- W884 assembles the W733 concrete leaves consumed by W883. -/
def concreteLeavesOfSourceTriangulationComparisonW884
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceHomologicalTriangulationData :=
    sourceHomologicalTriangulationDataOfSourceTriangulationW884 leaves
  endpointStrictTopologyData := leaves.endpointStrictTopologyData
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W884 W732 route data from source-triangulation leaves. -/
def routeDataProviderOfSourceTriangulationComparisonW884
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfConcreteLeavesForW883
    (concreteLeavesOfSourceTriangulationComparisonW884 leaves)

/--
W884 direct bounded left calculus through the latest W883 comparison
concrete-leaves stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfConcreteLeavesComparisonStableExactAtW883
    (concreteLeavesOfSourceTriangulationComparisonW884 leaves)

/--
W884 bounded derived infinity-category package through the latest W883
comparison concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884
    (leaves : MetrizableWppSourceTriangulationComparisonLeavesW884) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfConcreteLeavesComparisonStableExactAtW883
    (concreteLeavesOfSourceTriangulationComparisonW884 leaves)

/-- W884 exposes W733 leaves with source triangulation in place of homological data. -/
def sourceTriangulationComparisonStableExactAtInputNamesW884 : List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "endpoint strict-topology data provider",
    "bounded homotopy localized-right-adjoint data provider"]

theorem sourceTriangulationComparisonStableExactAtInputNamesW884_count :
    sourceTriangulationComparisonStableExactAtInputNamesW884.length =
      8 :=
  rfl

/-- Current checked W884 state. -/
structure MetrizableSourceTriangulationComparisonStableExactAtRouteStateW884 :
    Type where
  seed : String
  declarations : List String
  homologyConstructionResult : String
  concreteLeavesResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSourceTriangulationComparisonStableExactAtRouteStateW884 :
    MetrizableSourceTriangulationComparisonStableExactAtRouteStateW884
    where
  seed := "w884-source-triangulation-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppSourceTriangulationComparisonLeavesW884",
      "sourceHomologicalTriangulationDataOfSourceTriangulationW884",
      "concreteLeavesOfSourceTriangulationComparisonW884",
      "routeDataProviderOfSourceTriangulationComparisonW884",
      "directBoundedLeftCalculusOfSourceTriangulationComparisonStableExactAtW884",
      "boundedDerivedInfinityCategoryOfSourceTriangulationComparisonStableExactAtW884",
      "sourceTriangulationComparisonStableExactAtInputNamesW884",
      "sourceTriangulationComparisonStableExactAtInputNamesW884_count"]
  homologyConstructionResult :=
    "proved: W855/W821 supplies the category-homology part of the W733 source\
      homological-triangulation leaf"
  concreteLeavesResult :=
    "proved: source-triangulation leaves construct the W733 leaves consumed by W883"
  exactAtResult :=
    "proved: source-triangulation leaves feed the W883 stable ExactAt route"
  replacedInputs :=
    ["W733 source homological-triangulation data provider"]
  remainingInputs :=
    sourceTriangulationComparisonStableExactAtInputNamesW884
  productSuccessClaimed := false

theorem currentW884SourceTriangulationComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableSourceTriangulationComparisonStableExactAtRouteStateW884;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
