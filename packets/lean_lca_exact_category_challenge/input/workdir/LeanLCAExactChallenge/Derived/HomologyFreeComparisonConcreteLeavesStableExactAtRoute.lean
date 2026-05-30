import LeanLCAExactChallenge.Derived.ComparisonSelectedCochainConcreteLeavesStableExactAtRoute
import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableRoute

/-!
W880 feeds the W879 comparison concrete-leaves stable-ExactAt route from the
W853 homology-free selected-cochain provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W880 direct bounded left calculus from one W853 homology-free provider through
the W879 comparison concrete-leaves stable ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/--
W880 bounded derived infinity-category package from one W853 homology-free
provider through the W879 comparison concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  match routeData.diagramAndMappedCokernelClosednessData with
  | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
      boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
        (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedMapComponents mappedCokernelClosedMapProvider)
  | .closedEmbedding globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =>
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
          globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W880 has one bundled input: the W853 homology-free provider. -/
def homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880 :
    List String :=
  homologyFreeSelectedCochainStableRouteInputNamesW853

theorem homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880_count :
    homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880.length =
      1 :=
  homologyFreeSelectedCochainStableRouteInputNamesW853_count

/-- Expanded W880 requirements are the eight fields of the W853 provider. -/
def homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation ordinary relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "endpoint strict-topology data provider",
    "bounded homotopy localized-right-adjoint data provider"]

theorem
    homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880_count :
    homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880.length =
      8 :=
  rfl

/-- Current checked W880 state. -/
structure MetrizableHomologyFreeComparisonConcreteLeavesStableExactAtRouteStateW880 :
    Type where
  seed : String
  declarations : List String
  branchAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  expandedRemainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableHomologyFreeComparisonConcreteLeavesStableExactAtRouteStateW880 :
    MetrizableHomologyFreeComparisonConcreteLeavesStableExactAtRouteStateW880
    where
  seed := "w880-homology-free-comparison-concrete-leaves-stable-exact-at"
  declarations :=
    ["directBoundedLeftCalculusOfHomologyFreeComparison" ++
        "ConcreteLeavesStableExactAtW880",
      "boundedDerivedInfinityCategoryOfHomologyFreeComparison" ++
        "ConcreteLeavesStableExactAtW880",
      "homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880",
      "homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880_count",
      "homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880",
      "homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880_count"]
  branchAssemblyResult :=
    "proved: W853 rebuilds the W735 branch consumed by the W879 route"
  exactAtResult :=
    "proved: one W853 homology-free provider supplies the W879 stable ExactAt package"
  replacedInputs :=
    comparisonConcreteLeavesStableExactAtInputNamesW879
  remainingInputs :=
    homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880
  expandedRemainingInputs :=
    homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880
  productSuccessClaimed := false

theorem currentW880HomologyFreeComparisonConcreteLeavesStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableHomologyFreeComparisonConcreteLeavesStableExactAtRouteStateW880;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
