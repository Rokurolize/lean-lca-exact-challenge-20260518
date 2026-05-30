import LeanLCAExactChallenge.Derived.SelectedCochainConcreteLeavesStableExactAtRoute
import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.W735W732SelectedCochainStableExactAtRoute

/-!
W879 feeds the W878 selected-cochain concrete-leaves stable-ExactAt route from
the W851 comparison selected-cochain surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W879 closed-map W847 data assembled by W851. -/
noncomputable def closedMapSelectedCochainDataOfComparisonW879
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedMapSelectedCochainDirectSourceDataOfComparisonW851 exactInputs

/-- W879 closed-embedding W847 data assembled by W851. -/
noncomputable def closedEmbeddingSelectedCochainDataOfComparisonW879
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851 exactInputs

/--
W879 closed-map direct bounded left calculus through the W878 concrete-leaves
stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
    (closedMapSelectedCochainDataOfComparisonW879 exactInputs)

/--
W879 closed-embedding direct bounded left calculus through the W878
concrete-leaves stable ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
    (closedEmbeddingSelectedCochainDataOfComparisonW879 exactInputs)

/--
W879 closed-map bounded derived infinity-category package through the W878
concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
    (closedMapSelectedCochainDataOfComparisonW879 exactInputs)

/--
W879 closed-embedding bounded derived infinity-category package through the W878
concrete-leaves stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
    (closedEmbeddingSelectedCochainDataOfComparisonW879 exactInputs)

/-- W879 has one bundled input: a W735 exact-input branch. -/
def comparisonConcreteLeavesStableExactAtInputNamesW879 :
    List String :=
  Dbounded.comparisonSelectedCochainStableRouteInputNamesW851

theorem comparisonConcreteLeavesStableExactAtInputNamesW879_count :
    comparisonConcreteLeavesStableExactAtInputNamesW879.length =
      1 :=
  Dbounded.comparisonSelectedCochainStableRouteInputNamesW851_count

/-- Expanded W879 requirements are the nine W735 branch fields. -/
def comparisonConcreteLeavesStableExactAtExpandedInputNamesW879 :
    List String :=
  Dbounded.w735W732SelectedCochainStableExactAtInputNamesW876

theorem comparisonConcreteLeavesStableExactAtExpandedInputNamesW879_count :
    comparisonConcreteLeavesStableExactAtExpandedInputNamesW879.length =
      9 :=
  Dbounded.w735W732SelectedCochainStableExactAtInputNamesW876_count

/-- Current checked W879 state. -/
structure MetrizableComparisonConcreteLeavesStableExactAtRouteStateW879 :
    Type where
  seed : String
  declarations : List String
  selectedCochainDataResult : String
  stableExactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  expandedRemainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComparisonConcreteLeavesStableExactAtRouteStateW879 :
    MetrizableComparisonConcreteLeavesStableExactAtRouteStateW879
    where
  seed := "w879-comparison-selected-cochain-concrete-leaves-stable-exact-at"
  declarations :=
    ["closedMapSelectedCochainDataOfComparisonW879",
      "closedEmbeddingSelectedCochainDataOfComparisonW879",
      "directBoundedLeftCalculusOfClosedMapComparison" ++
        "ConcreteLeavesStableExactAtW879",
      "directBoundedLeftCalculusOfClosedEmbeddingComparison" ++
        "ConcreteLeavesStableExactAtW879",
      "boundedDerivedInfinityCategoryOfClosedMapComparison" ++
        "ConcreteLeavesStableExactAtW879",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingComparison" ++
        "ConcreteLeavesStableExactAtW879",
      "comparisonConcreteLeavesStableExactAtInputNamesW879",
      "comparisonConcreteLeavesStableExactAtInputNamesW879_count",
      "comparisonConcreteLeavesStableExactAtExpandedInputNamesW879",
      "comparisonConcreteLeavesStableExactAtExpandedInputNamesW879_count"]
  selectedCochainDataResult :=
    "proved: W851 supplies W847 selected-cochain data from one W735 branch"
  stableExactAtResult :=
    "proved: W851 comparison selected-cochain data feed the W878 route"
  replacedInputs :=
    selectedCochainConcreteLeavesStableExactAtExpandedInputNamesW878
  remainingInputs :=
    comparisonConcreteLeavesStableExactAtInputNamesW879
  expandedRemainingInputs :=
    comparisonConcreteLeavesStableExactAtExpandedInputNamesW879
  productSuccessClaimed := false

theorem currentW879ComparisonConcreteLeavesStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableComparisonConcreteLeavesStableExactAtRouteStateW879;
      state.productSuccessClaimed) =
        false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
