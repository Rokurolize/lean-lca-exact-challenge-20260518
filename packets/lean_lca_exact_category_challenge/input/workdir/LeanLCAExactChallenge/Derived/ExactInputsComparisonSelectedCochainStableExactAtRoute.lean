import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.ExactInputsSelectedCochainDirectSourceStableExactAtRoute

/-!
W870 composes the W851 comparison-selected-cochain route with the W869
stable-ExactAt route. This removes W869's explicit comparison-isomorphism
argument by using the W831 comparison-bijectivity route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W870 closed-map direct bounded left calculus through W869, with W831 supplying
the W850 comparison-isomorphism input.
-/
theorem
    directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W870 closed-embedding direct bounded left calculus through W869, with W831
supplying the W850 comparison-isomorphism input.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W870 closed-map stable package through W869, with W831 supplying the W850
comparison-isomorphism input.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W870 closed-embedding stable package through W869, with W831 supplying the W850
comparison-isomorphism input.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/-- W870 has one input: the W735 exact-input branch. -/
def comparisonSelectedCochainStableExactAtInputNamesW870 : List String :=
  Dbounded.comparisonSelectedCochainStableRouteInputNamesW851

theorem comparisonSelectedCochainStableExactAtInputNamesW870_count :
    comparisonSelectedCochainStableExactAtInputNamesW870.length =
      1 :=
  Dbounded.comparisonSelectedCochainStableRouteInputNamesW851_count

/-- Current checked W870 state. -/
structure MetrizableComparisonSelectedCochainStableExactAtRouteStateW870 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComparisonSelectedCochainStableExactAtRouteStateW870 :
    MetrizableComparisonSelectedCochainStableExactAtRouteStateW870
    where
  seed := "w870-comparison-selected-cochain-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870",
      "directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870",
      "boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingComparison" ++
        "SelectedCochainStableExactAtW870",
      "comparisonSelectedCochainStableExactAtInputNamesW870",
      "comparisonSelectedCochainStableExactAtInputNamesW870_count"]
  comparisonResult :=
    "proved: W831 supplies W869's universal comparison-isomorphism input"
  concreteLeavesResult :=
    "proved: one W735 branch feeds the W869 concrete-leaves target ExactAt \
      direct route"
  stablePackageResult :=
    "proved: one W735 branch feeds the W869 direct-source stable package"
  replacedInputs :=
    ["explicit W736 comparison-isomorphism input at the W869 boundary"]
  remainingInputs :=
    Dbounded.comparisonSelectedCochainStableRouteInputNamesW851
  productSuccessClaimed := false

theorem currentW870ComparisonSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableComparisonSelectedCochainStableExactAtRouteStateW870;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
