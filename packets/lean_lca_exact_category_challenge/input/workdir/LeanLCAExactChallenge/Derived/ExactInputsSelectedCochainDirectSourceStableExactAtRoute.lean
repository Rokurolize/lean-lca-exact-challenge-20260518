import LeanLCAExactChallenge.Derived.ExactInputsSelectedCochainDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainDirectSourceStableExactAtRoute

/-!
W869 composes the W850 exact-input selected-cochain direct-source data with the
W868 stable-ExactAt route. This moves the latest stable ExactAt boundary from a
bundled W847 datum to W850's W736 comparison-isomorphism input plus one W735
exact-input branch.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W869 closed-map direct bounded left calculus through W868 after W850 assembles
the W847 selected-cochain direct-source data from exact inputs.
-/
theorem
    directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
    (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W869 closed-embedding direct bounded left calculus through W868 after W850
assembles the W847 selected-cochain direct-source data from exact inputs.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
    (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W869 closed-map stable package through the W850-to-W847 data assembly used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
    (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W869 closed-embedding stable package through the W850-to-W847 data assembly
used by the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
    (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W869 has the W850 boundary: comparison isomorphism plus one exact-input branch.
-/
def exactInputsSelectedCochainStableExactAtInputNamesW869 :
    List String :=
  Dbounded.exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850

theorem exactInputsSelectedCochainStableExactAtInputNamesW869_count :
    exactInputsSelectedCochainStableExactAtInputNamesW869.length =
      2 :=
  Dbounded.exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850_count

/-- Current checked W869 state. -/
structure MetrizableExactInputsSelectedCochainStableExactAtRouteStateW869 :
    Type where
  seed : String
  declarations : List String
  selectedCochainDataAssemblyResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableExactInputsSelectedCochainStableExactAtRouteStateW869 :
    MetrizableExactInputsSelectedCochainStableExactAtRouteStateW869
    where
  seed := "w869-exact-inputs-selected-cochain-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869",
      "directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869",
      "boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputs" ++
        "SelectedCochainStableExactAtW869",
      "exactInputsSelectedCochainStableExactAtInputNamesW869",
      "exactInputsSelectedCochainStableExactAtInputNamesW869_count"]
  selectedCochainDataAssemblyResult :=
    "proved: W850 exact inputs plus comparison data assemble W847 data"
  concreteLeavesResult :=
    "proved: W850 data feed the W868 concrete-leaves target ExactAt direct \
      route through W847"
  stablePackageResult :=
    "proved: W850 data feed the W868 direct-source stable package through W847"
  replacedInputs :=
    ["separate W847 selected-cochain direct-source data at the W868 boundary"]
  remainingInputs :=
    Dbounded.exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850
  productSuccessClaimed := false

theorem currentW869ExactInputsSelectedCochainStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableExactInputsSelectedCochainStableExactAtRouteStateW869;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
