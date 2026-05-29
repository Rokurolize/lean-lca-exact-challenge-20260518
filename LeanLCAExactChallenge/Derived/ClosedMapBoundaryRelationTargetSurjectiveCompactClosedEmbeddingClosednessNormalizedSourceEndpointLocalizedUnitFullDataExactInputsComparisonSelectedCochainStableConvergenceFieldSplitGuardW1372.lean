import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSelectedCochainStrictificationStableConvergenceFieldSplitGuardW1371
import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableExactAtRoute

/-!
W1372 records the definitional convergence from W850 exact-input selected
cochain data and W851 comparison-selected-cochain data into the W869/W870
stable ExactAt route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W869 closed-map direct calculus is W850 assembly followed by W868. -/
theorem w869ClosedMapDirectCalculusRunsThroughW850W868W1372
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        comparisonIso exactInputs =
      directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
          comparisonIso exactInputs) :=
  rfl

/-- W869 closed-embedding direct calculus is W850 assembly followed by W868. -/
theorem w869ClosedEmbeddingDirectCalculusRunsThroughW850W868W1372
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        comparisonIso exactInputs =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
          comparisonIso exactInputs) :=
  rfl

/-- W869 closed-map stable package is W850 assembly followed by W868. -/
theorem w869ClosedMapStablePackageRunsThroughW850W868W1372
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        comparisonIso exactInputs =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
          comparisonIso exactInputs) :=
  rfl

/-- W869 closed-embedding stable package is W850 assembly followed by W868. -/
theorem w869ClosedEmbeddingStablePackageRunsThroughW850W868W1372
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        comparisonIso exactInputs =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
          comparisonIso exactInputs) :=
  rfl

/-- W870 closed-map direct calculus is W869 with the W831 universal comparison iso. -/
theorem w870ClosedMapDirectCalculusRunsThroughW869W1372
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        exactInputs =
      directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        exactInputs :=
  rfl

/-- W870 closed-embedding direct calculus is W869 with the W831 universal comparison iso. -/
theorem w870ClosedEmbeddingDirectCalculusRunsThroughW869W1372
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        exactInputs =
      directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        exactInputs :=
  rfl

/-- W870 closed-map stable package is W869 with the W831 universal comparison iso. -/
theorem w870ClosedMapStablePackageRunsThroughW869W1372
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        exactInputs =
      boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        exactInputs :=
  rfl

/-- W870 closed-embedding stable package is W869 with the W831 universal comparison iso. -/
theorem w870ClosedEmbeddingStablePackageRunsThroughW869W1372
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        exactInputs =
      boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        exactInputs :=
  rfl

/-- W1372 keeps the W869 exact-input boundary count visible. -/
theorem w1372ExactInputsSelectedCochainStableExactAtInputCountMatchesW869 :
    exactInputsSelectedCochainStableExactAtInputNamesW869.length = 2 :=
  exactInputsSelectedCochainStableExactAtInputNamesW869_count

/-- W1372 keeps the W870 comparison-selected-cochain boundary count visible. -/
theorem w1372ComparisonSelectedCochainStableExactAtInputCountMatchesW870 :
    comparisonSelectedCochainStableExactAtInputNamesW870.length = 1 :=
  comparisonSelectedCochainStableExactAtInputNamesW870_count

/-- Current W1372 nonterminal state. -/
structure ExactInputsComparisonSelectedCochainStableConvergenceStateW1372 :
    Type where
  seed : String
  declarations : List String
  exactInputsResult : String
  comparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1372 records W850/W851 convergence into W869/W870. -/
def currentExactInputsComparisonSelectedCochainStableConvergenceStateW1372 :
    ExactInputsComparisonSelectedCochainStableConvergenceStateW1372 where
  seed := "w1372-exact-inputs-comparison-selected-cochain-stable-convergence"
  declarations :=
    ["w869ClosedMapDirectCalculusRunsThroughW850W868W1372",
      "w869ClosedEmbeddingDirectCalculusRunsThroughW850W868W1372",
      "w869ClosedMapStablePackageRunsThroughW850W868W1372",
      "w869ClosedEmbeddingStablePackageRunsThroughW850W868W1372",
      "w870ClosedMapDirectCalculusRunsThroughW869W1372",
      "w870ClosedEmbeddingDirectCalculusRunsThroughW869W1372",
      "w870ClosedMapStablePackageRunsThroughW869W1372",
      "w870ClosedEmbeddingStablePackageRunsThroughW869W1372",
      "w1372ExactInputsSelectedCochainStableExactAtInputCountMatchesW869",
      "w1372ComparisonSelectedCochainStableExactAtInputCountMatchesW870"]
  exactInputsResult :=
    "proved: W869 direct calculus and stable package route through W850 \
      exact-input selected-cochain assembly and W868"
  comparisonResult :=
    "proved: W870 direct calculus and stable package route through W869 using \
      the W831 universal comparison isomorphism"
  remainingInputs :=
    comparisonSelectedCochainStableExactAtInputNamesW870
  productSuccessClaimed := false

theorem currentW1372ExactInputsComparisonSelectedCochainStableConvergence_productSuccess :
    currentExactInputsComparisonSelectedCochainStableConvergenceStateW1372.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
