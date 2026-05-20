import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W300: direct degreewise short-complex colimit comparison for `WalkingParallelPairᵒᵖ`.

W299 reduced one W271 input to two smaller facts.  This file discharges the first
of those facts: applying the degreewise short-complex functor to a WPP-op colimit
cocone is colimit.  The proof is not by a synthesized preservation instance for
`shortComplexFunctor`; it explicitly combines:

* mathlib's colimit preservation for `HomologicalComplex.eval`;
* mathlib's constructor `ShortComplex.isColimitOfIsColimitπ`.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpShortComplexColimitComparisonW300

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/--
Applying the degree-`i` short-complex functor to a WPP-op cochain-complex colimit
cocone gives a colimit cocone in short complexes.
-/
abbrev walkingParallelPairOp_shortComplex_colimitComparison : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        ∀ i : ℤ, Nonempty (IsColimit ((degreeShortComplexFunctor i).mapCocone ck))

/--
Direct proof of the W299 comparison input.

The three projections of the mapped short-complex cocone are the evaluations of
the original cochain-complex cocone in degrees `prev i`, `i`, and `next i`; these
are colimit cocones because `HomologicalComplex.eval` preserves colimits.
-/
theorem walkingParallelPairOp_shortComplex_colimitComparison_direct :
    walkingParallelPairOp_shortComplex_colimitComparison := by
  intro K ck hck i
  refine ⟨ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_⟩
  · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor] using
      (isColimitOfPreserves
        (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).prev i)) hck)
  · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor] using
      (isColimitOfPreserves
        (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) i) hck)
  · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor] using
      (isColimitOfPreserves
        (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
          ((ComplexShape.up ℤ).next i)) hck)

/-- Machine-readable frontier state for W300. -/
structure WppOpShortComplexColimitComparisonState : Type where
  seed : String
  selectedRoute : String
  provedInput : String
  upstreamConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W300 boundary state. -/
def currentWppOpShortComplexColimitComparisonState :
    WppOpShortComplexColimitComparisonState where
  seed := "w300-parent-20260520T1615Z"
  selectedRoute :=
    "ShortComplex.isColimitOfIsColimitπ plus HomologicalComplex.eval colimit preservation"
  provedInput := "walkingParallelPairOp_shortComplex_colimitComparison"
  upstreamConsumer := "W299 exactAcyclic_walkingParallelPairOp_colimit_closure_of_shortComplexClosure"
  remainingInputs := ["shortComplexConflation_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpShortComplexColimitComparisonState_productSuccess :
    currentWppOpShortComplexColimitComparisonState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpShortComplexColimitComparisonDeclarationNames : List String :=
  ["degreeShortComplexFunctor",
    "walkingParallelPairOp_shortComplex_colimitComparison",
    "walkingParallelPairOp_shortComplex_colimitComparison_direct",
    "currentWppOpShortComplexColimitComparisonState"]

theorem wppOpShortComplexColimitComparisonDeclarationNames_count :
    wppOpShortComplexColimitComparisonDeclarationNames.length = 4 := rfl

section Checks

#check degreeShortComplexFunctor
#check walkingParallelPairOp_shortComplex_colimitComparison
#check walkingParallelPairOp_shortComplex_colimitComparison_direct
#check currentWppOpShortComplexColimitComparisonState
#check currentWppOpShortComplexColimitComparisonState_productSuccess
#check wppOpShortComplexColimitComparisonDeclarationNames
#check wppOpShortComplexColimitComparisonDeclarationNames_count
#check ShortComplex.isColimitOfIsColimitπ
#check HomologicalComplex.eval
#check isColimitOfPreserves

end Checks

end WppOpShortComplexColimitComparisonW300

end LeanLCAExactChallenge
