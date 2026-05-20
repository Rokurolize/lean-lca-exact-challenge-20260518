import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W299: exact-acyclic `WalkingParallelPairᵒᵖ` colimit closure boundary.

W271 left the direct input
`exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure`.  Since
`exactAcyclic C K` is defined degreewise as `QuillenExactCategory.Conflation (K.sc i)`,
this file reduces that input to two smaller local facts:

* the short-complex functor at each degree preserves the relevant WPP-op colimit cocone;
* WPP-op colimits of strict `MetrizableLCA` short complexes preserve `Conflation`.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpExactAcyclicColimitClosureW299

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/-- W271's exact-acyclic WPP-op colimit closure input, restated locally. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        (∀ j : WalkingParallelPairᵒᵖ, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/--
Degreewise comparison input: applying the degree-`i` short-complex functor to a WPP-op
cochain-complex colimit cocone gives a colimit cocone in short complexes.
-/
abbrev walkingParallelPairOp_shortComplex_colimitComparison : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        ∀ i : ℤ, Nonempty (IsColimit ((degreeShortComplexFunctor i).mapCocone ck))

/--
The remaining strict short-complex closure theorem: WPP-op colimits preserve the local
`MetrizableLCA` conflation predicate.
-/
abbrev shortComplexConflation_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, QuillenExactCategory.Conflation (S.obj j)) →
          QuillenExactCategory.Conflation cs.pt

/--
The degreewise comparison and short-complex conflation closure inputs imply W271's
exact-acyclic WPP-op colimit closure.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_shortComplexClosure
    (hcomparison : walkingParallelPairOp_shortComplex_colimitComparison)
    (hclosure : shortComplexConflation_walkingParallelPairOp_colimitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  intro K ck hck hK i
  rcases hcomparison K ck hck i with ⟨hsc⟩
  exact hclosure (K ⋙ degreeShortComplexFunctor i) ((degreeShortComplexFunctor i).mapCocone ck)
    hsc (fun j => hK j i)

/-- Machine-readable frontier state for W299. -/
structure WppOpExactAcyclicColimitClosureState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W299 boundary state. -/
def currentWppOpExactAcyclicColimitClosureState :
    WppOpExactAcyclicColimitClosureState where
  seed := "w299-parent-20260520T1555Z"
  selectedRoute :=
    "reduce W271 exact-acyclic WPP-op colimit closure to degreewise short-complex colimit closure"
  checkedBoundary :=
    "walkingParallelPairOp_shortComplex_colimitComparison + shortComplexConflation_walkingParallelPairOp_colimitClosure"
  provedConsumer :=
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_shortComplexClosure"
  remainingInputs :=
    ["walkingParallelPairOp_shortComplex_colimitComparison",
      "shortComplexConflation_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpExactAcyclicColimitClosureState_productSuccess :
    currentWppOpExactAcyclicColimitClosureState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpExactAcyclicColimitClosureDeclarationNames : List String :=
  ["degreeShortComplexFunctor",
    "walkingParallelPairOp_shortComplex_colimitComparison",
    "shortComplexConflation_walkingParallelPairOp_colimitClosure",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_shortComplexClosure",
    "currentWppOpExactAcyclicColimitClosureState"]

theorem wppOpExactAcyclicColimitClosureDeclarationNames_count :
    wppOpExactAcyclicColimitClosureDeclarationNames.length = 5 := rfl

section Checks

#check degreeShortComplexFunctor
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check walkingParallelPairOp_shortComplex_colimitComparison
#check shortComplexConflation_walkingParallelPairOp_colimitClosure
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_shortComplexClosure
#check currentWppOpExactAcyclicColimitClosureState
#check currentWppOpExactAcyclicColimitClosureState_productSuccess
#check wppOpExactAcyclicColimitClosureDeclarationNames
#check wppOpExactAcyclicColimitClosureDeclarationNames_count
#check HomologicalComplex.shortComplexFunctor
#check QuillenExactCategory.Conflation

end Checks

end WppOpExactAcyclicColimitClosureW299

end LeanLCAExactChallenge
