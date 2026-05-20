import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W301: field boundary for strict short-exact `WalkingParallelPairᵒᵖ` colimit closure.

W299/W300 reduce W271's exact-acyclic WPP-op colimit-closure input to a
ShortComplex-level closure statement for the local strict `MetrizableLCA`
conflation predicate.  Since the product exact structure defines conflations as
`MetrizableLCA.strictShortExact`, this file lowers that remaining closure theorem
to the four concrete fields in `StrictShortExact`:

* closed embedding of the left map;
* open map of the right map;
* surjectivity of the right map;
* algebraic kernel exactness.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpStrictShortExactColimitFieldsW301

/-- The remaining strict short-exact WPP-op colimit closure target. -/
abbrev strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          MetrizableLCA.strictShortExact cs.pt

/-- The corresponding product exact-category conflation closure target. -/
abbrev shortComplexConflation_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, QuillenExactCategory.Conflation (S.obj j)) →
          QuillenExactCategory.Conflation cs.pt

/-- Closure of the left closed-embedding field under the chosen WPP-op colimit. -/
abbrev leftClosedEmbedding_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Closure of the right surjectivity field under the chosen WPP-op colimit. -/
abbrev rightSurjective_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Closure of the algebraic kernel exactness field under the chosen WPP-op colimit. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/--
The four concrete `StrictShortExact` fields imply strict short-exact closure under
the chosen WPP-op colimit.
-/
theorem strictShortExact_walkingParallelPairOp_colimit_closure_of_fields
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure)
    (hsurj : rightSurjective_walkingParallelPairOp_colimitClosure)
    (hexact : algebraicExact_walkingParallelPairOp_colimitClosure) :
    strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  intro S cs hcs hS
  exact
    { closed_inclusion := hclosed S cs hcs hS
      open_map := hopen S cs hcs hS
      surjective := hsurj S cs hcs hS
      algebraic_exact := hexact S cs hcs hS }

/--
Strict short-exact closure is definitionally the same local input needed for
product conflation closure in `ShortComplex MetrizableLCA`.
-/
theorem shortComplexConflation_walkingParallelPairOp_colimitClosure_of_strictShortExact
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    shortComplexConflation_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hstrict S cs hcs hS

/-- Machine-readable frontier state for W301. -/
structure WppOpStrictShortExactColimitFieldsState : Type where
  seed : String
  selectedRoute : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W301 boundary state. -/
def currentWppOpStrictShortExactColimitFieldsState :
    WppOpStrictShortExactColimitFieldsState where
  seed := "w301-parent-20260520T1618Z"
  selectedRoute :=
    "reduce WPP-op ShortComplex Conflation colimit closure to four StrictShortExact fields"
  provedConsumer :=
    "strictShortExact_walkingParallelPairOp_colimit_closure_of_fields"
  remainingInputs :=
    ["leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure",
      "rightSurjective_walkingParallelPairOp_colimitClosure",
      "algebraicExact_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpStrictShortExactColimitFieldsState_productSuccess :
    currentWppOpStrictShortExactColimitFieldsState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpStrictShortExactColimitFieldsDeclarationNames : List String :=
  ["strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure",
    "shortComplexConflation_walkingParallelPairOp_colimitClosure",
    "leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
    "rightOpenMap_walkingParallelPairOp_colimitClosure",
    "rightSurjective_walkingParallelPairOp_colimitClosure",
    "algebraicExact_walkingParallelPairOp_colimitClosure",
    "strictShortExact_walkingParallelPairOp_colimit_closure_of_fields",
    "shortComplexConflation_walkingParallelPairOp_colimitClosure_of_strictShortExact",
    "currentWppOpStrictShortExactColimitFieldsState"]

theorem wppOpStrictShortExactColimitFieldsDeclarationNames_count :
    wppOpStrictShortExactColimitFieldsDeclarationNames.length = 9 := rfl

section Checks

#check strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure
#check shortComplexConflation_walkingParallelPairOp_colimitClosure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure
#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check rightSurjective_walkingParallelPairOp_colimitClosure
#check algebraicExact_walkingParallelPairOp_colimitClosure
#check strictShortExact_walkingParallelPairOp_colimit_closure_of_fields
#check shortComplexConflation_walkingParallelPairOp_colimitClosure_of_strictShortExact
#check currentWppOpStrictShortExactColimitFieldsState
#check currentWppOpStrictShortExactColimitFieldsState_productSuccess
#check wppOpStrictShortExactColimitFieldsDeclarationNames
#check wppOpStrictShortExactColimitFieldsDeclarationNames_count
#check MetrizableLCA.strictShortExact
#check MetrizableLCA.quillenExactCategory
#check QuillenExactCategory.Conflation

end Checks

end WppOpStrictShortExactColimitFieldsW301

end LeanLCAExactChallenge
