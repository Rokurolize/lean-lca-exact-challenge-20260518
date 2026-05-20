import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W307: exact equivalence for the W301 strict-short-exact field split.

W301 proved that the four concrete `MetrizableLCA.strictShortExact` fields imply
the WPP-op strict-short-exact colimit closure.  This file records the converse:
the closure theorem itself immediately supplies each concrete field.  This makes
the W301 split an exact equivalence, so later workers can focus on proving one
of the four fields rather than rechecking whether the split lost information.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpStrictShortExactColimitFieldsIffW307

/-- The remaining strict short-exact WPP-op colimit closure target, restated locally. -/
abbrev strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          MetrizableLCA.strictShortExact cs.pt

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

/-- The four concrete field-closure inputs packaged together. -/
structure StrictShortExactFieldClosurePackage : Prop where
  leftClosedEmbedding : leftClosedEmbedding_walkingParallelPairOp_colimitClosure
  rightOpenMap : rightOpenMap_walkingParallelPairOp_colimitClosure
  rightSurjective : rightSurjective_walkingParallelPairOp_colimitClosure
  algebraicExact : algebraicExact_walkingParallelPairOp_colimitClosure

/-- Strict-short-exact colimit closure supplies the left closed-embedding field. -/
theorem leftClosedEmbedding_of_strictShortExactClosure
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    leftClosedEmbedding_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact (hstrict S cs hcs hS).closed_inclusion

/-- Strict-short-exact colimit closure supplies the right open-map field. -/
theorem rightOpenMap_of_strictShortExactClosure
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    rightOpenMap_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact (hstrict S cs hcs hS).open_map

/-- Strict-short-exact colimit closure supplies the right surjectivity field. -/
theorem rightSurjective_of_strictShortExactClosure
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    rightSurjective_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact (hstrict S cs hcs hS).surjective

/-- Strict-short-exact colimit closure supplies the algebraic exactness field. -/
theorem algebraicExact_of_strictShortExactClosure
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact (hstrict S cs hcs hS).algebraic_exact

/-- The strict-short-exact closure theorem gives the exact field package. -/
theorem fieldClosurePackage_of_strictShortExactClosure
    (hstrict : strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure) :
    StrictShortExactFieldClosurePackage where
  leftClosedEmbedding := leftClosedEmbedding_of_strictShortExactClosure hstrict
  rightOpenMap := rightOpenMap_of_strictShortExactClosure hstrict
  rightSurjective := rightSurjective_of_strictShortExactClosure hstrict
  algebraicExact := algebraicExact_of_strictShortExactClosure hstrict

/-- The field package gives the strict-short-exact closure theorem. -/
theorem strictShortExactClosure_of_fieldClosurePackage
    (h : StrictShortExactFieldClosurePackage) :
    strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  intro S cs hcs hS
  exact
    { closed_inclusion := h.leftClosedEmbedding S cs hcs hS
      open_map := h.rightOpenMap S cs hcs hS
      surjective := h.rightSurjective S cs hcs hS
      algebraic_exact := h.algebraicExact S cs hcs hS }

/-- W301's four-field split is exact: no information is lost in either direction. -/
theorem strictShortExactClosure_iff_fieldClosurePackage :
    strictShortExact_metrizableLCA_walkingParallelPairOp_colimit_closure ↔
      StrictShortExactFieldClosurePackage := by
  constructor
  · exact fieldClosurePackage_of_strictShortExactClosure
  · exact strictShortExactClosure_of_fieldClosurePackage

/-- Machine-readable frontier state for W307. -/
structure WppOpStrictShortExactFieldsIffState : Type where
  seed : String
  checkedBoundary : String
  provedEquivalence : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W307 boundary state. -/
def currentWppOpStrictShortExactFieldsIffState :
    WppOpStrictShortExactFieldsIffState where
  seed := "w307-parent-20260520T1629Z"
  checkedBoundary :=
    "W301 strictShortExact WPP-op colimit closure versus four concrete fields"
  provedEquivalence :=
    "strictShortExactClosure_iff_fieldClosurePackage"
  remainingInputs :=
    ["leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure",
      "rightSurjective_walkingParallelPairOp_colimitClosure",
      "algebraicExact_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpStrictShortExactFieldsIffState_productSuccess :
    currentWppOpStrictShortExactFieldsIffState.productSuccessClaimed = false := rfl

section Checks

#check StrictShortExactFieldClosurePackage
#check leftClosedEmbedding_of_strictShortExactClosure
#check rightOpenMap_of_strictShortExactClosure
#check rightSurjective_of_strictShortExactClosure
#check algebraicExact_of_strictShortExactClosure
#check fieldClosurePackage_of_strictShortExactClosure
#check strictShortExactClosure_of_fieldClosurePackage
#check strictShortExactClosure_iff_fieldClosurePackage
#check currentWppOpStrictShortExactFieldsIffState
#check currentWppOpStrictShortExactFieldsIffState_productSuccess

end Checks

end WppOpStrictShortExactColimitFieldsIffW307

end LeanLCAExactChallenge
