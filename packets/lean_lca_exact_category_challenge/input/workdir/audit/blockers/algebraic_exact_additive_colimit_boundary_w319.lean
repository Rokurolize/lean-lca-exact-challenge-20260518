import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W319: reducing the W318 algebraic-exactness input to an additive colimit exactness
boundary.

W318 leaves a direct element-level algebraic kernel equality for the WPP-op
colimit point.  This file separates that obligation from topology: the remaining
input is a pure `AddCommGrpCat` statement saying that the underlying additive
component colimits preserve the kernel/range equality of the short-complex right
map.

This intentionally avoids `ShortComplex.Exact`, `HasHomology`, and forgetful
`PreservesHomology`.  It does not prove the additive exactness preservation
theorem itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicExactAdditiveColimitBoundaryW319

/-- The W318 algebraic exactness field. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Element-level exactness of a short complex after forgetting topology. -/
abbrev AdditiveKernelExact (T : ShortComplex MetrizableLCA.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂

/--
Pure additive colimit exactness boundary.  The hypotheses expose only the
componentwise additive exactness of the diagram and the WPP-op colimit cocone.
Downstream work may prove this from explicit coequalizer presentations in
`AddCommGrpCat`.
-/
abbrev additiveKernelExact_wppOp_colimit_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, AdditiveKernelExact (S.obj j)) →
          AdditiveKernelExact cs.pt

/--
The additive boundary supplies W318's algebraic field.  The strictness assumptions
are consumed only through their already-available algebraic exactness fields.
-/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary
    (hboundary : additiveKernelExact_wppOp_colimit_boundary) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hboundary S cs hcs (fun j x₂ hx₂ => (hS j).algebraic_exact x₂ hx₂)

/-- A more explicit package for the additive exactness frontier. -/
structure AdditiveKernelExactColimitInput : Prop where
  boundary : additiveKernelExact_wppOp_colimit_boundary

/-- Package consumer for W318's algebraic field. -/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_input
    (h : AdditiveKernelExactColimitInput) :
    algebraicExact_walkingParallelPairOp_colimitClosure :=
  algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary h.boundary

/-- Machine-readable W319 frontier state. -/
structure AlgebraicExactAdditiveColimitBoundaryState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W319 state for downstream workers. -/
def currentAlgebraicExactAdditiveColimitBoundaryState :
    AlgebraicExactAdditiveColimitBoundaryState where
  seed := "w319-parent-20260521T0320Z"
  provedConsumer :=
    "algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary"
  remainingInputs :=
    ["additiveKernelExact_wppOp_colimit_boundary",
      "prove it by explicit AddCommGrpCat WPP-op coequalizer/colimit presentation"]
  productSuccessClaimed := false

theorem currentAlgebraicExactAdditiveColimitBoundaryState_productSuccess :
    currentAlgebraicExactAdditiveColimitBoundaryState.productSuccessClaimed = false := rfl

section Checks

#check algebraicExact_walkingParallelPairOp_colimitClosure
#check AdditiveKernelExact
#check additiveKernelExact_wppOp_colimit_boundary
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary
#check AdditiveKernelExactColimitInput
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_input
#check currentAlgebraicExactAdditiveColimitBoundaryState
#check currentAlgebraicExactAdditiveColimitBoundaryState_productSuccess
#check MetrizableLCA.StrictShortExact.algebraic_exact

end Checks

end AlgebraicExactAdditiveColimitBoundaryW319

end LeanLCAExactChallenge
