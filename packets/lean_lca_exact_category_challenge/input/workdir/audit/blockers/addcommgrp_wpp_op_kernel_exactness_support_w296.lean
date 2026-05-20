import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Connected

/-!
W296: AddCommGrpCat kernel-exactness support for the W319 additive boundary.

W319 reduced the W318 algebraic exactness field to the preservation of the
element-level middle-kernel lift across a WPP-op colimit.  This file makes the
remaining additive input explicit in `AddCommGrpCat` terms and proves the checked
consumer back to W319's `additiveKernelExact_wppOp_colimit_boundary`.

The broad automatic route is intentionally guarded: mathlib does not synthesize
`HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpWppOpKernelExactnessSupportW296

/-- Element-level middle-kernel exactness for a short complex of abelian groups. -/
abbrev AddCommGrpKernelExact (T : ShortComplex AddCommGrpCat.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- The local additive exactness predicate from W319. -/
abbrev AdditiveKernelExact (T : ShortComplex MetrizableLCA.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- W319's additive WPP-op colimit boundary, restated locally. -/
abbrev additiveKernelExact_wppOp_colimit_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, AdditiveKernelExact (S.obj j)) →
          AdditiveKernelExact cs.pt

/--
The AddCommGrpCat-shaped source theorem that would close W319's additive
boundary.  It is deliberately no stronger than the kernel-lift fact needed at
the WPP-op colimit point.
-/
abbrev addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          AddCommGrpKernelExact (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/-- The MetrizableLCA and AddCommGrpCat element-level predicates are definitionally aligned. -/
theorem addCommGrpKernelExact_iff_additiveKernelExact
    (T : ShortComplex MetrizableLCA.{0}) :
    AddCommGrpKernelExact (T.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ↔
      AdditiveKernelExact T := by
  rfl

/--
Consumer from the AddCommGrpCat-shaped kernel-exactness input to W319's additive
boundary.
-/
theorem additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact
    (hboundary : addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable) :
    additiveKernelExact_wppOp_colimit_boundary := by
  intro S cs hcs hS
  exact hboundary S cs hcs (fun j => (addCommGrpKernelExact_iff_additiveKernelExact
    (S.obj j)).mpr (hS j))

/-- ShortComplex exactness in `AddCommGrpCat` supplies the element-level kernel lift. -/
theorem addCommGrpKernelExact_of_shortComplex_exact
    (T : ShortComplex AddCommGrpCat.{0}) (hT : T.Exact) :
    AddCommGrpKernelExact T := by
  rw [ShortComplex.ab_exact_iff] at hT
  exact hT

/--
An exactness-closure theorem for WPP-op colimit points in `AddCommGrpCat` would
supply the element-level boundary needed above.
-/
abbrev addCommGrpShortComplexExact_wppOp_colimit_boundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})).Exact) →
          (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})).Exact

/-- Exact short-complex closure implies the narrower kernel-exactness boundary. -/
theorem addCommGrpKernelExact_wppOp_colimit_boundary_of_shortComplexExact
    (hexact : addCommGrpShortComplexExact_wppOp_colimit_boundary_for_metrizable) :
    addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hS
  exact addCommGrpKernelExact_of_shortComplex_exact
    (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (hexact S cs hcs (fun j => by
      rw [ShortComplex.ab_exact_iff]
      exact hS j))

/--
error: failed to synthesize
  HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat

/-- Machine-readable W296 support state. -/
structure AddCommGrpWppOpKernelExactnessSupportState : Type where
  seed : String
  checkedConsumer : String
  remainingInputs : List String
  negativeGuards : List String
  productSuccessClaimed : Bool

/-- Reproducible W296 state for downstream workers. -/
def currentAddCommGrpWppOpKernelExactnessSupportState :
    AddCommGrpWppOpKernelExactnessSupportState where
  seed := "w296-20260520T173116Z-7a6a84871feb8b81"
  checkedConsumer :=
    "additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact"
  remainingInputs :=
    ["addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable",
      "or the stronger addCommGrpShortComplexExact_wppOp_colimit_boundary_for_metrizable"]
  negativeGuards :=
    ["no synthesized HasExactColimitsOfShape WalkingParallelPairᵒᵖ AddCommGrpCat"]
  productSuccessClaimed := false

theorem currentAddCommGrpWppOpKernelExactnessSupportState_productSuccess :
    currentAddCommGrpWppOpKernelExactnessSupportState.productSuccessClaimed = false := rfl

section Checks

#check AddCommGrpKernelExact
#check AdditiveKernelExact
#check additiveKernelExact_wppOp_colimit_boundary
#check addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable
#check addCommGrpKernelExact_iff_additiveKernelExact
#check additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact
#check addCommGrpKernelExact_of_shortComplex_exact
#check addCommGrpShortComplexExact_wppOp_colimit_boundary_for_metrizable
#check addCommGrpKernelExact_wppOp_colimit_boundary_of_shortComplexExact
#check currentAddCommGrpWppOpKernelExactnessSupportState
#check currentAddCommGrpWppOpKernelExactnessSupportState_productSuccess

end Checks

end AddCommGrpWppOpKernelExactnessSupportW296

end LeanLCAExactChallenge
