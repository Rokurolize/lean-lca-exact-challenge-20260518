import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
W366: degenerate SnakeInput support for the AddCommGrp frontier.

The v362 route asks for a `SnakeInput` whose cokernel row is the underlying
`AddCommGrpCat` short complex at the WPP-op colimit.  This file records a
checked lower bound on that route: if the target short complex is already exact
and its left map is mono, then it can be presented as the cokernel row of the
degenerate snake input `0 -> T -> T`.

This is not a product-completion claim.  Its purpose is to make the remaining
SnakeInput work sharper: a non-degenerate construction is only useful if it
proves the missing exactness/mono facts rather than repackaging them.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpDegenerateSnakeSupportW366

/-- The explicit zero short complex over `AddCommGrpCat`. -/
abbrev zeroShortComplex : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk
    (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of PUnit)
    (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of PUnit)
    (by simp)

/-- The zero short complex is exact. -/
theorem zeroShortComplex_exact : zeroShortComplex.Exact := by
  exact ShortComplex.exact_of_isZero_X₂ zeroShortComplex (by
    dsimp [zeroShortComplex]
    exact AddCommGrpCat.isZero_of_subsingleton _)

/-- The right map of the zero short complex is epi. -/
theorem zeroShortComplex_epi_g : Epi zeroShortComplex.g := by
  rw [show zeroShortComplex.g = 𝟙 (AddCommGrpCat.of PUnit) by
    ext x]
  infer_instance

/--
The zero short complex is the kernel of the zero map from itself to any short
complex.
-/
def zeroShortComplex_kernel_zero (T : ShortComplex AddCommGrpCat.{0}) :
    IsLimit
      (KernelFork.ofι (0 : zeroShortComplex ⟶ zeroShortComplex)
        (by simp : (0 : zeroShortComplex ⟶ zeroShortComplex) ≫
          (0 : zeroShortComplex ⟶ T) = 0)) := by
  refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg => 0) ?_ ?_
  · intro W g hg
    ext x
  · intro W g hg m hm
    ext x

/-- The identity map presents `T` as the cokernel of `0 : 0 -> T`. -/
def identity_isCokernel_zero (T : ShortComplex AddCommGrpCat.{0}) :
    IsColimit
      (CokernelCofork.ofπ (𝟙 T)
        (by simp : (0 : zeroShortComplex ⟶ T) ≫ (𝟙 T) = 0)) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {Z} g hg => g) ?_ ?_
  · intro Z g hg
    simp
  · intro Z g hg m hm
    simpa using hm

/--
Degenerate snake input with `L₁ = 0`, `L₂ = T`, and `L₃ = T`.

This is useful as a guardrail: a SnakeInput certificate for the frontier is
substantive only when it supplies the exactness and mono facts, not when those
facts are already assumed.
-/
def degenerateSnakeInput (T : ShortComplex AddCommGrpCat.{0})
    (hT : T.Exact) [Mono T.f] :
    ShortComplex.SnakeInput AddCommGrpCat.{0} where
  L₀ := zeroShortComplex
  L₁ := zeroShortComplex
  L₂ := T
  L₃ := T
  v₀₁ := 0
  v₁₂ := 0
  v₂₃ := 𝟙 T
  h₀ := zeroShortComplex_kernel_zero T
  h₃ := identity_isCokernel_zero T
  L₁_exact := zeroShortComplex_exact
  epi_L₁_g := zeroShortComplex_epi_g
  L₂_exact := hT
  mono_L₂_f := inferInstance

/-- AddCommGrp element-level kernel exactness is the concrete form of `ShortComplex.Exact`. -/
theorem shortComplexExact_of_addCommGrpKernelExact
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpKernelExact T) :
    T.Exact := by
  rw [ShortComplex.ab_exact_iff]
  exact hT

/-- A left-injective AddCommGrp short-complex map is mono categorically. -/
theorem mono_f_of_addCommGrpLeftInjective
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective T) :
    Mono T.f :=
  (AddCommGrpCat.mono_iff_injective T.f).mpr hT

/--
If a short complex is already exact and its left map is mono, it has the v362
SnakeInput cokernel-row certificate.
-/
def strictSnakeCokernelData_of_exact_and_mono
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : T.Exact) [Mono T.f] :
    WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpStrictSnakeCokernelData T where
  input := degenerateSnakeInput T hT
  cokernelRowIso := Iso.refl T

/--
Element-level exactness plus left injectivity are enough to build the
degenerate SnakeInput certificate.
-/
theorem strictSnakeCokernelData_of_kernelExact_leftInjective
    (T : ShortComplex AddCommGrpCat.{0})
    (hleft : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective T)
    (hexact : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpKernelExact T) :
    Nonempty (WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpStrictSnakeCokernelData T) := by
  haveI : Mono T.f := mono_f_of_addCommGrpLeftInjective T hleft
  exact ⟨strictSnakeCokernelData_of_exact_and_mono T
    (shortComplexExact_of_addCommGrpKernelExact T hexact)⟩

/--
Boundary form: the v362 SnakeInput boundary follows if the WPP-op colimit point
is known to retain left injectivity and AddCommGrp kernel exactness.
-/
abbrev addCommGrpDegenerateSnakeBoundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective
              ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
            WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpKernelExact
              ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
              WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpRightSurjective
                ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective
              (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
            WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpKernelExact
              (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/--
The degenerate exact+mono boundary supplies the v362 SnakeInput boundary.
-/
theorem addCommGrpStrictSnakeCokernel_boundary_of_degenerate
    (hboundary : addCommGrpDegenerateSnakeBoundary_for_metrizable) :
    WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hS
  rcases hboundary S cs hcs hS with ⟨hleft, hexact⟩
  exact strictSnakeCokernelData_of_kernelExact_leftInjective
    (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) hleft hexact

/-- Machine-readable W366 support state. -/
structure AddCommGrpDegenerateSnakeSupportState : Type where
  checkedTheorems : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpDegenerateSnakeSupportState :
    AddCommGrpDegenerateSnakeSupportState where
  checkedTheorems :=
    ["zeroShortComplex_exact",
      "zeroShortComplex_epi_g",
      "zeroShortComplex_kernel_zero",
      "identity_isCokernel_zero",
      "degenerateSnakeInput",
      "shortComplexExact_of_addCommGrpKernelExact",
      "mono_f_of_addCommGrpLeftInjective",
      "strictSnakeCokernelData_of_exact_and_mono",
      "strictSnakeCokernelData_of_kernelExact_leftInjective",
      "addCommGrpStrictSnakeCokernel_boundary_of_degenerate"]
  remainingInputs :=
    ["prove the WPP-op colimit point retains AddCommGrp left injectivity",
      "prove the WPP-op colimit point retains AddCommGrp kernel exactness",
      "or build a non-degenerate SnakeInput that proves these facts rather than assuming them"]
  productSuccessClaimed := false

theorem currentAddCommGrpDegenerateSnakeSupportState_productSuccess :
    currentAddCommGrpDegenerateSnakeSupportState.productSuccessClaimed = false := rfl

section Checks

#check zeroShortComplex
#check zeroShortComplex_exact
#check zeroShortComplex_epi_g
#check zeroShortComplex_kernel_zero
#check identity_isCokernel_zero
#check degenerateSnakeInput
#check shortComplexExact_of_addCommGrpKernelExact
#check mono_f_of_addCommGrpLeftInjective
#check strictSnakeCokernelData_of_exact_and_mono
#check strictSnakeCokernelData_of_kernelExact_leftInjective
#check addCommGrpDegenerateSnakeBoundary_for_metrizable
#check addCommGrpStrictSnakeCokernel_boundary_of_degenerate
#check currentAddCommGrpDegenerateSnakeSupportState
#check currentAddCommGrpDegenerateSnakeSupportState_productSuccess

end Checks

end AddCommGrpDegenerateSnakeSupportW366

end LeanLCAExactChallenge
