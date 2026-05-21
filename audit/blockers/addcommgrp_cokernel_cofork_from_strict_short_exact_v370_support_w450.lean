import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.StrictExact

/-!
W450: AddCommGrp cokernel cofork from a strict short exact sequence.

This file isolates the algebraic boundary needed by the strict snake route: after
forgetting topology from a strict short exact `MetrizableLCA` short complex, the
right map is a cokernel cofork of the left map.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpExactAcyclicFrontierConsolidatedW318
open AddCommGrpSnakeInputDifferenceCokernel

namespace AddCommGrpCokernelCoforkFromStrictShortExactV370SupportW450

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeed : String :=
  "w450-20260521T005956Z-5d765b6e0f7677a1"

/-- Strict exactness gives left injectivity after forgetting topology. -/
theorem forgottenStrictShortExact_leftInjective
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpLeftInjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) := by
  exact hS.closed_inclusion.injective

/-- Strict exactness gives middle kernel exactness after forgetting topology. -/
theorem forgottenStrictShortExact_kernelExact
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpKernelExact (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) := by
  exact hS.algebraic_exact

/-- Strict exactness gives right surjectivity after forgetting topology. -/
theorem forgottenStrictShortExact_rightSurjective
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpRightSurjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) := by
  exact hS.surjective

/-- The forgotten strict short exact sequence is short exact in `AddCommGrpCat`. -/
def forgottenStrictShortExact_shortExact
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})).ShortExact where
  exact := by
    simpa using MetrizableLCA.forgetToAddCommGrpCat_exact_of_strict (S := S) hS
  mono_f := by
    rw [AddCommGrpCat.mono_iff_injective]
    exact forgottenStrictShortExact_leftInjective hS
  epi_g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact forgottenStrictShortExact_rightSurjective hS

/--
After forgetting topology, the right map of a strict short exact sequence is a
cokernel cofork of the left map.
-/
def forgottenStrictShortExactCokernelCoforkIsColimit
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    IsColimit
      (CokernelCofork.ofπ
        ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).map S.g)
        (by
          simpa using
            (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})).zero)) := by
  simpa using ShortComplex.ShortExact.gIsCokernel
    (forgottenStrictShortExact_shortExact hS)

/--
Adapter for W345: strict `MetrizableLCA` source rows supply the exact, epi, and
mono side fields of `ParallelPairDifferenceStrictCokernelData`; the remaining
inputs are precisely the kernel row, cokernel row, and maps for the difference.
-/
def parallelPairDifferenceStrictCokernelData_of_forgottenStrictRows
    {L₁ L₂ : ShortComplex MetrizableLCA.{0}}
    {L₃ : ShortComplex AddCommGrpCat.{0}}
    (hL₁ : MetrizableLCA.strictShortExact L₁)
    (hL₂ : MetrizableLCA.strictShortExact L₂)
    (u v :
      L₁.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
        L₂.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (q : L₂.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶ L₃)
    (w : (u - v) ≫ q = 0 := by cat_disch)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i : L₀ ⟶ L₁.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (u - v) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi))
    (h₃ : IsColimit (CokernelCofork.ofπ q w)) :
    ParallelPairDifferenceStrictCokernelData
      (L₁.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      (L₂.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      L₃ where
  u := u
  v := v
  q := q
  w := w
  L₀ := L₀
  i := i
  wi := wi
  h₀ := h₀
  h₃ := h₃
  L₁_kernelExact := forgottenStrictShortExact_kernelExact hL₁
  L₁_rightSurjective := forgottenStrictShortExact_rightSurjective hL₁
  L₂_kernelExact := forgottenStrictShortExact_kernelExact hL₂
  L₂_leftInjective := forgottenStrictShortExact_leftInjective hL₂

/-- Machine-readable W450 state. -/
structure AddCommGrpCokernelCoforkFromStrictShortExactSupportState : Type where
  seed : String
  checkedDeclarations : List String
  proofBoundary : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W450. -/
def currentAddCommGrpCokernelCoforkFromStrictShortExactSupportState :
    AddCommGrpCokernelCoforkFromStrictShortExactSupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["forgottenStrictShortExact_leftInjective",
      "forgottenStrictShortExact_kernelExact",
      "forgottenStrictShortExact_rightSurjective",
      "forgottenStrictShortExact_shortExact",
      "forgottenStrictShortExactCokernelCoforkIsColimit",
      "parallelPairDifferenceStrictCokernelData_of_forgottenStrictRows"]
  proofBoundary :=
    ["left injectivity is hS.closed_inclusion.injective",
      "middle kernel exactness is hS.algebraic_exact plus the short-complex zero relation already used by forgetToAddCommGrpCat_exact_of_strict",
      "right surjectivity is hS.surjective",
      "the cokernel cofork result follows from ShortComplex.ShortExact.gIsCokernel in AddCommGrpCat"]
  remainingInputs :=
    ["construct the concrete difference kernel row",
      "construct the concrete difference cokernel row",
      "identify the WPP-op colimit short complex with that cokernel row"]
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelCoforkFromStrictShortExactSupportState_productSuccess :
    currentAddCommGrpCokernelCoforkFromStrictShortExactSupportState.productSuccessClaimed =
      false := rfl

section Checks

#check supportSeed
#check forgottenStrictShortExact_leftInjective
#check forgottenStrictShortExact_kernelExact
#check forgottenStrictShortExact_rightSurjective
#check forgottenStrictShortExact_shortExact
#check forgottenStrictShortExactCokernelCoforkIsColimit
#check parallelPairDifferenceStrictCokernelData_of_forgottenStrictRows
#check currentAddCommGrpCokernelCoforkFromStrictShortExactSupportState
#check currentAddCommGrpCokernelCoforkFromStrictShortExactSupportState_productSuccess

end Checks

end AddCommGrpCokernelCoforkFromStrictShortExactV370SupportW450

end LeanLCAExactChallenge
