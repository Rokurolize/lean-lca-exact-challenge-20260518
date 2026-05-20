import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W338: `AddCommGrp` SnakeInput cokernel-row support for the v362 boundary.

This file records the checked part of the strict algebraic route: mathlib's
`ShortComplex.SnakeInput` names the cokernel row as `L₃`, exposes the cokernel
cofork proof as `h₃`, and proves that `L₃` is exact as `L₃_exact`.  The v362
boundary may therefore ask for an isomorphism from this `L₃` row to the WPP-op
colimit short complex and consume exactness through the existing W318 bridge.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpExactAcyclicFrontierConsolidatedW318
namespace AddCommGrpSnakeCokernelV362SupportW338

/-- Local abbreviation for the certificate shape required by the v362 boundary. -/
abbrev SnakeCokernelRowCertificate (T : ShortComplex AddCommGrpCat.{0}) : Prop :=
  Nonempty (AddCommGrpStrictSnakeCokernelData T)

/-- Mathlib's snake input exposes its cokernel row as `L₃`. -/
abbrev snakeInputCokernelRow (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    ShortComplex AddCommGrpCat.{0} :=
  S.L₃

/-- The snake input field `h₃` says that `L₃` is the cokernel row of `v₁₂`. -/
def snakeInput_cokernelRow_isColimit
    (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    IsColimit (CokernelCofork.ofπ S.v₂₃ S.w₁₃) :=
  S.h₃

/-- The dual kernel-row field is `h₀`; it is recorded to avoid row-name ambiguity. -/
def snakeInput_kernelRow_isLimit
    (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    IsLimit (KernelFork.ofι S.v₀₁ S.w₀₂) :=
  S.h₀

/-- The first middle row exactness field is named `L₁_exact`. -/
theorem snakeInput_firstMiddleRow_exact
    (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    S.L₁.Exact :=
  S.L₁_exact

/-- The second middle row exactness field is named `L₂_exact`. -/
theorem snakeInput_secondMiddleRow_exact
    (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    S.L₂.Exact :=
  S.L₂_exact

/-- Mathlib proves exactness of the cokernel row as `ShortComplex.SnakeInput.L₃_exact`. -/
theorem snakeInput_cokernelRow_exact
    (S : ShortComplex.SnakeInput AddCommGrpCat.{0}) :
    (snakeInputCokernelRow S).Exact :=
  S.L₃_exact

/-- A v362 cokernel-row certificate gives categorical exactness of the target row. -/
theorem exact_of_strictSnakeCokernelData
    (T : ShortComplex AddCommGrpCat.{0})
    (d : AddCommGrpStrictSnakeCokernelData T) :
    T.Exact :=
  ShortComplex.exact_of_iso d.cokernelRowIso d.input.L₃_exact

/-- A nonempty v362 cokernel-row certificate gives categorical exactness. -/
theorem exact_of_snakeCokernelRowCertificate
    (T : ShortComplex AddCommGrpCat.{0})
    (h : SnakeCokernelRowCertificate T) :
    T.Exact := by
  rcases h with ⟨d⟩
  exact exact_of_strictSnakeCokernelData T d

/--
The checked consumer already in W318 turns a v362 cokernel-row certificate into
the strict `AddCommGrp` kernel-exactness field used by the algebraic boundary.
-/
theorem addCommGrpKernelExact_of_snakeCokernelRowCertificate
    (T : ShortComplex AddCommGrpCat.{0})
    (h : SnakeCokernelRowCertificate T) :
    AddCommGrpKernelExact T := by
  rcases h with ⟨d⟩
  exact addCommGrpKernelExact_of_strictSnakeCokernelData T d

/--
The v362 boundary is exactly the WPP-op colimit request for the local
`SnakeCokernelRowCertificate` shape.
-/
theorem v362Boundary_iff_snakeCokernelRowCertificateBoundary :
    addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable ↔
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S),
          IsColimit cs →
            (∀ j : WalkingParallelPairᵒᵖ,
              AddCommGrpLeftInjective
                  ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
                AddCommGrpKernelExact
                  ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
                  AddCommGrpRightSurjective
                    ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
              SnakeCokernelRowCertificate
                (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) := by
  rfl

/-- Machine-readable W338 state. -/
structure AddCommGrpSnakeCokernelV362SupportState : Type where
  seed : String
  checkedApi : List String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W338 support state. -/
def currentAddCommGrpSnakeCokernelV362SupportState :
    AddCommGrpSnakeCokernelV362SupportState where
  seed := "w338-20260520T200551Z-82791f0165cad83b"
  checkedApi :=
    ["ShortComplex.SnakeInput.L₃",
      "ShortComplex.SnakeInput.h₃",
      "ShortComplex.SnakeInput.L₁_exact",
      "ShortComplex.SnakeInput.L₂_exact",
      "ShortComplex.SnakeInput.L₃_exact"]
  provedConsumers :=
    ["snakeInput_cokernelRow_isColimit",
      "snakeInput_cokernelRow_exact",
      "exact_of_strictSnakeCokernelData",
      "addCommGrpKernelExact_of_snakeCokernelRowCertificate",
      "v362Boundary_iff_snakeCokernelRowCertificateBoundary"]
  remainingInputs :=
    ["construct a ShortComplex.SnakeInput whose L₃ is isomorphic to the WPP-op colimit short complex",
      "identify the cokernel cofork/coequalizer comparison isomorphisms for that concrete WPP-op colimit"]
  productSuccessClaimed := false

theorem currentAddCommGrpSnakeCokernelV362SupportState_productSuccess :
    currentAddCommGrpSnakeCokernelV362SupportState.productSuccessClaimed = false := rfl

section Checks

#check SnakeCokernelRowCertificate
#check snakeInputCokernelRow
#check snakeInput_cokernelRow_isColimit
#check snakeInput_kernelRow_isLimit
#check snakeInput_firstMiddleRow_exact
#check snakeInput_secondMiddleRow_exact
#check snakeInput_cokernelRow_exact
#check exact_of_strictSnakeCokernelData
#check exact_of_snakeCokernelRowCertificate
#check addCommGrpKernelExact_of_snakeCokernelRowCertificate
#check v362Boundary_iff_snakeCokernelRowCertificateBoundary
#check currentAddCommGrpSnakeCokernelV362SupportState
#check currentAddCommGrpSnakeCokernelV362SupportState_productSuccess

end Checks

end AddCommGrpSnakeCokernelV362SupportW338
end WppOpExactAcyclicFrontierConsolidatedW318

end LeanLCAExactChallenge
