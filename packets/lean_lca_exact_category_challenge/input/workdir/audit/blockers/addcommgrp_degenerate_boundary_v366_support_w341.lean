import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
W341: AddCommGrp degenerate SnakeInput boundary consumer for v366.

This standalone support file copies the small W366 degenerate SnakeInput
construction and adds checked boundary consumers.  The main consumer reduces the
v362/W318 SnakeInput cokernel-row boundary to two non-circular colimit facts:
left injectivity at the colimit point and the existing strict kernel-exactness
boundary.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpDegenerateBoundaryV366SupportW341

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

/-- The zero short complex is the kernel of the zero map from itself to any short complex. -/
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

/-- Exactness plus left injectivity give the degenerate v362 SnakeInput certificate. -/
def strictSnakeCokernelData_of_exact_and_mono
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : T.Exact) [Mono T.f] :
    WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpStrictSnakeCokernelData T where
  input := degenerateSnakeInput T hT
  cokernelRowIso := Iso.refl T

/-- Element-level exactness plus left injectivity build the degenerate certificate. -/
theorem strictSnakeCokernelData_of_kernelExact_leftInjective
    (T : ShortComplex AddCommGrpCat.{0})
    (hleft : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective T)
    (hexact : WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpKernelExact T) :
    Nonempty (WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpStrictSnakeCokernelData T) := by
  haveI : Mono T.f := mono_f_of_addCommGrpLeftInjective T hleft
  exact ⟨strictSnakeCokernelData_of_exact_and_mono T
    (shortComplexExact_of_addCommGrpKernelExact T hexact)⟩

/--
The AddCommGrp left-injectivity-at-colimit boundary.  It has the same component
strictness assumptions as W318's SnakeInput boundary, but asks only for
left-injectivity of the colimit-point left map.
-/
abbrev addCommGrpLeftInjective_wppOp_colimit_boundary_for_metrizable : Prop :=
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
            (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/--
Closed-embedding component data version of the left-injectivity boundary.  This
is the form directly consumed by the pure LCA certificate.
-/
abbrev addCommGrpLeftInjective_wppOp_colimit_boundary_from_closedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          WppOpExactAcyclicFrontierConsolidatedW318.AddCommGrpLeftInjective
            (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/--
Combined degenerate statement: left injectivity at the colimit point plus strict
kernel exactness at the colimit point are exactly the remaining facts needed by
the copied W366 degenerate SnakeInput construction.
-/
abbrev addCommGrpDegenerateSnakeBoundary_leftInjective_strictKernelExact_statement : Prop :=
  addCommGrpLeftInjective_wppOp_colimit_boundary_for_metrizable →
    WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable →
      WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable

/--
The v362 SnakeInput boundary follows from the AddCommGrp left-injectivity
boundary and the existing strict kernel-exactness boundary.
-/
theorem addCommGrpDegenerateSnakeBoundary_of_leftInjective_and_strictKernelExact :
    addCommGrpDegenerateSnakeBoundary_leftInjective_strictKernelExact_statement := by
  intro hleftBoundary hkernelBoundary S cs hcs hS
  exact strictSnakeCokernelData_of_kernelExact_leftInjective
    (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (hleftBoundary S cs hcs hS)
    (hkernelBoundary S cs hcs hS)

/-- Named v362/W318 boundary consumer for the degenerate reduction. -/
theorem addCommGrpStrictSnakeCokernel_boundary_of_leftInjective_and_strictKernelExact
    (hleftBoundary : addCommGrpLeftInjective_wppOp_colimit_boundary_for_metrizable)
    (hkernelBoundary :
      WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable :=
  addCommGrpDegenerateSnakeBoundary_of_leftInjective_and_strictKernelExact
    hleftBoundary hkernelBoundary

/--
The pure W318 LCA certificate supplies the closed-embedding component version
of the AddCommGrp left-injectivity boundary.
-/
theorem addCommGrpLeftInjective_wppOp_colimit_boundary_of_lca_leftCertificate
    (hquot : WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage) :
    addCommGrpLeftInjective_wppOp_colimit_boundary_from_closedEmbedding := by
  intro S cs hcs hclosed
  let α : S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).f
      naturality := fun _ _ f => (S.map f).comm₁₂ }
  have h₁ : IsColimit
      ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) :=
    isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  have h₂ : IsColimit
      ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) :=
    isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  rcases hquot
    (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    cs.pt.f
    h₁ h₂ hclosed
    (fun j => (cs.ι.app j).comm₁₂) with ⟨hinj, _hind, _hclosedImage⟩
  exact hinj

/-- Machine-readable W341 support state. -/
structure AddCommGrpDegenerateBoundaryV366SupportState : Type where
  seed : String
  copiedFrom : List String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpDegenerateBoundaryV366SupportState :
    AddCommGrpDegenerateBoundaryV366SupportState where
  seed := "6e6a39f4bcfc80334db67c1b"
  copiedFrom :=
    ["W366 degenerate SnakeInput exact+mono construction"]
  provedConsumers :=
    ["strictSnakeCokernelData_of_kernelExact_leftInjective",
      "addCommGrpStrictSnakeCokernel_boundary_of_leftInjective_and_strictKernelExact",
      "addCommGrpLeftInjective_wppOp_colimit_boundary_of_lca_leftCertificate"]
  remainingInputs :=
    ["prove AddCommGrp left-injectivity at the WPP-op colimit point from the exact strict algebraic component hypotheses, or supply closed-embedding component hypotheses",
      "prove or provide the existing AddCommGrp strict kernel-exactness boundary",
      "optionally replace the degenerate certificate with a non-degenerate SnakeInput that proves these facts internally"]
  productSuccessClaimed := false

theorem currentAddCommGrpDegenerateBoundaryV366SupportState_productSuccess :
    currentAddCommGrpDegenerateBoundaryV366SupportState.productSuccessClaimed = false := rfl

section Checks

#check degenerateSnakeInput
#check strictSnakeCokernelData_of_kernelExact_leftInjective
#check addCommGrpLeftInjective_wppOp_colimit_boundary_for_metrizable
#check addCommGrpLeftInjective_wppOp_colimit_boundary_from_closedEmbedding
#check addCommGrpDegenerateSnakeBoundary_leftInjective_strictKernelExact_statement
#check addCommGrpDegenerateSnakeBoundary_of_leftInjective_and_strictKernelExact
#check addCommGrpStrictSnakeCokernel_boundary_of_leftInjective_and_strictKernelExact
#check addCommGrpLeftInjective_wppOp_colimit_boundary_of_lca_leftCertificate
#check currentAddCommGrpDegenerateBoundaryV366SupportState
#check currentAddCommGrpDegenerateBoundaryV366SupportState_productSuccess

end Checks

end AddCommGrpDegenerateBoundaryV366SupportW341

end LeanLCAExactChallenge
