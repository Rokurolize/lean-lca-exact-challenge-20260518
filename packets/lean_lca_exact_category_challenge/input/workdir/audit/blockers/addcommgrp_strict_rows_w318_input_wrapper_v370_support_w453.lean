import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.StrictExact

/-!
W453: W318 input wrappers from strict `MetrizableLCA` rows.

This support file packages the strict-row AddCommGrp facts in the shape expected
by the W318 frontier.  It deliberately leaves the concrete difference kernel
row, difference cokernel row, and colimit-row identification as explicit inputs.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpExactAcyclicFrontierConsolidatedW318
open AddCommGrpSnakeInputDifferenceCokernel

namespace AddCommGrpStrictRowsW318InputWrapperV370SupportW453

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeed : String :=
  "w453-20260521T102500Z-d196733e8efce505427a9cdd"

/-- The functor forgetting a short complex of metrizable LCA groups to abelian groups. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The forgotten ordinary-left arrow of the WPP-op short-complex diagram. -/
def selectedForgottenLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map
    (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left))

/-- The forgotten ordinary-right arrow of the WPP-op short-complex diagram. -/
def selectedForgottenRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map
    (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right))

/-- A strict short exact row supplies exactly W318's three AddCommGrp row inputs. -/
def addCommGrpStrictInputsOfStrictShortExact
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpLeftInjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
      AddCommGrpKernelExact (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpRightSurjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  ⟨hS.closed_inclusion.injective, hS.algebraic_exact, hS.surjective⟩

/-- A strict WPP-op family supplies W318's row-input family. -/
def addCommGrpStrictInputsFamilyOfStrictShortExact
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j)) :
    ∀ j,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  fun j => addCommGrpStrictInputsOfStrictShortExact (hS j)

/--
Consumer for W318's strict AddCommGrp kernel-exactness boundary using strict
component rows as the direct source of the row-input family.
-/
theorem addCommGrpKernelExact_colimit_of_boundary_and_strictRows
    (hboundary : addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable)
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hcs : IsColimit cs)
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j)) :
    AddCommGrpKernelExact (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  hboundary S cs hcs (addCommGrpStrictInputsFamilyOfStrictShortExact hS)

/--
The strict AddCommGrp boundary reduces W318's algebraic exactness closure to the
boundary plus strict component rows.
-/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_boundary
    (hboundary : addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact addCommGrpKernelExact_colimit_of_boundary_and_strictRows hboundary hcs hS

/--
The SnakeInput cokernel-row boundary also reduces W318's algebraic exactness
closure to the boundary plus strict component rows.
-/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_snakeBoundary
    (hsnake : addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    algebraicExact_walkingParallelPairOp_colimitClosure :=
  algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_boundary
    (addCommGrpStrictKernelExact_wppOp_colimit_boundary_of_snakeCokernel hsnake)

/--
Selected WPP-op source/target adapter for the difference-cokernel route.

The strictness side fields come from the ordinary source and target rows.  The
kernel row, cokernel row, difference map equation, and their universal
properties remain explicit inputs.
-/
def selectedWppOpParallelPairDifferenceStrictCokernelData_of_forgottenStrictRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j))
    {L₃ : ShortComplex AddCommGrpCat.{0}}
    (q :
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
        L₃)
    (w : (selectedForgottenLeft S - selectedForgottenRight S) ≫ q = 0 := by cat_disch)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i :
      L₀ ⟶
        (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi))
    (h₃ : IsColimit (CokernelCofork.ofπ q w)) :
    ParallelPairDifferenceStrictCokernelData
      ((S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      ((S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      L₃ where
  u := selectedForgottenLeft S
  v := selectedForgottenRight S
  q := q
  w := w
  L₀ := L₀
  i := i
  wi := wi
  h₀ := h₀
  h₃ := h₃
  L₁_kernelExact := (addCommGrpStrictInputsFamilyOfStrictShortExact hS ordinarySourceIndex).2.1
  L₁_rightSurjective := (addCommGrpStrictInputsFamilyOfStrictShortExact hS ordinarySourceIndex).2.2
  L₂_kernelExact := (addCommGrpStrictInputsFamilyOfStrictShortExact hS ordinaryTargetIndex).2.1
  L₂_leftInjective := (addCommGrpStrictInputsFamilyOfStrictShortExact hS ordinaryTargetIndex).1

/-- The selected WPP-op adapter directly supplies a SnakeInput cokernel-row certificate. -/
def strictSnakeCokernelData_of_selectedWppOpStrictRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j))
    {L₃ T : ShortComplex AddCommGrpCat.{0}}
    (q :
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
        L₃)
    (w : (selectedForgottenLeft S - selectedForgottenRight S) ≫ q = 0 := by cat_disch)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i :
      L₀ ⟶
        (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi))
    (h₃ : IsColimit (CokernelCofork.ofπ q w))
    (e : L₃ ≅ T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    (selectedWppOpParallelPairDifferenceStrictCokernelData_of_forgottenStrictRows
      hS q w L₀ i wi h₀ h₃)
    e

/-- Machine-readable W453 support state. -/
structure AddCommGrpStrictRowsW318InputWrapperV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  w318InputWrapperResult : String
  snakeBoundaryConsumerResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W453. -/
def currentAddCommGrpStrictRowsW318InputWrapperV370SupportState :
    AddCommGrpStrictRowsW318InputWrapperV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["addCommGrpStrictInputsOfStrictShortExact",
      "addCommGrpStrictInputsFamilyOfStrictShortExact",
      "addCommGrpKernelExact_colimit_of_boundary_and_strictRows",
      "algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_boundary",
      "algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_snakeBoundary",
      "ordinarySourceIndex",
      "ordinaryTargetIndex",
      "selectedForgottenLeft",
      "selectedForgottenRight",
      "selectedWppOpParallelPairDifferenceStrictCokernelData_of_forgottenStrictRows",
      "strictSnakeCokernelData_of_selectedWppOpStrictRows"]
  w318InputWrapperResult := "proved"
  snakeBoundaryConsumerResult := "proved"
  remainingInputs :=
    ["construct the concrete difference kernel row",
      "construct the concrete difference cokernel row",
      "prove the selected target cofork is the required cokernel cofork",
      "identify the difference cokernel row with cs.pt.map (forget₂ MetrizableLCA AddCommGrpCat)"]
  productSuccessClaimed := false

theorem currentAddCommGrpStrictRowsW318InputWrapperV370SupportState_productSuccess :
    currentAddCommGrpStrictRowsW318InputWrapperV370SupportState.productSuccessClaimed =
      false := rfl

section Checks

#check supportSeed
#check forgottenShortComplexFunctor
#check ordinarySourceIndex
#check ordinaryTargetIndex
#check selectedForgottenLeft
#check selectedForgottenRight
#check addCommGrpStrictInputsOfStrictShortExact
#check addCommGrpStrictInputsFamilyOfStrictShortExact
#check addCommGrpKernelExact_colimit_of_boundary_and_strictRows
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_boundary
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_strictRows_snakeBoundary
#check selectedWppOpParallelPairDifferenceStrictCokernelData_of_forgottenStrictRows
#check strictSnakeCokernelData_of_selectedWppOpStrictRows
#check currentAddCommGrpStrictRowsW318InputWrapperV370SupportState
#check currentAddCommGrpStrictRowsW318InputWrapperV370SupportState_productSuccess

end Checks

end AddCommGrpStrictRowsW318InputWrapperV370SupportW453

end LeanLCAExactChallenge
