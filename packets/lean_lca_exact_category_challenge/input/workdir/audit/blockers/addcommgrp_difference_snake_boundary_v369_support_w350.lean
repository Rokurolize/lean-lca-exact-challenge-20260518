import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel

/-!
W350: difference-Snake boundary support for the v369 AddCommGrp branch.

This file packages the concrete remaining inputs for the W318 SnakeInput
cokernel-row boundary.  It does not construct those inputs; it checks that once
the difference kernel row, difference cokernel row, and cokernel-row
identification are available, the existing v369 `ParallelPairDifference...`
constructor supplies W318's boundary.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpDifferenceSnakeBoundaryV369SupportW350

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/--
Concrete remaining inputs for the AddCommGrp difference-Snake route to a target
short complex `T`.

The first row is the difference-kernel row, the third row is the
difference-cokernel row, and `cokernelRowIso` identifies that cokernel row with
the target short complex.
-/
structure DifferenceSnakeBoundaryInputs
    (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  differenceKernelRow : ShortComplex AddCommGrpCat.{0}
  differenceMiddleRow : ShortComplex AddCommGrpCat.{0}
  differenceCokernelRow : ShortComplex AddCommGrpCat.{0}
  differenceData :
    ParallelPairDifferenceStrictCokernelData
      differenceKernelRow differenceMiddleRow differenceCokernelRow
  cokernelRowIso : differenceCokernelRow ≅ T

/--
The packaged difference-Snake inputs give the strict SnakeInput cokernel-row
certificate required by W318.
-/
def strictSnakeCokernelData_of_differenceSnakeBoundaryInputs
    {T : ShortComplex AddCommGrpCat.{0}}
    (D : DifferenceSnakeBoundaryInputs T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D.differenceData D.cokernelRowIso

/--
Element-level exactness consumer for the packaged difference-Snake inputs.
-/
theorem addCommGrpKernelExact_of_differenceSnakeBoundaryInputs
    {T : ShortComplex AddCommGrpCat.{0}}
    (D : DifferenceSnakeBoundaryInputs T) :
    AddCommGrpKernelExact T :=
  addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    D.differenceData D.cokernelRowIso

/--
Boundary statement whose only payload is the remaining concrete difference-Snake
input package at each WPP-op colimit target.
-/
abbrev addCommGrpDifferenceSnakeBoundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          AddCommGrpLeftInjective
              ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
            AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
              AddCommGrpRightSurjective
                ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          Nonempty
            (DifferenceSnakeBoundaryInputs
              (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))

/--
Checked boundary consumer: a boundary that supplies the difference-Snake input
package at the WPP-op colimit target gives W318's strict SnakeInput cokernel
boundary.
-/
theorem addCommGrpStrictSnakeCokernel_boundary_of_differenceSnakeBoundary
    (hboundary : addCommGrpDifferenceSnakeBoundary_for_metrizable) :
    addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hS
  rcases hboundary S cs hcs hS with ⟨D⟩
  exact ⟨strictSnakeCokernelData_of_differenceSnakeBoundaryInputs D⟩

/--
Combined consumer into W318's exact-acyclic closure theorem: after the left LCA
boundary, the algebraic remaining input can be stated as the difference-Snake
package boundary.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_differenceSnake
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hsnake : addCommGrpDifferenceSnakeBoundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel
    hclosed
    (addCommGrpStrictSnakeCokernel_boundary_of_differenceSnakeBoundary hsnake)

/-- Machine-readable W350 support state. -/
structure AddCommGrpDifferenceSnakeBoundaryV369SupportState : Type where
  seed : String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpDifferenceSnakeBoundaryV369SupportState :
    AddCommGrpDifferenceSnakeBoundaryV369SupportState where
  seed := "Dkvs3xuFTj3vJpDMvfgTgw5m"
  provedConsumers :=
    ["strictSnakeCokernelData_of_differenceSnakeBoundaryInputs",
      "addCommGrpKernelExact_of_differenceSnakeBoundaryInputs",
      "addCommGrpStrictSnakeCokernel_boundary_of_differenceSnakeBoundary",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_differenceSnake"]
  remainingInputs :=
    ["construct the concrete difference kernel row",
      "construct the concrete difference cokernel row",
      "identify the difference cokernel row with cs.pt.map (forget₂ MetrizableLCA AddCommGrpCat)"]
  productSuccessClaimed := false

theorem currentAddCommGrpDifferenceSnakeBoundaryV369SupportState_productSuccess :
    currentAddCommGrpDifferenceSnakeBoundaryV369SupportState.productSuccessClaimed = false := rfl

section Checks

#check DifferenceSnakeBoundaryInputs
#check strictSnakeCokernelData_of_differenceSnakeBoundaryInputs
#check addCommGrpKernelExact_of_differenceSnakeBoundaryInputs
#check addCommGrpDifferenceSnakeBoundary_for_metrizable
#check addCommGrpStrictSnakeCokernel_boundary_of_differenceSnakeBoundary
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_differenceSnake
#check currentAddCommGrpDifferenceSnakeBoundaryV369SupportState
#check currentAddCommGrpDifferenceSnakeBoundaryV369SupportState_productSuccess

end Checks

end AddCommGrpDifferenceSnakeBoundaryV369SupportW350

end LeanLCAExactChallenge
