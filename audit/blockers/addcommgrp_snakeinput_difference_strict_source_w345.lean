import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel

/-!
W345: source-backed AddCommGrp SnakeInput difference-cokernel support.

This audit file fixes the checked API added in
`LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel`.  It
narrows the strict AddCommGrp frontier to three concrete row-construction tasks:
the difference kernel row, the difference cokernel row, and the isomorphism from
that cokernel row to the WPP-op colimit short complex.

No product-completion claim is made here.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

namespace AddCommGrpSnakeInputDifferenceCokernelW345

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

def w345SourceDeclarationNames : List String :=
  ["shortComplexExact_of_addCommGrpKernelExact",
    "epi_g_of_addCommGrpRightSurjective",
    "mono_f_of_addCommGrpLeftInjective",
    "DifferenceCokernelSnakeInputData",
    "ParallelPairDifferenceCokernelData",
    "ParallelPairDifferenceStrictCokernelData",
    "parallelPairDifferenceCokernelData_of_strictData",
    "snakeInput_of_parallelPairDifferenceStrictCokernelData",
    "parallelPair_strictSnakeInput_v₁₂",
    "strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData",
    "addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData"]

theorem w345SourceDeclarationNames_count :
    w345SourceDeclarationNames.length = 11 := rfl

structure W345SourceSupportState : Type where
  sourceModule : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentW345SourceSupportState : W345SourceSupportState where
  sourceModule := "LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel"
  remainingInputs :=
    ["construct the difference kernel row from the concrete WPP-op source pair",
      "construct the difference cokernel row from the concrete WPP-op target cofork",
      "identify the WPP-op colimit short complex with that cokernel row"]
  productSuccessClaimed := false

theorem currentW345SourceSupportState_productSuccess :
    currentW345SourceSupportState.productSuccessClaimed = false := rfl

section Checks

#check shortComplexExact_of_addCommGrpKernelExact
#check epi_g_of_addCommGrpRightSurjective
#check mono_f_of_addCommGrpLeftInjective
#check DifferenceCokernelSnakeInputData
#check ParallelPairDifferenceCokernelData
#check ParallelPairDifferenceStrictCokernelData
#check parallelPairDifferenceCokernelData_of_strictData
#check snakeInput_of_parallelPairDifferenceStrictCokernelData
#check parallelPair_strictSnakeInput_v₁₂
#check strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
#check addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
#check currentAddCommGrpSnakeInputDifferenceCokernelState
#check currentAddCommGrpSnakeInputDifferenceCokernelState_productSuccess
#check w345SourceDeclarationNames_count
#check currentW345SourceSupportState_productSuccess

end Checks

end AddCommGrpSnakeInputDifferenceCokernelW345

end LeanLCAExactChallenge

