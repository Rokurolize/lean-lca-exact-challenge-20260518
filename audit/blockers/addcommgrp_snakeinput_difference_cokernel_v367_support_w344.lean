import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
W344: SnakeInput support for difference-cokernel rows in `AddCommGrpCat`.

For a parallel pair of morphisms of exact short complexes, the coequalizer row is
expected to be the cokernel row of the difference morphism `u - v`.  This file
records the checked API bridge: once the kernel row, cokernel row, exactness, and
strictness inputs required by mathlib's `ShortComplex.SnakeInput` are available,
the difference morphism packages directly into the v362
`AddCommGrpStrictSnakeCokernelData` certificate consumed by W318.

No product-completion claim is made here.  The remaining frontier is the concrete
construction of those row certificates from the WPP-op colimit/cofork data.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpExactAcyclicFrontierConsolidatedW318
namespace AddCommGrpSnakeInputDifferenceCokernelV367SupportW344

/--
Explicit input data for building a `SnakeInput` whose cokernel row is `L₃` for a
chosen difference-like morphism `d : L₁ ⟶ L₂`.

The fields mirror mathlib's `ShortComplex.SnakeInput` obligations, so this
structure is an API map rather than an unproved existence theorem.
-/
structure DifferenceCokernelSnakeInputData
    (L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  d : L₁ ⟶ L₂
  q : L₂ ⟶ L₃
  w : d ≫ q = 0 := by cat_disch
  L₀ : ShortComplex AddCommGrpCat.{0}
  i : L₀ ⟶ L₁
  wi : i ≫ d = 0 := by cat_disch
  h₀ : IsLimit (KernelFork.ofι i wi)
  h₃ : IsColimit (CokernelCofork.ofπ q w)
  L₁_exact : L₁.Exact
  epi_L₁_g : Epi L₁.g
  L₂_exact : L₂.Exact
  mono_L₂_f : Mono L₂.f

/-- Constructor from explicit difference-cokernel data to mathlib's `SnakeInput`. -/
def snakeInput_of_differenceCokernelData
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : DifferenceCokernelSnakeInputData L₁ L₂ L₃) :
    ShortComplex.SnakeInput AddCommGrpCat.{0} where
  L₀ := D.L₀
  L₁ := L₁
  L₂ := L₂
  L₃ := L₃
  v₀₁ := D.i
  v₁₂ := D.d
  v₂₃ := D.q
  w₀₂ := D.wi
  w₁₃ := D.w
  h₀ := D.h₀
  h₃ := D.h₃
  L₁_exact := D.L₁_exact
  epi_L₁_g := D.epi_L₁_g
  L₂_exact := D.L₂_exact
  mono_L₂_f := D.mono_L₂_f

/-- The constructed snake input uses the supplied cokernel row as its `L₃`. -/
theorem snakeInput_of_differenceCokernelData_L₃
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : DifferenceCokernelSnakeInputData L₁ L₂ L₃) :
    (snakeInput_of_differenceCokernelData D).L₃ = L₃ := rfl

/--
The explicit difference-cokernel data gives the v362 strict SnakeInput certificate
for any target row identified with the constructed cokernel row.
-/
def strictSnakeCokernelData_of_differenceCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : DifferenceCokernelSnakeInputData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpStrictSnakeCokernelData T where
  input := snakeInput_of_differenceCokernelData D
  cokernelRowIso := e

/--
Specialized input data for a parallel pair `u v`, where the middle vertical map
of the snake input is exactly the difference morphism `u - v`.
-/
structure ParallelPairDifferenceCokernelData
    (L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  u : L₁ ⟶ L₂
  v : L₁ ⟶ L₂
  q : L₂ ⟶ L₃
  w : (u - v) ≫ q = 0 := by cat_disch
  L₀ : ShortComplex AddCommGrpCat.{0}
  i : L₀ ⟶ L₁
  wi : i ≫ (u - v) = 0 := by cat_disch
  h₀ : IsLimit (KernelFork.ofι i wi)
  h₃ : IsColimit (CokernelCofork.ofπ q w)
  L₁_exact : L₁.Exact
  epi_L₁_g : Epi L₁.g
  L₂_exact : L₂.Exact
  mono_L₂_f : Mono L₂.f

/-- Forget the parallel-pair presentation and retain the difference morphism. -/
def differenceCokernelData_of_parallelPair
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) :
    DifferenceCokernelSnakeInputData L₁ L₂ L₃ where
  d := D.u - D.v
  q := D.q
  w := D.w
  L₀ := D.L₀
  i := D.i
  wi := D.wi
  h₀ := D.h₀
  h₃ := D.h₃
  L₁_exact := D.L₁_exact
  epi_L₁_g := D.epi_L₁_g
  L₂_exact := D.L₂_exact
  mono_L₂_f := D.mono_L₂_f

/-- Build a snake input whose middle map is the difference `u - v`. -/
def snakeInput_of_parallelPairDifferenceCokernelData
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) :
    ShortComplex.SnakeInput AddCommGrpCat.{0} :=
  snakeInput_of_differenceCokernelData (differenceCokernelData_of_parallelPair D)

/-- The middle vertical map of the constructed snake input is definitionally `u - v`. -/
theorem parallelPair_snakeInput_v₁₂
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) :
    (snakeInput_of_parallelPairDifferenceCokernelData D).v₁₂ = D.u - D.v := rfl

/--
Parallel-pair difference-cokernel data gives the v362 strict SnakeInput
certificate for any target row identified with the supplied cokernel row.
-/
def strictSnakeCokernelData_of_parallelPairDifferenceCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_differenceCokernelData
    (differenceCokernelData_of_parallelPair D) e

/-- Checked W318 consumer: the parallel-pair bridge supplies AddCommGrp kernel exactness. -/
theorem addCommGrpKernelExact_of_parallelPairDifferenceCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpKernelExact T :=
  addCommGrpKernelExact_of_strictSnakeCokernelData T
    (strictSnakeCokernelData_of_parallelPairDifferenceCokernelData D e)

/-- Machine-readable W344 state. -/
structure AddCommGrpSnakeInputDifferenceCokernelSupportState : Type where
  seed : String
  checkedConstructors : List String
  explicitInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W344 support state. -/
def currentAddCommGrpSnakeInputDifferenceCokernelSupportState :
    AddCommGrpSnakeInputDifferenceCokernelSupportState where
  seed := "w344-20260520T202531Z-2833ddc187e17dd9"
  checkedConstructors :=
    ["DifferenceCokernelSnakeInputData",
      "snakeInput_of_differenceCokernelData",
      "ParallelPairDifferenceCokernelData",
      "snakeInput_of_parallelPairDifferenceCokernelData",
      "strictSnakeCokernelData_of_parallelPairDifferenceCokernelData",
      "addCommGrpKernelExact_of_parallelPairDifferenceCokernelData"]
  explicitInputs :=
    ["kernel row L₀ of the difference morphism",
      "cokernel row L₃ of the difference morphism u - v",
      "exactness of L₁ and L₂",
      "Epi L₁.g and Mono L₂.f",
      "an isomorphism from the constructed L₃ row to the target short complex"]
  remainingInputs :=
    ["construct these kernel/cokernel row certificates from the concrete WPP-op colimit cofork",
      "identify the WPP-op colimit short complex with the cokernel row of u - v",
      "derive or transport the required Epi/Mono strictness hypotheses at the concrete source rows"]
  productSuccessClaimed := false

theorem currentAddCommGrpSnakeInputDifferenceCokernelSupportState_productSuccess :
    currentAddCommGrpSnakeInputDifferenceCokernelSupportState.productSuccessClaimed = false := rfl

section Checks

#check DifferenceCokernelSnakeInputData
#check snakeInput_of_differenceCokernelData
#check snakeInput_of_differenceCokernelData_L₃
#check strictSnakeCokernelData_of_differenceCokernelData
#check ParallelPairDifferenceCokernelData
#check differenceCokernelData_of_parallelPair
#check snakeInput_of_parallelPairDifferenceCokernelData
#check parallelPair_snakeInput_v₁₂
#check strictSnakeCokernelData_of_parallelPairDifferenceCokernelData
#check addCommGrpKernelExact_of_parallelPairDifferenceCokernelData
#check currentAddCommGrpSnakeInputDifferenceCokernelSupportState
#check currentAddCommGrpSnakeInputDifferenceCokernelSupportState_productSuccess

end Checks

end AddCommGrpSnakeInputDifferenceCokernelV367SupportW344
end WppOpExactAcyclicFrontierConsolidatedW318

end LeanLCAExactChallenge
