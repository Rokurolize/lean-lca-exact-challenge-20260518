import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
AddCommGrp SnakeInput support for difference-cokernel rows.

This module packages the algebraic route used by the W318 exact-acyclic boundary: a
parallel-pair coequalizer row can supply the SnakeInput cokernel row once it is
identified with the cokernel of the difference morphism `u - v`.  The checked
constructors below keep the remaining work focused on the concrete
kernel/cokernel row certificates and the colimit-row isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpSnakeInputDifferenceCokernel

open WppOpExactAcyclicFrontierConsolidatedW318

/-- AddCommGrp element-level kernel exactness is the concrete form of `ShortComplex.Exact`. -/
theorem shortComplexExact_of_addCommGrpKernelExact
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : AddCommGrpKernelExact T) :
    T.Exact := by
  rw [ShortComplex.ab_exact_iff]
  exact hT

/-- A right-surjective AddCommGrp short-complex map is categorically epi. -/
theorem epi_g_of_addCommGrpRightSurjective
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : AddCommGrpRightSurjective T) :
    Epi T.g := by
  rw [AddCommGrpCat.epi_iff_surjective]
  exact hT

/-- A left-injective AddCommGrp short-complex map is categorically mono. -/
theorem mono_f_of_addCommGrpLeftInjective
    (T : ShortComplex AddCommGrpCat.{0})
    (hT : AddCommGrpLeftInjective T) :
    Mono T.f :=
  (AddCommGrpCat.mono_iff_injective T.f).mpr hT

/--
Explicit input data for building a `SnakeInput` whose cokernel row is `L₃` for a
chosen difference-like morphism `d : L₁ ⟶ L₂`.
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
The explicit difference-cokernel data gives the W318 strict SnakeInput
certificate for any target row identified with the constructed cokernel row.
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

/-- Strict component fields are enough to provide the exact/epi/mono SnakeInput side data. -/
structure ParallelPairDifferenceStrictCokernelData
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
  L₁_kernelExact : AddCommGrpKernelExact L₁
  L₁_rightSurjective : AddCommGrpRightSurjective L₁
  L₂_kernelExact : AddCommGrpKernelExact L₂
  L₂_leftInjective : AddCommGrpLeftInjective L₂

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

/-- Turn strict component fields into the exact/epi/mono side data required by SnakeInput. -/
def parallelPairDifferenceCokernelData_of_strictData
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃) :
    ParallelPairDifferenceCokernelData L₁ L₂ L₃ where
  u := D.u
  v := D.v
  q := D.q
  w := D.w
  L₀ := D.L₀
  i := D.i
  wi := D.wi
  h₀ := D.h₀
  h₃ := D.h₃
  L₁_exact := shortComplexExact_of_addCommGrpKernelExact L₁ D.L₁_kernelExact
  epi_L₁_g := epi_g_of_addCommGrpRightSurjective L₁ D.L₁_rightSurjective
  L₂_exact := shortComplexExact_of_addCommGrpKernelExact L₂ D.L₂_kernelExact
  mono_L₂_f := mono_f_of_addCommGrpLeftInjective L₂ D.L₂_leftInjective

/-- Build a snake input whose middle map is the difference `u - v`. -/
def snakeInput_of_parallelPairDifferenceCokernelData
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) :
    ShortComplex.SnakeInput AddCommGrpCat.{0} :=
  snakeInput_of_differenceCokernelData (differenceCokernelData_of_parallelPair D)

/-- Build a snake input directly from strict component fields plus row certificates. -/
def snakeInput_of_parallelPairDifferenceStrictCokernelData
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃) :
    ShortComplex.SnakeInput AddCommGrpCat.{0} :=
  snakeInput_of_parallelPairDifferenceCokernelData
    (parallelPairDifferenceCokernelData_of_strictData D)

/-- The middle vertical map of the constructed snake input is definitionally `u - v`. -/
theorem parallelPair_strictSnakeInput_v₁₂
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃) :
    (snakeInput_of_parallelPairDifferenceStrictCokernelData D).v₁₂ = D.u - D.v := rfl

/--
Parallel-pair difference-cokernel data gives the W318 strict SnakeInput
certificate for any target row identified with the supplied cokernel row.
-/
def strictSnakeCokernelData_of_parallelPairDifferenceCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceCokernelData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_differenceCokernelData
    (differenceCokernelData_of_parallelPair D) e

/--
Strict component fields plus kernel/cokernel row certificates give the W318
strict SnakeInput certificate for any identified target row.
-/
def strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceCokernelData
    (parallelPairDifferenceCokernelData_of_strictData D) e

/-- Checked W318 consumer: strict difference-cokernel data supplies AddCommGrp kernel exactness. -/
theorem addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃) (e : L₃ ≅ T) :
    AddCommGrpKernelExact T :=
  addCommGrpKernelExact_of_strictSnakeCokernelData T
    (strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData D e)

/-- Machine-readable state for this source-support module. -/
structure AddCommGrpSnakeInputDifferenceCokernelState : Type where
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSnakeInputDifferenceCokernelState :
    AddCommGrpSnakeInputDifferenceCokernelState where
  checkedConstructors :=
    ["DifferenceCokernelSnakeInputData",
      "ParallelPairDifferenceCokernelData",
      "ParallelPairDifferenceStrictCokernelData",
      "parallelPairDifferenceCokernelData_of_strictData",
      "strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData",
      "addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData"]
  remainingInputs :=
    ["construct the difference kernel row from the concrete WPP-op source pair",
      "construct the difference cokernel row from the concrete WPP-op target cofork",
      "identify the WPP-op colimit short complex with that cokernel row"]
  productSuccessClaimed := false

theorem currentAddCommGrpSnakeInputDifferenceCokernelState_productSuccess :
    currentAddCommGrpSnakeInputDifferenceCokernelState.productSuccessClaimed = false := rfl

end AddCommGrpSnakeInputDifferenceCokernel

end LeanLCAExactChallenge
