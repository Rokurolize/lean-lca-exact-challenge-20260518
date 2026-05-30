import LeanLCAExactChallenge.Derived.ComparisonEmbeddingCriterionRoute
import LeanLCAExactChallenge.LCA.Pullback

/-!
W819: reduce W818 fiber saturation to the remaining cokernel-fiber closure
input.

W818 isolated the direct topological comparison criterion: algebraic
bijectivity plus a fiber-saturation statement imply the W816 embedding target.
This helper proves the kernel-range and boundary-closure half of that
saturation argument.  What remains is the concrete assertion that equality in
the right cokernel projection puts the difference in the closed boundary
subgroup.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

universe u

/--
An arbitrary limiting kernel fork in `MetrizableLCA` has the expected
element-level range: every point killed by the target morphism is in the range
of the kernel inclusion.
-/
theorem kernelFork_range_of_apply_eq_zeroW819
    {A B K : MetrizableLCA.{u}} {g : A ⟶ B} {ι : K ⟶ A}
    {w : ι ≫ g = 0}
    (hι : IsLimit (KernelFork.ofι ι w)) {x : A} (hx : g x = 0) :
    x ∈ Set.range (ι : K → A) := by
  let fork : Fork g 0 := KernelFork.ofι ι w
  let e : fork.pt ≅ MetrizableLCA.equalizerObj g 0 :=
    IsLimit.conePointUniqueUpToIso hι (MetrizableLCA.equalizerIsLimit g 0)
  let y : MetrizableLCA.equalizerObj g 0 :=
    ⟨x, by simpa [MetrizableLCA.zero_apply] using hx⟩
  refine ⟨e.inv y, ?_⟩
  have hcomp :
      e.hom ≫ MetrizableLCA.equalizerι g 0 = ι := by
    simpa [fork, MetrizableLCA.equalizerFork] using
      (IsLimit.conePointUniqueUpToIso_hom_comp
        hι (MetrizableLCA.equalizerIsLimit g 0) WalkingParallelPair.zero)
  have heval :
      (MetrizableLCA.equalizerι g 0) (e.hom (e.inv y)) =
        ι (e.inv y) := by
    exact congrArg
      (fun f : fork.pt ⟶ A => (f : fork.pt → A) (e.inv y)) hcomp
  have hy : e.hom (e.inv y) = y := by
    exact congrArg (fun f : MetrizableLCA.equalizerObj g 0 ⟶
      MetrizableLCA.equalizerObj g 0 => (f : _ → _) y) e.inv_hom_id
  calc
    ι (e.inv y) = (MetrizableLCA.equalizerι g 0) (e.hom (e.inv y)) := heval.symm
    _ = (MetrizableLCA.equalizerι g 0) y := by rw [hy]
    _ = x := rfl

/--
The closure of the boundary range of a short complex lies in the kernel of the
outgoing map.  This is the topological replacement for the algebraic
`range f ≤ ker g` step in the `TopModuleCat` proof.
-/
theorem boundary_closure_subset_kernelW819
    (S : ShortComplex MetrizableLCA.{u}) :
    closure (Set.range (S.f : S.X₁ → S.X₂)) ⊆
      {x : S.X₂ | S.g x = 0} := by
  have hsubset :
      Set.range (S.f : S.X₁ → S.X₂) ⊆
        {x : S.X₂ | S.g x = 0} := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.X₁ ⟶ S.X₃ => (f : S.X₁ → S.X₃) a) S.zero
  exact closure_minimal hsubset
    (isClosed_singleton.preimage S.g.hom.continuous)

/--
Remaining W819 cokernel-fiber input: if two points have the same image under
the chosen right cokernel projection, their difference lies in the closed
boundary range.
-/
def rightCokernelFiberClosureTargetW819
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) : Prop :=
  ∀ {x : S.X₂} {k : h₁.K},
    h₂.p x = h₂.p (h₁.i k) →
      x - h₁.i k ∈ closure (Set.range (S.f : S.X₁ → S.X₂))

/--
W819: the kernel-range and boundary-closure facts turn the remaining
cokernel-fiber closure input into W818's fiber-saturation condition.
-/
theorem leftRightComparisonFiberSaturation_of_rightCokernelFiberClosureW819
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    (hclosure : rightCokernelFiberClosureTargetW819 h₁ h₂) :
    leftRightComparisonFiberSaturationW818 h₁ h₂ := by
  intro x hx
  rcases hx with ⟨y, hy, hpy⟩
  rcases hy with ⟨k, rfl⟩
  have hdiff_mem :
      x - h₁.i k ∈ closure (Set.range (S.f : S.X₁ → S.X₂)) :=
    hclosure hpy.symm
  have hdiff_zero : S.g (x - h₁.i k) = 0 :=
    boundary_closure_subset_kernelW819 S hdiff_mem
  have hik_zero : S.g (h₁.i k) = 0 := by
    exact congrArg (fun f : h₁.K ⟶ S.X₃ => (f : h₁.K → S.X₃) k) h₁.wi
  have hx_zero : S.g x = 0 := by
    calc
      S.g x = S.g ((x - h₁.i k) + h₁.i k) := by rw [sub_add_cancel]
      _ = S.g (x - h₁.i k) + S.g (h₁.i k) := map_add S.g.hom _ _
      _ = 0 := by simp [hdiff_zero, hik_zero]
  exact kernelFork_range_of_apply_eq_zeroW819 h₁.hi hx_zero

/--
W819 target: algebraic bijectivity plus the remaining right-cokernel
fiber-closure input.
-/
def comparisonRightCokernelFiberClosureTargetW819
    (S : ShortComplex MetrizableLCA.{0}) : Prop :=
  Function.Bijective (S.leftRightHomologyComparison :
      S.leftHomology → S.rightHomology) ∧
    rightCokernelFiberClosureTargetW819
      S.leftHomologyData S.rightHomologyData

/-- W819 converts the right-cokernel closure target into the W818 target. -/
theorem comparisonFiberSaturationTarget_of_rightCokernelFiberClosureW819
    (S : ShortComplex MetrizableLCA.{0})
    (h : comparisonRightCokernelFiberClosureTargetW819 S) :
    comparisonFiberSaturationTargetW818 S :=
  ⟨h.1,
    leftRightComparisonFiberSaturation_of_rightCokernelFiberClosureW819
      S.leftHomologyData S.rightHomologyData h.2⟩

/--
W819: a universal algebraic-bijectivity plus right-cokernel fiber-closure
theorem supplies `CategoryWithHomology MetrizableLCA` through W818 and W816.
-/
theorem categoryWithHomology_of_rightCokernelFiberClosureW819
    (h :
      ∀ S : ShortComplex MetrizableLCA.{0},
        comparisonRightCokernelFiberClosureTargetW819 S) :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonFiberSaturationW818
    (fun S => comparisonFiberSaturationTarget_of_rightCokernelFiberClosureW819
      S (h S))

/-- Input names for the W819 comparison fiber-saturation route. -/
def comparisonFiberSaturationInputNamesW819 :
    List String :=
  ["algebraic bijectivity of the canonical left-right homology comparison",
    "right cokernel equality detects closed boundary-closure differences"]

theorem comparisonFiberSaturationInputNamesW819_count :
    comparisonFiberSaturationInputNamesW819.length = 2 :=
  rfl

/-- Current checked W819 state for the comparison fiber-saturation route. -/
structure ComparisonFiberSaturationRouteStateW819 :
    Type where
  seed : String
  declarations : List String
  topologyResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W819 state. -/
def currentComparisonFiberSaturationRouteSupportStateW819 :
    ComparisonFiberSaturationRouteStateW819
    where
  seed := "w819-comparison-fiber-saturation-route"
  declarations :=
    ["kernelFork_range_of_apply_eq_zeroW819",
      "boundary_closure_subset_kernelW819",
      "rightCokernelFiberClosureTargetW819",
      "leftRightComparisonFiberSaturation_of_rightCokernelFiberClosureW819",
      "comparisonRightCokernelFiberClosureTargetW819",
      "comparisonFiberSaturationTarget_of_rightCokernelFiberClosureW819",
      "categoryWithHomology_of_rightCokernelFiberClosureW819",
      "comparisonFiberSaturationInputNamesW819",
      "comparisonFiberSaturationInputNamesW819_count"]
  topologyResult :=
    "proved: boundary-closure points are cycles, and cycles are in the range " ++
      "of any limiting MetrizableLCA kernel inclusion"
  removedInputs :=
    ["full W818 fiber-saturation proof after right-cokernel fiber closure " ++
      "has been established"]
  remainingInputs :=
    comparisonFiberSaturationInputNamesW819
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentComparisonFiberSaturationRouteStateW819 :
    ComparisonFiberSaturationRouteStateW819 :=
  currentComparisonFiberSaturationRouteSupportStateW819

theorem currentComparisonFiberSaturationRouteStateW819_productSuccess :
    currentComparisonFiberSaturationRouteStateW819.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
