import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W246 audit: concrete homology-zero bridges for strict `MetrizableLCA` targets.

W243 showed that `ShortComplex.QuasiIso.exact_iff` transports categorical
`ShortComplex.Exact`.  This file sharpens the target-side bridge question for
v257: categorical exactness may support a kernel/range bridge, but it cannot
imply surjectivity of `T.g`.  The counterexample is the exact short complex
`0 -> 0 -> ZMod 2`, whose middle homology is zero while the final map is not
surjective.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace ShortComplexExactnessHomologyZeroW246

/-- Concrete kernel equality required by `MetrizableLCA.strictShortExact`. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Concrete right-map surjectivity required by `MetrizableLCA.strictShortExact`. -/
abbrev TargetSurjectivity (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  Function.Surjective (T.g : T.X₂ → T.X₃)

/-- Topological fields required by `MetrizableLCA.strictShortExact`. -/
structure TargetStrictTopology (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)

/--
Named element-level API that would turn categorical exactness into the concrete
algebraic fields consumed by the local strict predicate.
-/
structure ExactElementAPI (T : ShortComplex MetrizableLCA.{u}) : Prop where
  kernel_equality_of_exact : T.Exact → TargetKernelEquality T
  surjective_g_of_exact : T.Exact → TargetSurjectivity T

/--
`strictShortExact` can consume an existing `ShortComplex.Exact` once the exact
element-level API and the two target topological fields are supplied.
-/
theorem strictShortExact_of_shortComplexExact_of_elementAPI_of_topology
    {T : ShortComplex MetrizableLCA.{u}} (hT : T.Exact)
    (hapi : ExactElementAPI T) (htop : TargetStrictTopology T) :
    MetrizableLCA.strictShortExact T where
  closed_inclusion := htop.closed_embedding_f
  open_map := htop.open_map_g
  surjective := hapi.surjective_g_of_exact hT
  algebraic_exact := by
    intro x₂ hx₂
    exact ((hapi.kernel_equality_of_exact hT) x₂).mp hx₂

/--
W243's transported categorical exactness is enough for strict exactness only
after the same target-side element API and topology are provided.
-/
theorem strictShortExact_of_quasiIso_of_exactElementAPI_of_topology
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology] (hS : S.Exact)
    (hφ : ShortComplex.QuasiIso φ) (hapi : ExactElementAPI T)
    (htop : TargetStrictTopology T) :
    MetrizableLCA.strictShortExact T := by
  haveI : ShortComplex.QuasiIso φ := hφ
  exact strictShortExact_of_shortComplexExact_of_elementAPI_of_topology
    ((ShortComplex.QuasiIso.exact_iff φ).1 hS) hapi htop

/--
The tempting unconditional bridge isolated by W243.  The theorem below shows
that this is too strong for the current v257 target.
-/
abbrev ShortComplexExactToTargetSurjectivity : Prop :=
  ∀ {T : ShortComplex MetrizableLCA.{0}} [T.HasHomology],
    T.Exact → TargetSurjectivity T

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

/-- The discrete two-element LCA object used by the obstruction. -/
abbrev Z2LCA : MetrizableLCA.{0} :=
  MetrizableLCA.of (ZMod 2)

/-- Exact target with zero middle object and nonzero right object. -/
abbrev exactButNotSurjectiveTarget : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := Z2LCA
  f := 0
  g := 0
  zero := by simp

/-- The target has zero middle homology: this is categorical `ShortComplex.Exact`. -/
theorem exactButNotSurjectiveTarget_exact :
    exactButNotSurjectiveTarget.Exact :=
  ShortComplex.exact_of_isZero_X₂ exactButNotSurjectiveTarget
    MetrizableLCA.zeroObj_isZero

/-- The right map of the exact target is not surjective. -/
theorem exactButNotSurjectiveTarget_g_not_surjective :
    ¬ TargetSurjectivity exactButNotSurjectiveTarget := by
  intro h
  rcases h (1 : ZMod 2) with ⟨x, hx⟩
  cases x
  norm_num at hx

/--
There is no current theorem of the form
`ShortComplex.Exact T -> Function.Surjective T.g`.
-/
theorem no_shortComplexExact_to_targetSurjectivity :
    ¬ ShortComplexExactToTargetSurjectivity := by
  intro h
  haveI : exactButNotSurjectiveTarget.HasHomology :=
    exactButNotSurjectiveTarget_exact.hasHomology
  exact exactButNotSurjectiveTarget_g_not_surjective
    (h exactButNotSurjectiveTarget_exact)

/--
Concrete obstruction summary for downstream workers.
-/
def exactnessHomologyZeroBridgeStatus : List String :=
  ["proved: ShortComplex.Exact plus an explicit element API and target topology constructs strictShortExact",
    "proved: transported exactness via ShortComplex.QuasiIso.exact_iff feeds that conditional constructor",
    "proved: ShortComplex.Exact does not imply surjectivity of T.g",
    "counterexample: the exact complex 0 -> 0 -> ZMod 2 has non-surjective final zero map",
    "missing: replace the false exactness-to-surjectivity bridge by a right-exactness, Epi T.g, cokernel-zero, or explicit Function.Surjective assumption"]

theorem exactnessHomologyZeroBridgeStatus_count :
    exactnessHomologyZeroBridgeStatus.length = 5 := rfl

section Checks

#check TargetKernelEquality
#check TargetSurjectivity
#check TargetStrictTopology
#check ExactElementAPI
#check strictShortExact_of_shortComplexExact_of_elementAPI_of_topology
#check strictShortExact_of_quasiIso_of_exactElementAPI_of_topology
#check ShortComplexExactToTargetSurjectivity
#check Z2LCA
#check exactButNotSurjectiveTarget
#check exactButNotSurjectiveTarget_exact
#check exactButNotSurjectiveTarget_g_not_surjective
#check no_shortComplexExact_to_targetSurjectivity
#check exactnessHomologyZeroBridgeStatus
#check exactnessHomologyZeroBridgeStatus_count
#check ShortComplex.QuasiIso.exact_iff
#check ShortComplex.exact_of_isZero_X₂
#check MetrizableLCA.strictShortExact

end Checks

end ShortComplexExactnessHomologyZeroW246

end LeanLCAExactChallenge
