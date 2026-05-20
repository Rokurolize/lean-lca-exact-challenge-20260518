import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W256: exactness, kernel equality, and categorical epi input for strict `MetrizableLCA`
short complexes.

The v268 target has `MetrizableLCA.strictShortExact_of_kernel_open_closed_epi`. This file records
the strongest compiling bridge found from `ShortComplex.Exact`: categorical exactness gives the
element-level kernel equality through `ShortComplex.exact_iff_of_hasForget` when the short complex
has homology and the local forgetful functor preserves homology. The right endpoint still needs an
explicit `[Epi T.g]`, cokernel-zero, or equivalent right-exactness input.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace ShortComplexExactEpiKernelBridgeW256

/-- Element-level kernel equality consumed by the local strict exactness theorem. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- The remaining topological fields of `MetrizableLCA.strictShortExact`. -/
structure TargetStrictTopology (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)

/--
Concrete-category exactness bridge. This is the closest available imported ShortComplex API:
it removes the need for an explicit kernel-equality field once homology preservation by the
forgetful functor is provided.
-/
theorem targetKernelEquality_of_exact_of_hasForget
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) : TargetKernelEquality T := by
  letI := hhom
  letI := hpres
  intro x₂
  constructor
  · intro hx₂
    exact (ShortComplex.exact_iff_of_hasForget T).mp hT x₂ hx₂
  · rintro ⟨x₁, rfl⟩
    change (T.f ≫ T.g : T.X₁ ⟶ T.X₃) x₁ = (0 : T.X₁ ⟶ T.X₃) x₁
    exact congrArg (fun h : T.X₁ ⟶ T.X₃ => h x₁) T.zero

theorem strictShortExact_of_shortComplexExact_of_kernelBridge_epi_topology
    {T : ShortComplex MetrizableLCA.{u}} [Epi T.g]
    (hT : T.Exact) (hker : T.Exact → TargetKernelEquality T)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃)) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_epi (hker hT) hclosed hopen

theorem strictShortExact_of_shortComplexExact_of_hasForget_epi_topology
    {T : ShortComplex MetrizableLCA.{u}} [Epi T.g]
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃)) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_epi
    (targetKernelEquality_of_exact_of_hasForget hhom hpres hT) hclosed hopen

theorem strictShortExact_of_shortComplexExact_of_hasForget_cokernelπ_eq_zero_topology
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃))
    (hπ : MetrizableLCA.cokernelπ T.g = 0) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero
    (targetKernelEquality_of_exact_of_hasForget hhom hpres hT) hclosed hopen hπ

theorem strictShortExact_of_quasiIso_of_hasForget_epi_topology
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology] [Epi T.g]
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃)) :
    MetrizableLCA.strictShortExact T := by
  haveI : ShortComplex.QuasiIso φ := hφ
  exact strictShortExact_of_shortComplexExact_of_hasForget_epi_topology
    (T := T) (inferInstance : T.HasHomology) hpres
    ((ShortComplex.QuasiIso.exact_iff φ).1 hS) hclosed hopen

/-- Categorical exactness alone cannot provide the right-end `Epi T.g`. -/
abbrev ShortComplexExactToTargetEpi : Prop :=
  ∀ {T : ShortComplex MetrizableLCA.{0}} [T.HasHomology], T.Exact → Epi T.g

/-- Quasi-isomorphism plus source exactness also cannot provide target `Epi T.g`. -/
abbrev QuasiIsoExactToTargetEpi : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{0}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    S.Exact → ShortComplex.QuasiIso φ → Epi T.g

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

/-- The discrete two-element LCA object used by the endpoint obstruction. -/
abbrev Z2LCA : MetrizableLCA.{0} :=
  MetrizableLCA.of (ZMod 2)

/-- Exact complex with zero middle object and nonzero right object. -/
abbrev exactButNotEpiTarget : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := Z2LCA
  f := 0
  g := 0
  zero := by simp

/-- The target is exact because the middle object is zero. -/
theorem exactButNotEpiTarget_exact :
    exactButNotEpiTarget.Exact :=
  ShortComplex.exact_of_isZero_X₂ exactButNotEpiTarget
    MetrizableLCA.zeroObj_isZero

/-- The right map is not surjective. -/
theorem exactButNotEpiTarget_g_not_surjective :
    ¬ Function.Surjective (exactButNotEpiTarget.g :
      exactButNotEpiTarget.X₂ → exactButNotEpiTarget.X₃) := by
  intro h
  rcases h (1 : ZMod 2) with ⟨x, hx⟩
  cases x
  norm_num at hx

/-- Therefore the right map is not epi in this concrete category. -/
theorem exactButNotEpiTarget_g_not_epi :
    ¬ Epi exactButNotEpiTarget.g := by
  intro hEpi
  letI := hEpi
  have hcomp :
      exactButNotEpiTarget.g ≫ (0 : Z2LCA ⟶ Z2LCA) =
        exactButNotEpiTarget.g ≫ (𝟙 Z2LCA) := by
    ext x
    cases x
    rfl
  have hid : (0 : Z2LCA ⟶ Z2LCA) = 𝟙 Z2LCA :=
    (cancel_epi exactButNotEpiTarget.g).mp hcomp
  have hfun := congrArg (fun f : Z2LCA ⟶ Z2LCA => f (1 : ZMod 2)) hid
  change (0 : ZMod 2) = 1 at hfun
  norm_num at hfun

/-- No theorem can turn categorical exactness alone into `Epi T.g`. -/
theorem no_shortComplexExact_to_targetEpi :
    ¬ ShortComplexExactToTargetEpi := by
  intro h
  haveI : exactButNotEpiTarget.HasHomology :=
    exactButNotEpiTarget_exact.hasHomology
  exact exactButNotEpiTarget_g_not_epi (h exactButNotEpiTarget_exact)

/-- Transported exactness via a quasi-isomorphism still does not supply `Epi T.g`. -/
theorem no_quasiIsoExact_to_targetEpi :
    ¬ QuasiIsoExactToTargetEpi := by
  intro h
  haveI : exactButNotEpiTarget.HasHomology :=
    exactButNotEpiTarget_exact.hasHomology
  have hqi : ShortComplex.QuasiIso (𝟙 exactButNotEpiTarget) := inferInstance
  exact exactButNotEpiTarget_g_not_epi
    (h (𝟙 exactButNotEpiTarget) exactButNotEpiTarget_exact hqi)

def endpointEpiBridgeStatus : List String :=
  ["available: MetrizableLCA.cokernelπ_eq_zero_of_epi turns an explicit Epi into cokernelπ = 0",
    "available: MetrizableLCA.strictShortExact_of_kernel_open_closed_epi consumes [Epi T.g]",
    "available: MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero consumes cokernelπ T.g = 0",
    "false: ShortComplex.Exact alone implies Epi T.g",
    "false: transported exactness via ShortComplex.QuasiIso alone implies Epi T.g",
    "missing: a valid right-exactness or cokernel-zero theorem producing [Epi T.g] for the local target"]

theorem endpointEpiBridgeStatus_count :
    endpointEpiBridgeStatus.length = 6 := rfl

def strictExactInputState : List String :=
  ["kernel equality: obtained from ShortComplex.Exact using ShortComplex.exact_iff_of_hasForget with T.HasHomology and forgetful PreservesHomology",
    "right endpoint: still needs [Epi T.g], cokernelπ T.g = 0, or another valid right-exactness input",
    "closed embedding: still an explicit IsClosedEmbedding (T.f : T.X1 -> T.X2) input",
    "open map: still an explicit IsOpenMap (T.g : T.X2 -> T.X3) input",
    "quasi-isomorphism: only transports ShortComplex.Exact through ShortComplex.QuasiIso.exact_iff"]

theorem strictExactInputState_count :
    strictExactInputState.length = 5 := rfl

section Checks

#check TargetKernelEquality
#check TargetStrictTopology
#check targetKernelEquality_of_exact_of_hasForget
#check strictShortExact_of_shortComplexExact_of_kernelBridge_epi_topology
#check strictShortExact_of_shortComplexExact_of_hasForget_epi_topology
#check strictShortExact_of_shortComplexExact_of_hasForget_cokernelπ_eq_zero_topology
#check strictShortExact_of_quasiIso_of_hasForget_epi_topology
#check ShortComplexExactToTargetEpi
#check QuasiIsoExactToTargetEpi
#check exactButNotEpiTarget
#check exactButNotEpiTarget_exact
#check exactButNotEpiTarget_g_not_surjective
#check exactButNotEpiTarget_g_not_epi
#check no_shortComplexExact_to_targetEpi
#check no_quasiIsoExact_to_targetEpi
#check endpointEpiBridgeStatus
#check endpointEpiBridgeStatus_count
#check strictExactInputState
#check strictExactInputState_count
#check ShortComplex.exact_iff_of_hasForget
#check ShortComplex.exact_iff_exact_map_forget₂
#check ShortComplex.ab_exact_iff
#check ShortComplex.ShortExact.mk'
#check ShortComplex.ShortExact.surjective_g
#check Preadditive.epi_iff_surjective'
#check MetrizableLCA.cokernelπ_eq_zero_of_epi
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_epi
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero

end Checks

end ShortComplexExactEpiKernelBridgeW256

end LeanLCAExactChallenge
