import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.RightHomology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W262 audit: right-homology and right-end cokernel/epi inputs.

`ShortComplex.RightHomology` describes the middle homology using the cokernel
of `f` followed by the induced map to `X₃`.  Vanishing of that object is still a
middle-exactness statement, not a right-end surjectivity or cokernel-vanishing
statement for `g`.  The compiling positive bridge in current APIs is therefore
through `ShortComplex.ShortExact`, whose separate `[Epi T.g]` field is exactly
one of the right-end inputs needed by the local strictness constructors.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace ShortComplexRightHomologyCokernelBridgeW262

/-- Element-level kernel/range equality consumed by `strictShortExact`. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Target-side topology fields consumed by `strictShortExact`. -/
structure TargetStrictTopology (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)

/-- Categorical exactness gives the concrete kernel bridge after forgetting topology. -/
theorem targetKernelEquality_of_shortComplexExact
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) :
    TargetKernelEquality T := by
  letI := hhom
  letI := hpres
  intro x₂
  constructor
  · intro hx₂
    exact (ShortComplex.exact_iff_of_hasForget T).mp hT x₂ hx₂
  · rintro ⟨x₁, rfl⟩
    change (T.f ≫ T.g : T.X₁ ⟶ T.X₃) x₁ = (0 : T.X₁ ⟶ T.X₃) x₁
    exact congrArg (fun h : T.X₁ ⟶ T.X₃ => h x₁) T.zero

/-- `ShortExact` packages the separate right-end epi datum that plain exactness lacks. -/
theorem targetEpi_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) : Epi T.g := by
  exact hT.epi_g

theorem cokernelπ_eq_zero_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) :
    MetrizableLCA.cokernelπ T.g = 0 := by
  haveI : Epi T.g := targetEpi_of_shortExact hT
  exact MetrizableLCA.cokernelπ_eq_zero_of_epi T.g

theorem cokernelSubgroup_eq_top_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) :
    MetrizableLCA.cokernelSubgroup T.g = ⊤ :=
  MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero T.g
    (cokernelπ_eq_zero_of_shortExact hT)

theorem cokernelObj_isZero_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) :
    IsZero (MetrizableLCA.cokernelObj T.g) :=
  MetrizableLCA.cokernelObj_isZero_of_cokernelSubgroup_eq_top T.g
    (cokernelSubgroup_eq_top_of_shortExact hT)

/--
`ShortExact` plus the same topology and forgetful-homology inputs as W258 gives
the local strict short exact predicate.
-/
theorem strictShortExact_of_shortExact_of_topology
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.ShortExact) (htop : TargetStrictTopology T) :
    MetrizableLCA.strictShortExact T := by
  haveI : Epi T.g := targetEpi_of_shortExact hT
  exact MetrizableLCA.strictShortExact_of_kernel_open_closed_epi
    (targetKernelEquality_of_shortComplexExact hhom hpres hT.exact)
    htop.closed_embedding_f htop.open_map_g

/-- Exactness, equivalently middle homology zero, also makes right homology zero. -/
theorem rightHomology_isZero_of_exact
    {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology] (hT : T.Exact) :
    IsZero T.rightHomology :=
  IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology T).mp hT) T.rightHomologyIso

theorem rightHomology_isZero_of_shortExact
    {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology] (hT : T.ShortExact) :
    IsZero T.rightHomology :=
  rightHomology_isZero_of_exact hT.exact

/--
The smallest comparison datum that would turn right-homology zero into a local
right-end cokernel input.  Current APIs do not provide this comparison, and the
counterexample below explains why it cannot be inferred from right-homology
zero alone.
-/
structure RightHomologyCokernelObjComparison
    (T : ShortComplex MetrizableLCA.{u}) [T.HasRightHomology] : Type (u + 1) where
  cokernelObjIsoRightHomology :
    MetrizableLCA.cokernelObj T.g ≅ T.rightHomology

theorem cokernelObj_isZero_of_rightHomology_isZero_of_comparison
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology]
    (hzero : IsZero T.rightHomology)
    (hcmp : RightHomologyCokernelObjComparison T) :
    IsZero (MetrizableLCA.cokernelObj T.g) :=
  IsZero.of_iso hzero hcmp.cokernelObjIsoRightHomology

theorem cokernelSubgroup_eq_top_of_rightHomology_isZero_of_comparison
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology]
    (hzero : IsZero T.rightHomology)
    (hcmp : RightHomologyCokernelObjComparison T) :
    MetrizableLCA.cokernelSubgroup T.g = ⊤ :=
  MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelObj_isZero T.g
    (cokernelObj_isZero_of_rightHomology_isZero_of_comparison hzero hcmp)

theorem strictShortExact_of_exact_of_topology_of_rightHomology_cokernel_comparison
    {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology]
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T)
    (hcmp : RightHomologyCokernelObjComparison T) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
    (targetKernelEquality_of_shortComplexExact inferInstance hpres hT)
    htop.closed_embedding_f htop.open_map_g
    (cokernelSubgroup_eq_top_of_rightHomology_isZero_of_comparison
      (rightHomology_isZero_of_exact hT) hcmp)

/-- A hypothetical invalid bridge from right-homology zero to the right endpoint epi. -/
abbrev RightHomologyZeroToTargetEpi : Prop :=
  ∀ {T : ShortComplex MetrizableLCA.{0}} [T.HasHomology],
    IsZero T.rightHomology → Epi T.g

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

theorem exactButNotEpiTarget_exact :
    exactButNotEpiTarget.Exact :=
  ShortComplex.exact_of_isZero_X₂ exactButNotEpiTarget
    MetrizableLCA.zeroObj_isZero

theorem exactButNotEpiTarget_g_not_surjective :
    ¬ Function.Surjective (exactButNotEpiTarget.g :
      exactButNotEpiTarget.X₂ → exactButNotEpiTarget.X₃) := by
  intro h
  rcases h (1 : ZMod 2) with ⟨x, hx⟩
  cases x
  norm_num at hx

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

/--
Right-homology zero alone is still too weak: it is a middle-exactness datum,
so the W256 endpoint obstruction also blocks this route to `[Epi T.g]`.
-/
theorem no_rightHomologyZero_to_targetEpi :
    ¬ RightHomologyZeroToTargetEpi := by
  intro h
  haveI : exactButNotEpiTarget.HasHomology :=
    exactButNotEpiTarget_exact.hasHomology
  exact exactButNotEpiTarget_g_not_epi
    (h (rightHomology_isZero_of_exact exactButNotEpiTarget_exact))

def availableRightEndpointBridge : List String :=
  ["ShortComplex.ShortExact supplies the separate Epi T.g field",
    "ShortExact -> MetrizableLCA.cokernelπ T.g = 0",
    "ShortExact -> MetrizableLCA.cokernelSubgroup T.g = top",
    "ShortExact -> IsZero (MetrizableLCA.cokernelObj T.g)",
    "ShortExact plus topology plus the W258 kernel bridge constructs strictShortExact"]

theorem availableRightEndpointBridge_count :
    availableRightEndpointBridge.length = 5 := rfl

def missingRightHomologyEndpointBridge : List String :=
  ["right-homology zero alone is middle exactness, not right-end exactness",
    "missing: canonical comparison MetrizableLCA.cokernelObj T.g ≅ T.rightHomology",
    "missing: IsZero T.rightHomology -> IsZero (MetrizableLCA.cokernelObj T.g)",
    "missing: IsZero T.rightHomology -> MetrizableLCA.cokernelπ T.g = 0",
    "false: IsZero T.rightHomology -> Epi T.g"]

theorem missingRightHomologyEndpointBridge_count :
    missingRightHomologyEndpointBridge.length = 5 := rfl

section Checks

#check TargetKernelEquality
#check TargetStrictTopology
#check targetKernelEquality_of_shortComplexExact
#check targetEpi_of_shortExact
#check cokernelπ_eq_zero_of_shortExact
#check cokernelSubgroup_eq_top_of_shortExact
#check cokernelObj_isZero_of_shortExact
#check strictShortExact_of_shortExact_of_topology
#check rightHomology_isZero_of_exact
#check rightHomology_isZero_of_shortExact
#check RightHomologyCokernelObjComparison
#check cokernelObj_isZero_of_rightHomology_isZero_of_comparison
#check cokernelSubgroup_eq_top_of_rightHomology_isZero_of_comparison
#check strictShortExact_of_exact_of_topology_of_rightHomology_cokernel_comparison
#check RightHomologyZeroToTargetEpi
#check exactButNotEpiTarget
#check exactButNotEpiTarget_exact
#check exactButNotEpiTarget_g_not_surjective
#check exactButNotEpiTarget_g_not_epi
#check no_rightHomologyZero_to_targetEpi
#check availableRightEndpointBridge_count
#check missingRightHomologyEndpointBridge_count
#check ShortComplex.HasRightHomology
#check ShortComplex.rightHomology
#check ShortComplex.rightHomologyι
#check ShortComplex.pOpcycles
#check ShortComplex.fromOpcycles
#check ShortComplex.ShortExact
#check ShortComplex.ShortExact.mk'
#check ShortComplex.exact_iff_isZero_homology
#check MetrizableLCA.cokernelπ_eq_zero_of_epi
#check MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero
#check MetrizableLCA.cokernelObj_isZero_of_cokernelSubgroup_eq_top
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_epi

end Checks

end ShortComplexRightHomologyCokernelBridgeW262

end LeanLCAExactChallenge
