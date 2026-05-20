import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.RightHomology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W268 audit: precise right-homology/end-cokernel comparison.

The useful comparison is not an isomorphism
`T.rightHomology ≅ MetrizableLCA.cokernelObj T.g`.  In mathlib,
`T.rightHomology` is the kernel of `T.fromOpcycles : T.opcycles ⟶ T.X₃`.
Since `T.pOpcycles : T.X₂ ⟶ T.opcycles` is epi and
`T.pOpcycles ≫ T.fromOpcycles = T.g`, the local endpoint cokernel projection
`MetrizableLCA.cokernelπ T.g` is also a categorical cokernel of
`T.fromOpcycles`.  Thus right homology and endpoint cokernel are kernel and
cokernel of the same induced map, not two objects that vanish together.

The shortest checked boundary is therefore an explicit right-end input such as
`Epi T.fromOpcycles`, `Epi T.g`, `MetrizableLCA.cokernelπ T.g = 0`, or
`IsZero (MetrizableLCA.cokernelObj T.g)`.  The counterexample at the end keeps
the W262 obstruction: `IsZero T.rightHomology` alone cannot imply `Epi T.g`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace RightHomologyCokernelComparisonW268

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

/-- The right-homology inclusion is the kernel of the induced opcycles map. -/
def rightHomologyι_isKernel_fromOpcycles
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology] :
    IsLimit (KernelFork.ofι T.rightHomologyι T.rightHomologyData.ι_g') :=
  T.rightHomologyData.hι'

/--
The endpoint cokernel projection kills `T.fromOpcycles`, because it kills
`T.g = T.pOpcycles ≫ T.fromOpcycles` and `T.pOpcycles` is epi.
-/
theorem fromOpcycles_comp_cokernelπ_eq_zero
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology] :
    T.fromOpcycles ≫ MetrizableLCA.cokernelπ T.g = 0 := by
  rw [← cancel_epi T.pOpcycles]
  rw [← Category.assoc, T.p_fromOpcycles, MetrizableLCA.comp_cokernelπ, comp_zero]

theorem g_comp_eq_zero_of_fromOpcycles_comp_eq_zero
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology]
    {A : MetrizableLCA.{u}} {k : T.X₃ ⟶ A}
    (hk : T.fromOpcycles ≫ k = 0) :
    T.g ≫ k = 0 := by
  rw [← T.p_fromOpcycles, Category.assoc, hk, comp_zero]

/--
The local endpoint cokernel of `T.g` is also a categorical cokernel of the
induced opcycles map `T.fromOpcycles`.
-/
def cokernelπ_isColimit_fromOpcycles
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology] :
    IsColimit (CokernelCofork.ofπ (MetrizableLCA.cokernelπ T.g)
      fromOpcycles_comp_cokernelπ_eq_zero) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {A} k hk => ?_)
    (fun {A} k hk => ?_) (fun {A} k hk m hm => ?_)
  · exact (CokernelCofork.IsColimit.desc'
      (MetrizableLCA.cokernelIsColimit T.g) k
      (g_comp_eq_zero_of_fromOpcycles_comp_eq_zero hk)).1
  · exact (CokernelCofork.IsColimit.desc'
      (MetrizableLCA.cokernelIsColimit T.g) k
      (g_comp_eq_zero_of_fromOpcycles_comp_eq_zero hk)).2
  · apply Cofork.IsColimit.hom_ext (MetrizableLCA.cokernelIsColimit T.g)
    have hfac := (CokernelCofork.IsColimit.desc'
        (MetrizableLCA.cokernelIsColimit T.g) k
        (g_comp_eq_zero_of_fromOpcycles_comp_eq_zero hk)).2
    change MetrizableLCA.cokernelπ T.g ≫ m =
      MetrizableLCA.cokernelπ T.g ≫ (CokernelCofork.IsColimit.desc'
        (MetrizableLCA.cokernelIsColimit T.g) k
        (g_comp_eq_zero_of_fromOpcycles_comp_eq_zero hk)).1
    change MetrizableLCA.cokernelπ T.g ≫ (CokernelCofork.IsColimit.desc'
        (MetrizableLCA.cokernelIsColimit T.g) k
        (g_comp_eq_zero_of_fromOpcycles_comp_eq_zero hk)).1 = k at hfac
    exact hm.trans hfac.symm

/--
Precise comparison datum: `rightHomology` is the kernel and the local endpoint
cokernel is the cokernel of the same induced map `T.fromOpcycles`.
-/
structure RightHomologyEndpointCokernelComparison
    (T : ShortComplex MetrizableLCA.{u}) [T.HasRightHomology] : Type (u + 1) where
  rightHomology_kernel :
    IsLimit (KernelFork.ofι T.rightHomologyι T.rightHomologyData.ι_g')
  endpoint_cokernel :
    IsColimit (CokernelCofork.ofπ (MetrizableLCA.cokernelπ T.g)
      fromOpcycles_comp_cokernelπ_eq_zero)

def rightHomologyEndpointCokernelComparison
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology] :
    RightHomologyEndpointCokernelComparison T where
  rightHomology_kernel := rightHomologyι_isKernel_fromOpcycles
  endpoint_cokernel := cokernelπ_isColimit_fromOpcycles

/-- An explicit epi for the induced opcycles map is enough to zero the endpoint cokernel. -/
theorem cokernelπ_eq_zero_of_epi_fromOpcycles
    {T : ShortComplex MetrizableLCA.{u}} [T.HasRightHomology]
    [Epi T.fromOpcycles] :
    MetrizableLCA.cokernelπ T.g = 0 := by
  rw [← cancel_epi T.fromOpcycles]
  rw [fromOpcycles_comp_cokernelπ_eq_zero, comp_zero]

theorem strictShortExact_of_exact_of_topology_of_epi_fromOpcycles
    {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology]
    [Epi T.fromOpcycles]
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero
    (targetKernelEquality_of_shortComplexExact inferInstance hpres hT)
    htop.closed_embedding_f htop.open_map_g
    (cokernelπ_eq_zero_of_epi_fromOpcycles (T := T))

/-- `ShortExact` still supplies the endpoint epi field directly. -/
theorem targetEpi_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) : Epi T.g :=
  hT.epi_g

theorem cokernelObj_isZero_of_shortExact {T : ShortComplex MetrizableLCA.{u}}
    (hT : T.ShortExact) :
    IsZero (MetrizableLCA.cokernelObj T.g) := by
  haveI : Epi T.g := targetEpi_of_shortExact hT
  exact MetrizableLCA.cokernelObj_isZero_of_cokernelSubgroup_eq_top T.g
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero T.g
      (MetrizableLCA.cokernelπ_eq_zero_of_epi T.g))

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

/-- Exactness, equivalently middle homology zero, makes right homology zero. -/
theorem rightHomology_isZero_of_exact
    {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology] (hT : T.Exact) :
    IsZero T.rightHomology :=
  IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology T).mp hT) T.rightHomologyIso

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
Right-homology zero alone is too weak: it is the zero-kernel side of
`T.fromOpcycles`, and it does not force the endpoint cokernel side to vanish.
-/
theorem no_rightHomologyZero_to_targetEpi :
    ¬ RightHomologyZeroToTargetEpi := by
  intro h
  haveI : exactButNotEpiTarget.HasHomology :=
    exactButNotEpiTarget_exact.hasHomology
  exact exactButNotEpiTarget_g_not_epi
    (h (rightHomology_isZero_of_exact exactButNotEpiTarget_exact))

def checkedComparisonBoundary : List String :=
  ["T.rightHomology is Kernel T.fromOpcycles via ShortComplex.rightHomologyData.hι'",
    "MetrizableLCA.cokernelπ T.g is Cokernel T.fromOpcycles because T.pOpcycles is epi",
    "there is no checked API making right-homology zero imply endpoint cokernel zero",
    "shortest positive endpoint inputs checked here: Epi T.fromOpcycles, Epi T.g, cokernelπ T.g = 0, or IsZero (cokernelObj T.g)",
    "counterexample preserved: IsZero T.rightHomology does not imply Epi T.g"]

theorem checkedComparisonBoundary_count :
    checkedComparisonBoundary.length = 5 := rfl

section Checks

#check targetKernelEquality_of_shortComplexExact
#check rightHomologyι_isKernel_fromOpcycles
#check fromOpcycles_comp_cokernelπ_eq_zero
#check cokernelπ_isColimit_fromOpcycles
#check RightHomologyEndpointCokernelComparison
#check rightHomologyEndpointCokernelComparison
#check cokernelπ_eq_zero_of_epi_fromOpcycles
#check strictShortExact_of_exact_of_topology_of_epi_fromOpcycles
#check targetEpi_of_shortExact
#check cokernelObj_isZero_of_shortExact
#check strictShortExact_of_shortExact_of_topology
#check rightHomology_isZero_of_exact
#check RightHomologyZeroToTargetEpi
#check exactButNotEpiTarget_g_not_epi
#check no_rightHomologyZero_to_targetEpi
#check checkedComparisonBoundary_count
#check ShortComplex.rightHomology
#check ShortComplex.rightHomologyι
#check ShortComplex.pOpcycles
#check ShortComplex.fromOpcycles
#check ShortComplex.p_fromOpcycles
#check MetrizableLCA.cokernelIsColimit
#check MetrizableLCA.cokernelπ_eq_zero_of_epi

end Checks

end RightHomologyCokernelComparisonW268

end LeanLCAExactChallenge
