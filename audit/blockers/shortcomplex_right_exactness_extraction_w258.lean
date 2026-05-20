import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.RightHomology

/-!
W258 audit: extracting the right-exactness input for strict short exactness.

The v270 cokernel API gives several equivalent right-end inputs once the target
map is known to be open.  This file isolates the strongest compiling consumer:
`ShortComplex.Exact` supplies the element-level kernel bridge through the
forgetful homology API, while the right end still needs an explicit
`Epi T.g`, `cokernelπ T.g = 0`, `cokernelSubgroup T.g = ⊤`, or
`IsZero (cokernelObj T.g)` assumption.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace ShortComplexRightExactnessExtractionW258

/-- Element-level kernel/range equality consumed by `strictShortExact`. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Target-side topology fields consumed by `strictShortExact`. -/
structure TargetStrictTopology (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)

/--
Categorical short-complex exactness gives the concrete kernel bridge after the
same homology and forgetful-homology preservation inputs used by the local API.
-/
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

/--
Package the exactness-derived kernel bridge, topology fields, and cokernel-top
right input into the promoted v270 strictness constructor.
-/
theorem cokernelTopStrictInput_of_shortComplexExact_of_topology
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T)
    (hcok : MetrizableLCA.cokernelSubgroup T.g = ⊤) :
    MetrizableLCA.CokernelTopStrictInput T where
  kernel_equality := targetKernelEquality_of_shortComplexExact hhom hpres hT
  closed_embedding_f := htop.closed_embedding_f
  open_map_g := htop.open_map_g
  cokernel_top_g := hcok

theorem strictShortExact_of_shortComplexExact_of_topology_of_cokernelSubgroup_eq_top
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T)
    (hcok : MetrizableLCA.cokernelSubgroup T.g = ⊤) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_cokernelTopStrictInput
    (cokernelTopStrictInput_of_shortComplexExact_of_topology hhom hpres hT htop hcok)

theorem strictShortExact_of_shortComplexExact_of_topology_of_cokernelπ_eq_zero
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T)
    (hπ : MetrizableLCA.cokernelπ T.g = 0) :
    MetrizableLCA.strictShortExact T :=
  strictShortExact_of_shortComplexExact_of_topology_of_cokernelSubgroup_eq_top
    hhom hpres hT htop
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero T.g hπ)

theorem strictShortExact_of_shortComplexExact_of_topology_of_epi
    {T : ShortComplex MetrizableLCA.{u}} [Epi T.g]
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T) :
    MetrizableLCA.strictShortExact T :=
  strictShortExact_of_shortComplexExact_of_topology_of_cokernelπ_eq_zero
    hhom hpres hT htop (MetrizableLCA.cokernelπ_eq_zero_of_epi T.g)

theorem strictShortExact_of_shortComplexExact_of_topology_of_cokernelObj_isZero
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) (htop : TargetStrictTopology T)
    (hzero : IsZero (MetrizableLCA.cokernelObj T.g)) :
    MetrizableLCA.strictShortExact T :=
  strictShortExact_of_shortComplexExact_of_topology_of_cokernelSubgroup_eq_top
    hhom hpres hT htop
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelObj_isZero T.g hzero)

/-- Categorical exactness transported by a quasi-isomorphism. -/
theorem target_shortComplexExact_of_quasiIso
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ) :
    T.Exact := by
  haveI : ShortComplex.QuasiIso φ := hφ
  exact (ShortComplex.QuasiIso.exact_iff φ).1 hS

/--
Consumer for a quasi-isomorphism route: after exactness is transported to `T`,
the same explicit topology and cokernel-zero/right-exactness input construct
`strictShortExact T`.
-/
theorem strictShortExact_of_quasiIso_of_topology_of_cokernelSubgroup_eq_top
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ)
    (htop : TargetStrictTopology T)
    (hcok : MetrizableLCA.cokernelSubgroup T.g = ⊤) :
    MetrizableLCA.strictShortExact T :=
  strictShortExact_of_shortComplexExact_of_topology_of_cokernelSubgroup_eq_top
    (T := T) inferInstance hpres (target_shortComplexExact_of_quasiIso φ hS hφ) htop hcok

theorem strictShortExact_of_quasiIso_of_topology_of_cokernelObj_isZero
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ)
    (htop : TargetStrictTopology T)
    (hzero : IsZero (MetrizableLCA.cokernelObj T.g)) :
    MetrizableLCA.strictShortExact T :=
  strictShortExact_of_quasiIso_of_topology_of_cokernelSubgroup_eq_top φ hpres hS hφ htop
    (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelObj_isZero T.g hzero)

/--
Names for right-end bridges searched for but not found in the local API.
The W246 counterexample rules out the second declaration without an extra
right-exactness hypothesis.
-/
def missingRightExactnessDeclarations : List String :=
  ["MetrizableLCA.cokernelObj_isZero_of_rightHomologyZero :
      right-homology-zero T -> IsZero (MetrizableLCA.cokernelObj T.g)",
    "MetrizableLCA.epi_g_of_rightHomologyZero :
      right-homology-zero T -> Epi T.g",
    "MetrizableLCA.cokernelπ_eq_zero_of_rightHomologyZero :
      right-homology-zero T -> MetrizableLCA.cokernelπ T.g = 0",
    "MetrizableLCA.cokernelSubgroup_eq_top_of_rightHomologyZero :
      right-homology-zero T -> MetrizableLCA.cokernelSubgroup T.g = ⊤",
    "not valid: T.Exact -> Function.Surjective (T.g : T.X₂ -> T.X₃)"]

theorem missingRightExactnessDeclarations_count :
    missingRightExactnessDeclarations.length = 5 := rfl

/-- Closest currently available declarations checked below. -/
def closestAvailableDeclarations : List String :=
  ["ShortComplex.QuasiIso.exact_iff",
    "ShortComplex.exact_iff_isZero_homology",
    "ShortComplex.HasRightHomology",
    "ShortComplex.rightHomology",
    "ShortComplex.rightHomologyι",
    "ShortComplex.pOpcycles",
    "ShortComplex.fromOpcycles",
    "ShortComplex.homologyMap",
    "ShortComplex.homologyπ",
    "ShortComplex.homologyι",
    "MetrizableLCA.cokernelSubgroup_eq_top_iff_cokernelObj_isZero",
    "MetrizableLCA.cokernelπ_eq_zero_iff_cokernelSubgroup_eq_top",
    "MetrizableLCA.cokernelπ_eq_zero_of_epi",
    "MetrizableLCA.surjective_iff_cokernelSubgroup_eq_top_of_isOpenMap",
    "W246 boundary theorem name: ShortComplexExactnessHomologyZeroW246.no_shortComplexExact_to_targetSurjectivity"]

theorem closestAvailableDeclarations_count :
    closestAvailableDeclarations.length = 15 := rfl

/-- Minimal route that remains after this audit. -/
def minimalRemainingRoute : List String :=
  ["exactness-to-kernel: use targetKernelEquality_of_shortComplexExact with HasHomology and PreservesHomology",
    "right-exactness-to-cokernel-zero/epi: still needs an explicit right-homology-zero-to-cokernel or right-homology-zero-to-epi theorem",
    "closed embedding: still a separate topology field for T.f",
    "open map: still a separate topology field for T.g; v270 turns cokernelSubgroup = top plus open map into surjectivity"]

theorem minimalRemainingRoute_count :
    minimalRemainingRoute.length = 4 := rfl

/-- Compact final state for the parent verifier and downstream workers. -/
def auditStatus : List String :=
  ["proved: T.Exact plus HasHomology/PreservesHomology gives the element-level kernel equality bridge",
    "proved: kernel bridge plus topology plus Epi/cokernelπ=0/cokernelSubgroup=top/IsZero cokernelObj constructs strictShortExact",
    "proved: transported exactness via ShortComplex.QuasiIso.exact_iff feeds the same cokernel-top and cokernel-object-zero consumers",
    "preserved: W246 boundary; ShortComplex.Exact alone is not used as a right-surjectivity source",
    "blocked: no current declaration connects a right-homology-zero datum to Epi T.g or IsZero (cokernelObj T.g) in MetrizableLCA"]

theorem auditStatus_count :
    auditStatus.length = 5 := rfl

section Checks

#check TargetKernelEquality
#check TargetStrictTopology
#check targetKernelEquality_of_shortComplexExact
#check cokernelTopStrictInput_of_shortComplexExact_of_topology
#check strictShortExact_of_shortComplexExact_of_topology_of_cokernelSubgroup_eq_top
#check strictShortExact_of_shortComplexExact_of_topology_of_cokernelπ_eq_zero
#check strictShortExact_of_shortComplexExact_of_topology_of_epi
#check strictShortExact_of_shortComplexExact_of_topology_of_cokernelObj_isZero
#check target_shortComplexExact_of_quasiIso
#check strictShortExact_of_quasiIso_of_topology_of_cokernelSubgroup_eq_top
#check strictShortExact_of_quasiIso_of_topology_of_cokernelObj_isZero
#check missingRightExactnessDeclarations_count
#check closestAvailableDeclarations_count
#check minimalRemainingRoute_count
#check auditStatus_count
#check ShortComplex.QuasiIso.exact_iff
#check ShortComplex.exact_iff_isZero_homology
#check ShortComplex.HasRightHomology
#check ShortComplex.rightHomology
#check ShortComplex.rightHomologyι
#check ShortComplex.pOpcycles
#check ShortComplex.fromOpcycles
#check ShortComplex.homologyMap
#check ShortComplex.homologyπ
#check ShortComplex.homologyι
#check MetrizableLCA.CokernelTopStrictInput
#check MetrizableLCA.strictShortExact_of_cokernelTopStrictInput
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_epi
#check MetrizableLCA.cokernelSubgroup_eq_top_iff_cokernelObj_isZero
#check MetrizableLCA.cokernelπ_eq_zero_iff_cokernelSubgroup_eq_top
#check MetrizableLCA.cokernelπ_eq_zero_of_epi
#check MetrizableLCA.surjective_iff_cokernelSubgroup_eq_top_of_isOpenMap

end Checks

end ShortComplexRightExactnessExtractionW258

end LeanLCAExactChallenge
