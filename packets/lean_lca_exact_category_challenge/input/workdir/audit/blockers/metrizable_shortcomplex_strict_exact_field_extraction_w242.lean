import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W242 audit: strict-field extraction boundary for short-complex quasi-isomorphisms.

This separates the algebraic and topological fields required to transport
`MetrizableLCA.strictShortExact` along `ShortComplex.QuasiIso`.  The file records
what mathlib's quasi-isomorphism API exposes and names the missing extraction
theorems without claiming product success.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableShortComplexStrictExactFieldExtractionW242

structure TargetStrictTopology (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)

structure TargetAlgebraicExactness (T : ShortComplex MetrizableLCA.{u}) : Prop where
  kernel_equality :
    ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂
  surjective_g : Function.Surjective (T.g : T.X₂ → T.X₃)

theorem strictShortExact_of_targetTopology_of_targetAlgebraic
    {T : ShortComplex MetrizableLCA.{u}}
    (htop : TargetStrictTopology T) (halg : TargetAlgebraicExactness T) :
    MetrizableLCA.strictShortExact T where
  closed_inclusion := htop.closed_embedding_f
  open_map := htop.open_map_g
  surjective := halg.surjective_g
  algebraic_exact := by
    intro x₂ hx₂
    exact (halg.kernel_equality x₂).mp hx₂

theorem source_targetAlgebraicExactness
    {S : ShortComplex MetrizableLCA.{u}} (hS : MetrizableLCA.strictShortExact S) :
    TargetAlgebraicExactness S where
  kernel_equality := (MetrizableLCA.algebraic_kernel_of_strict hS).2
  surjective_g := (MetrizableLCA.open_surjection_of_strict hS).2

theorem source_targetStrictTopology
    {S : ShortComplex MetrizableLCA.{u}} (hS : MetrizableLCA.strictShortExact S) :
    TargetStrictTopology S where
  closed_embedding_f := MetrizableLCA.closed_inclusion_of_strict hS
  open_map_g := (MetrizableLCA.open_surjection_of_strict hS).1

structure QuasiIsoAPIWitness
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology] : Prop where
  homology_map_isIso : IsIso (ShortComplex.homologyMap φ)

theorem quasiIso_homologyMap_isIso
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology] (hφ : ShortComplex.QuasiIso φ) :
    IsIso (ShortComplex.homologyMap φ) := by
  haveI : ShortComplex.QuasiIso φ := hφ
  infer_instance

theorem quasiIsoAPIWitness_of_quasiIso
    {S T : ShortComplex MetrizableLCA.{u}} {φ : S ⟶ T}
    [S.HasHomology] [T.HasHomology] (hφ : ShortComplex.QuasiIso φ) :
    QuasiIsoAPIWitness φ where
  homology_map_isIso := quasiIso_homologyMap_isIso φ hφ

abbrev QuasiIsoTargetAlgebraicExtraction : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      TargetAlgebraicExactness T

abbrev QuasiIsoTargetTopologyExtraction : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      TargetStrictTopology T

abbrev MetrizableLCAShortComplexQuasiIsoStrictTransport : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      MetrizableLCA.strictShortExact T

theorem strictTransport_of_algebraicExtraction_of_topologyExtraction
    (halg : QuasiIsoTargetAlgebraicExtraction.{u})
    (htop : QuasiIsoTargetTopologyExtraction.{u}) :
    MetrizableLCAShortComplexQuasiIsoStrictTransport.{u} := by
  intro S T φ _ _ hS hφ
  exact strictShortExact_of_targetTopology_of_targetAlgebraic
    (htop φ hS hφ) (halg φ hS hφ)

abbrev QuasiIsoTargetKernelExtraction : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

abbrev QuasiIsoTargetSurjectivityExtraction : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      Function.Surjective (T.g : T.X₂ → T.X₃)

theorem algebraicExtraction_of_kernelExtraction_of_surjectivityExtraction
    (hker : QuasiIsoTargetKernelExtraction.{u})
    (hsurj : QuasiIsoTargetSurjectivityExtraction.{u}) :
    QuasiIsoTargetAlgebraicExtraction.{u} := by
  intro S T φ _ _ hS hφ
  exact
    { kernel_equality := hker φ hS hφ
      surjective_g := hsurj φ hS hφ }

def quasiIsoStrictFieldExtractionBoundary : List String :=
  ["ShortComplex.QuasiIso φ is equivalent to IsIso (ShortComplex.homologyMap φ)",
    "source strictShortExact S exposes source kernel equality and source surjectivity",
    "source strictShortExact S exposes source closed embedding and source open map",
    "missing: a theorem extracting target kernel equality from hS and hφ",
    "missing: a theorem extracting target surjectivity of T.g from hS and hφ",
    "missing: a theorem extracting target closed embedding of T.f from hS and hφ",
    "missing: a theorem extracting target open-map status of T.g from hS and hφ"]

theorem quasiIsoStrictFieldExtractionBoundary_count :
    quasiIsoStrictFieldExtractionBoundary.length = 7 := rfl

section Checks

#check TargetStrictTopology
#check TargetAlgebraicExactness
#check strictShortExact_of_targetTopology_of_targetAlgebraic
#check source_targetAlgebraicExactness
#check source_targetStrictTopology
#check QuasiIsoAPIWitness
#check quasiIso_homologyMap_isIso
#check quasiIsoAPIWitness_of_quasiIso
#check QuasiIsoTargetAlgebraicExtraction
#check QuasiIsoTargetTopologyExtraction
#check MetrizableLCAShortComplexQuasiIsoStrictTransport
#check strictTransport_of_algebraicExtraction_of_topologyExtraction
#check QuasiIsoTargetKernelExtraction
#check QuasiIsoTargetSurjectivityExtraction
#check algebraicExtraction_of_kernelExtraction_of_surjectivityExtraction
#check quasiIsoStrictFieldExtractionBoundary_count
#check ShortComplex.QuasiIso
#check ShortComplex.quasiIso_iff
#check ShortComplex.homologyMap

end Checks

end MetrizableShortComplexStrictExactFieldExtractionW242

end LeanLCAExactChallenge
