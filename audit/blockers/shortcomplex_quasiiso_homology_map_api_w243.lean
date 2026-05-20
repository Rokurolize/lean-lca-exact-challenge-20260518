import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W243 audit: homology-map API boundary for strict `MetrizableLCA` targets.

W242 isolated the target algebraic fields needed for
`MetrizableLCA.strictShortExact T`. This file probes the current
`ShortComplex.QuasiIso` API: mathlib transports categorical
`ShortComplex.Exact`, but the available homology-object declarations do not
directly expose the concrete element-level kernel equality or surjectivity of
`T.g` used by the local strict predicate.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory

namespace ShortComplexQuasiIsoHomologyMapAPIW243

/-- Concrete target-side kernel equality needed by `strictShortExact`. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Concrete target-side surjectivity needed by `strictShortExact`. -/
abbrev TargetSurjectivity (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  Function.Surjective (T.g : T.X₂ → T.X₃)

/-- The algebraic target payload separated from the topological strict fields. -/
structure TargetAlgebraicPayload (T : ShortComplex MetrizableLCA.{u}) : Prop where
  kernel_equality : TargetKernelEquality T
  surjective_g : TargetSurjectivity T

/-- The source strict predicate already exposes the concrete algebraic payload. -/
theorem source_targetAlgebraicPayload
    {S : ShortComplex MetrizableLCA.{u}} (hS : MetrizableLCA.strictShortExact S) :
    TargetAlgebraicPayload S where
  kernel_equality := (MetrizableLCA.algebraic_kernel_of_strict hS).2
  surjective_g := (MetrizableLCA.open_surjection_of_strict hS).2

/--
The current quasi-isomorphism API transports categorical short-complex
exactness, i.e. zero homology, from source to target.
-/
theorem target_shortComplexExact_of_quasiIso
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ) :
    T.Exact := by
  haveI : ShortComplex.QuasiIso φ := hφ
  exact (ShortComplex.QuasiIso.exact_iff φ).1 hS

/-- A hypothetical bridge from categorical exactness to concrete kernel equality. -/
abbrev ShortComplexExactToTargetKernel : Prop :=
  ∀ {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology],
    T.Exact → TargetKernelEquality T

/-- A hypothetical bridge from categorical exactness to concrete surjectivity. -/
abbrev ShortComplexExactToTargetSurjectivity : Prop :=
  ∀ {T : ShortComplex MetrizableLCA.{u}} [T.HasHomology],
    T.Exact → TargetSurjectivity T

/--
If the missing concrete bridges from categorical exactness are supplied, the
present homology-map API is enough for the algebraic target payload.
-/
theorem targetAlgebraicPayload_of_quasiIso_of_exactBridges
    (hker : ShortComplexExactToTargetKernel.{u})
    (hsurj : ShortComplexExactToTargetSurjectivity.{u})
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ) :
    TargetAlgebraicPayload T where
  kernel_equality := hker (target_shortComplexExact_of_quasiIso φ hS hφ)
  surjective_g := hsurj (target_shortComplexExact_of_quasiIso φ hS hφ)

/--
Smaller conditional surjectivity extractor: it records the exact gap after
`ShortComplex.QuasiIso.exact_iff`.
-/
abbrev QuasiIsoTargetSurjectivityExtractionFromExactBridge : Prop :=
  ShortComplexExactToTargetSurjectivity.{u} →
    ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
      [S.HasHomology] [T.HasHomology],
      S.Exact → ShortComplex.QuasiIso φ → TargetSurjectivity T

/-- The conditional surjectivity extractor follows from the categorical exactness bridge. -/
theorem quasiIsoTargetSurjectivityExtraction_fromExactBridge :
    QuasiIsoTargetSurjectivityExtractionFromExactBridge.{u} := by
  intro hsurj S T φ _ _ hS hφ
  exact hsurj (target_shortComplexExact_of_quasiIso φ hS hφ)

/--
Names for the currently missing concrete declarations.

The first item would connect local strict exactness to mathlib's categorical
homology exactness. The second and third would turn the transported zero
homology of `T` into the element-level fields required by W242.
-/
def missingConcreteHomologyDeclarations : List String :=
  ["MetrizableLCA.shortComplexExact_of_strictShortExact :
      MetrizableLCA.strictShortExact T -> T.Exact",
    "MetrizableLCA.targetKernelEquality_of_shortComplexExact :
      T.Exact -> forall x2 : T.X2, T.g x2 = 0 <-> exists x1 : T.X1, T.f x1 = x2",
    "MetrizableLCA.targetSurjective_g_of_shortComplexExact :
      T.Exact -> Function.Surjective (T.g : T.X2 -> T.X3)",
    "or, equivalently, an element-level API from ShortComplex.homologyπ/homologyι
      plus cycles/opcycles maps to the range of T.f and values of T.g"]

theorem missingConcreteHomologyDeclarations_count :
    missingConcreteHomologyDeclarations.length = 4 := rfl

/-- Compact audit conclusion for downstream review. -/
def homologyMapAPIAuditStatus : List String :=
  ["proved: ShortComplex.QuasiIso transports ShortComplex.Exact via homologyMap",
    "packaged: exactness-to-kernel and exactness-to-surjectivity bridges would give W242 algebraic payload",
    "packaged: a smaller conditional surjectivity extraction from a target exactness bridge",
    "blocked: current MetrizableLCA strict API exposes source concrete fields but not target fields from transported homology exactness",
    "missing: concrete element-level declarations relating ShortComplex.Exact/homologyπ/homologyι to T.g kernel membership and surjectivity"]

theorem homologyMapAPIAuditStatus_count :
    homologyMapAPIAuditStatus.length = 5 := rfl

section Checks

#check TargetKernelEquality
#check TargetSurjectivity
#check TargetAlgebraicPayload
#check source_targetAlgebraicPayload
#check target_shortComplexExact_of_quasiIso
#check ShortComplexExactToTargetKernel
#check ShortComplexExactToTargetSurjectivity
#check targetAlgebraicPayload_of_quasiIso_of_exactBridges
#check QuasiIsoTargetSurjectivityExtractionFromExactBridge
#check quasiIsoTargetSurjectivityExtraction_fromExactBridge
#check missingConcreteHomologyDeclarations
#check missingConcreteHomologyDeclarations_count
#check homologyMapAPIAuditStatus
#check homologyMapAPIAuditStatus_count
#check ShortComplex.QuasiIso
#check ShortComplex.quasiIso_iff
#check ShortComplex.QuasiIso.exact_iff
#check ShortComplex.exact_iff_isZero_homology
#check ShortComplex.homologyMap
#check ShortComplex.homologyπ
#check ShortComplex.homologyι
#check ShortComplex.π_homologyMap_ι
#check MetrizableLCA.strictShortExact
#check MetrizableLCA.algebraic_kernel_of_strict
#check MetrizableLCA.open_surjection_of_strict

end Checks

end ShortComplexQuasiIsoHomologyMapAPIW243

end LeanLCAExactChallenge
