import LeanLCAExactChallenge.LCA.Basic

/-!
Strict short exact sequences in the local `MetrizableLCA` category.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

/--
The strict short exact sequences specified in the challenge: closed inclusion on
the left, open surjection on the right, and exactness after forgetting topology.
-/
structure StrictShortExact (S : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_inclusion : IsClosedEmbedding (S.f : S.X₁ → S.X₂)
  open_map : IsOpenMap (S.g : S.X₂ → S.X₃)
  surjective : Function.Surjective (S.g : S.X₂ → S.X₃)
  algebraic_exact : ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂

/-- Predicate for strict short exact complexes. -/
def strictShortExact (S : ShortComplex MetrizableLCA.{u}) : Prop :=
  StrictShortExact S

lemma closed_inclusion_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) : IsClosedEmbedding (S.f : S.X₁ → S.X₂) :=
  hS.closed_inclusion

lemma open_surjection_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    IsOpenMap (S.g : S.X₂ → S.X₃) ∧ Function.Surjective (S.g : S.X₂ → S.X₃) :=
  ⟨hS.open_map, hS.surjective⟩

lemma algebraic_kernel_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    Function.Injective (S.f : S.X₁ → S.X₂) ∧
      ∀ x₂ : S.X₂, S.g x₂ = 0 ↔ ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  refine ⟨hS.closed_inclusion.injective, ?_⟩
  intro x₂
  constructor
  · exact hS.algebraic_exact x₂
  · rintro ⟨x₁, rfl⟩
    change (S.f ≫ S.g : S.X₁ ⟶ S.X₃) x₁ = (0 : S.X₁ ⟶ S.X₃) x₁
    exact congrArg (fun h : S.X₁ ⟶ S.X₃ ↦ h x₁) S.zero

lemma algebraic_cokernel_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    Function.Surjective (S.g : S.X₂ → S.X₃) :=
  hS.surjective

end MetrizableLCA

end LeanLCAExactChallenge
