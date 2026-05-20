import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W287: algebraic exactness for the WPP-op strict-short-exact colimit frontier.

The full field target asks for the element-level kernel equality at the colimit
short complex.  This parent-owned audit file narrows it to the categorical
boundary already used by the product API: once the WPP-op colimit point is known
to be `ShortComplex.Exact`, the existing forgetful-homology bridge gives the
requested algebraic kernel field.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AlgebraicExactWppOpColimitW287

/-- The W307 algebraic kernel-exactness field target, restated locally. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/--
Categorical exactness closure for the same WPP-op colimit.  This is deliberately
weaker than strict-short-exact closure: it names only the categorical exactness
needed to consume `ShortComplex.exact_iff_of_hasForget` at the colimit point.
-/
abbrev shortComplexExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.Exact

/-- Homology instances needed at the WPP-op colimit point. -/
abbrev colimitPointHasHomology : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → cs.pt.HasHomology

/-- The local forgetful functor preserves homology for this exactness bridge. -/
abbrev forgetPreservesHomology : Prop :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology

/-- Element-level kernel equality consumed by the algebraic field. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/--
The existing categorical bridge specialized to universe zero.  This is the
checked algebraic core of the WPP-op field: `ShortComplex.Exact` gives precisely
the middle kernel/range equality after the standard homology inputs are present.
-/
theorem targetKernelEquality_of_shortComplexExact
    {T : ShortComplex MetrizableLCA.{0}}
    (hhom : T.HasHomology)
    (hpres : forgetPreservesHomology)
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
Consumer back to W307's algebraic field.  Thus W287 reduces the field to the
checked boundary `shortComplexExact_walkingParallelPairOp_colimitClosure` plus
the homology-preservation inputs required by the local ShortComplex API.
-/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_shortComplexExactClosure
    (hhom : colimitPointHasHomology)
    (hpres : forgetPreservesHomology)
    (hexact : shortComplexExact_walkingParallelPairOp_colimitClosure) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS x₂ hx₂
  exact
    ((targetKernelEquality_of_shortComplexExact (hhom S cs hcs) hpres
        (hexact S cs hcs hS)) x₂).mp hx₂

/-- Minimal checked package for the algebraic exactness field. -/
structure AlgebraicExactBoundaryPackage : Prop where
  colimit_homology : colimitPointHasHomology
  forget_preserves_homology : forgetPreservesHomology
  shortComplex_exact_closure : shortComplexExact_walkingParallelPairOp_colimitClosure

/-- The checked package is sufficient for the W307 algebraic field. -/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_boundaryPackage
    (h : AlgebraicExactBoundaryPackage) :
    algebraicExact_walkingParallelPairOp_colimitClosure :=
  algebraicExact_walkingParallelPairOp_colimitClosure_of_shortComplexExactClosure
    h.colimit_homology h.forget_preserves_homology h.shortComplex_exact_closure

/-- Machine-readable frontier state for W287. -/
structure AlgebraicExactWppOpColimitState : Type where
  seed : String
  selectedRoute : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W287 boundary state. -/
def currentAlgebraicExactWppOpColimitState :
    AlgebraicExactWppOpColimitState where
  seed := "w287-20260520T164319Z-7e7a014ad6fd"
  selectedRoute :=
    "reduce W307 algebraic field to ShortComplex.Exact at the WPP-op colimit point"
  provedConsumer :=
    "algebraicExact_walkingParallelPairOp_colimitClosure_of_shortComplexExactClosure"
  remainingInputs :=
    ["colimitPointHasHomology",
      "forgetPreservesHomology",
      "shortComplexExact_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentAlgebraicExactWppOpColimitState_productSuccess :
    currentAlgebraicExactWppOpColimitState.productSuccessClaimed = false := rfl

def algebraicExactWppOpColimitDeclarationNames : List String :=
  ["algebraicExact_walkingParallelPairOp_colimitClosure",
    "shortComplexExact_walkingParallelPairOp_colimitClosure",
    "colimitPointHasHomology",
    "forgetPreservesHomology",
    "TargetKernelEquality",
    "targetKernelEquality_of_shortComplexExact",
    "algebraicExact_walkingParallelPairOp_colimitClosure_of_shortComplexExactClosure",
    "AlgebraicExactBoundaryPackage",
    "algebraicExact_walkingParallelPairOp_colimitClosure_of_boundaryPackage",
    "currentAlgebraicExactWppOpColimitState"]

theorem algebraicExactWppOpColimitDeclarationNames_count :
    algebraicExactWppOpColimitDeclarationNames.length = 10 := rfl

section Checks

#check algebraicExact_walkingParallelPairOp_colimitClosure
#check shortComplexExact_walkingParallelPairOp_colimitClosure
#check colimitPointHasHomology
#check forgetPreservesHomology
#check TargetKernelEquality
#check targetKernelEquality_of_shortComplexExact
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_shortComplexExactClosure
#check AlgebraicExactBoundaryPackage
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_boundaryPackage
#check currentAlgebraicExactWppOpColimitState
#check currentAlgebraicExactWppOpColimitState_productSuccess
#check algebraicExactWppOpColimitDeclarationNames
#check algebraicExactWppOpColimitDeclarationNames_count
#check ShortComplex.exact_iff_of_hasForget
#check MetrizableLCA.strictShortExact

end Checks

end AlgebraicExactWppOpColimitW287

end LeanLCAExactChallenge
