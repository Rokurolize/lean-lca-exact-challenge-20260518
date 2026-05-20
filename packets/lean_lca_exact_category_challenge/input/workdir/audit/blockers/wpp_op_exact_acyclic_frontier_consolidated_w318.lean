import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W318: consolidated WPP-op exact-acyclic frontier after W286/W287/W289/W317.

W317 showed that W271's exact-acyclic WPP-op colimit-closure input follows from
three direct strict-exact fields: left closed embedding, right open map, and
algebraic exactness.  W286, W287, and W289 each narrowed one of those fields to a
smaller API boundary.  This file combines those consumers into one checked
frontier statement.

Remaining source theorems after this file:

* WPP-op colimits preserve left closed embeddings of the short-complex left maps;
* WPP-op component colimits preserve openness of the induced right map;
* the WPP-op colimit point satisfies the algebraic kernel exactness field.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpExactAcyclicFrontierConsolidatedW318

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/-- W271's exact-acyclic WPP-op colimit closure input, restated locally. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        (∀ j : WalkingParallelPairᵒᵖ, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/-- WPP-op colimits preserve the left closed-embedding field. -/
abbrev wppOp_colimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- WPP-op component colimits preserve openness of the induced right map. -/
abbrev openMap_walkingParallelPairOp_colimitMap_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) →
        IsColimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCocone cs) →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsOpenMap ((S.obj j).g : (S.obj j).X₂ → (S.obj j).X₃)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Direct algebraic exactness at the WPP-op colimit point. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Left field consumer from W289's boundary. -/
theorem leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves
    (hpres : wppOp_colimit_preserves_leftClosedEmbedding) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) := by
  intro S cs hcs hS
  exact hpres S cs hcs (fun j => (hS j).closed_inclusion)

/-- Right-open field consumer from W286's boundary. -/
theorem rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary
    (hboundary : openMap_walkingParallelPairOp_colimitMap_boundary) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) := by
  intro S cs hcs hS
  exact hboundary S cs
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- The colimit right map is categorically epi, by componentwise strict exactness. -/
theorem rightMapEpi_walkingParallelPairOp_colimitClosure_direct
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hcs : IsColimit cs)
    (hS : ∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) :
    Epi cs.pt.g := by
  let φ : (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) :=
    { app := fun j => (S.obj j).g
      naturality := fun j j' f => (S.map f).comm₂₃ }
  haveI hφ : ∀ j, Epi (φ.app j) := fun j => by
    dsimp [φ]
    apply (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).epi_of_epi_map
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (hS j).surjective
  exact colim.map_epi' φ (ShortComplex.π₂.mapCocone cs)
    (isColimitOfPreserves ShortComplex.π₃ hcs) cs.pt.g
    (fun j => by
      dsimp [φ]
      simpa using (cs.ι.app j).comm₂₃)

/--
Consolidated strictness consumer from the W286/W287/W289-style boundaries.
-/
theorem strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
    (hclosed : wppOp_colimit_preserves_leftClosedEmbedding)
    (hopen : openMap_walkingParallelPairOp_colimitMap_boundary)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            MetrizableLCA.strictShortExact cs.pt := by
  intro S cs hcs hS
  have hopen_cs : IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary hopen S cs hcs hS
  haveI : Epi cs.pt.g :=
    rightMapEpi_walkingParallelPairOp_colimitClosure_direct S cs hcs hS
  have hsurj : Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
      (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
        (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
      hopen_cs
  exact
    { closed_inclusion :=
        leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves hclosed
          S cs hcs hS
      open_map := hopen_cs
      surjective := hsurj
      algebraic_exact := halg S cs hcs hS }

/--
Consolidated exact-acyclic consumer: W271's WPP-op exact-acyclic colimit closure
follows from the three remaining source-level field-preservation inputs.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
    (hclosed : wppOp_colimit_preserves_leftClosedEmbedding)
    (hopen : openMap_walkingParallelPairOp_colimitMap_boundary)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  intro K ck hck hK i
  let S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0} :=
    K ⋙ degreeShortComplexFunctor i
  let cs : Cocone S := (degreeShortComplexFunctor i).mapCocone ck
  have hcs : IsColimit cs := by
    refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).prev i)) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) i) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).next i)) hck)
  have hS : ∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j) := by
    intro j
    exact hK j i
  exact strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
    hclosed hopen halg S cs hcs hS

/-- Machine-readable W318 frontier state. -/
structure WppOpExactAcyclicFrontierConsolidatedState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W318 state for downstream workers. -/
def currentWppOpExactAcyclicFrontierConsolidatedState :
    WppOpExactAcyclicFrontierConsolidatedState where
  seed := "w318-parent-20260521T0310Z"
  provedConsumer :=
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier"
  remainingInputs :=
    ["wppOp_colimit_preserves_leftClosedEmbedding",
      "openMap_walkingParallelPairOp_colimitMap_boundary",
      "algebraicExact_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpExactAcyclicFrontierConsolidatedState_productSuccess :
    currentWppOpExactAcyclicFrontierConsolidatedState.productSuccessClaimed = false := rfl

section Checks

#check degreeShortComplexFunctor
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check wppOp_colimit_preserves_leftClosedEmbedding
#check openMap_walkingParallelPairOp_colimitMap_boundary
#check algebraicExact_walkingParallelPairOp_colimitClosure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
#check currentWppOpExactAcyclicFrontierConsolidatedState
#check currentWppOpExactAcyclicFrontierConsolidatedState_productSuccess
#check ShortComplex.π₂
#check ShortComplex.π₃
#check ShortComplex.isColimitOfIsColimitπ
#check colim.map_epi'

end Checks

end WppOpExactAcyclicFrontierConsolidatedW318

end LeanLCAExactChallenge
