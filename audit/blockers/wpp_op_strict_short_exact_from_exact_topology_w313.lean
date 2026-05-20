import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W313: reducing WPP-op strict short exact colimit closure to exactness plus the
two topological fields.

W310 proves that the right map of a WPP-op colimit is categorically epi, and
therefore becomes surjective once its underlying map is open.  The local
`MetrizableLCA.strictShortExact_of_exact_of_topology` constructor then shows
that the remaining strict-short-exact colimit problem is not right-surjectivity
or packaging: it is exactness, homology availability/preservation, closedness of
the left map, and openness of the right map for the chosen colimit point.

This file is intentionally nonterminal progress and makes no product-success
claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpStrictShortExactFromExactTopologyW313

/-- Closure target for strict short exactness under the chosen WPP-op colimit. -/
abbrev strictShortExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          MetrizableLCA.strictShortExact cs.pt

/-- Exactness of the chosen WPP-op colimit short complex. -/
abbrev exact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.Exact

/-- Homology availability for the chosen WPP-op colimit short complex. -/
abbrev hasHomology_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.HasHomology

/-- Closedness of the left map of the chosen WPP-op colimit short complex. -/
abbrev leftClosedEmbedding_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- Openness of the right map of the chosen WPP-op colimit short complex. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

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
Checked consumer: exactness plus the two topology fields imply strict short
exactness for the WPP-op colimit point.  Right-surjectivity is supplied by W310's
categorical-epi argument plus openness of the same right map.
-/
theorem strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology
    (hhom : hasHomology_walkingParallelPairOp_colimitClosure)
    (hpres : (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology)
    (hexact : exact_walkingParallelPairOp_colimitClosure)
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure) :
    strictShortExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  haveI : cs.pt.HasHomology := hhom S cs hcs hS
  haveI : Epi cs.pt.g :=
    rightMapEpi_walkingParallelPairOp_colimitClosure_direct S cs hcs hS
  have hsurj : Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
      (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
        (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
      (hopen S cs hcs hS)
  exact MetrizableLCA.strictShortExact_of_exact_of_topology
    inferInstance hpres (hexact S cs hcs hS)
    (hclosed S cs hcs hS) (hopen S cs hcs hS) hsurj

/-- Machine-readable W313 frontier state. -/
structure WppOpStrictShortExactFromExactTopologyState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W313 state for downstream workers. -/
def currentWppOpStrictShortExactFromExactTopologyState :
    WppOpStrictShortExactFromExactTopologyState where
  seed := "w313-parent-20260521T0200Z"
  provedConsumer :=
    "strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology"
  remainingInputs :=
    ["hasHomology_walkingParallelPairOp_colimitClosure",
      "PreservesHomology for forget₂ MetrizableLCA AddCommGrpCat",
      "exact_walkingParallelPairOp_colimitClosure",
      "leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpStrictShortExactFromExactTopologyState_productSuccess :
    currentWppOpStrictShortExactFromExactTopologyState.productSuccessClaimed = false := rfl

section Checks

#check strictShortExact_walkingParallelPairOp_colimitClosure
#check exact_walkingParallelPairOp_colimitClosure
#check hasHomology_walkingParallelPairOp_colimitClosure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure
#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology
#check currentWppOpStrictShortExactFromExactTopologyState
#check currentWppOpStrictShortExactFromExactTopologyState_productSuccess
#check MetrizableLCA.strictShortExact_of_exact_of_topology
#check colim.map_epi'

end Checks

end WppOpStrictShortExactFromExactTopologyW313

end LeanLCAExactChallenge
