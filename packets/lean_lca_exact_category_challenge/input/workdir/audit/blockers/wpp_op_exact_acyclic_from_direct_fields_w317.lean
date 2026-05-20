import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W317: a direct-field route to WPP-op exact-acyclic colimit closure.

W314 routed W271's exact-acyclic WPP-op colimit closure through
`ShortComplex.Exact`, `HasHomology`, and forgetful `PreservesHomology`.  This
file records a complementary route that avoids those global homology inputs.

The checked consumer needs only three concrete fields for WPP-op colimit points:

* the left map is a closed embedding;
* the right map is open;
* the element-level algebraic kernel equality holds.

The missing right-surjectivity field is supplied by the same categorical-epi
argument as W310 plus openness of the colimit right map.  The degreewise
short-complex colimit comparison is rebuilt as in W300.

This is nonterminal progress: the three concrete field closures still need
source proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpExactAcyclicFromDirectFieldsW317

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

/-- Closure of the left closed-embedding field under the chosen WPP-op colimit. -/
abbrev leftClosedEmbedding_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Closure of the algebraic kernel exactness field under the chosen WPP-op colimit. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Strict-short-exact WPP-op colimit closure. -/
abbrev strictShortExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          MetrizableLCA.strictShortExact cs.pt

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
The direct concrete fields imply WPP-op strict-short-exact colimit closure,
without using `ShortComplex.Exact`, `HasHomology`, or forgetful
`PreservesHomology`.
-/
theorem strictShortExact_walkingParallelPairOp_colimitClosure_of_direct_fields
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    strictShortExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  haveI : Epi cs.pt.g :=
    rightMapEpi_walkingParallelPairOp_colimitClosure_direct S cs hcs hS
  have hsurj : Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
      (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
        (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
      (hopen S cs hcs hS)
  exact
    { closed_inclusion := hclosed S cs hcs hS
      open_map := hopen S cs hcs hS
      surjective := hsurj
      algebraic_exact := halg S cs hcs hS }

/--
The direct concrete fields imply W271's exact-acyclic WPP-op colimit closure.
This bypasses the W314 homology-preservation route.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_direct_fields
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure)
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
  exact strictShortExact_walkingParallelPairOp_colimitClosure_of_direct_fields
    hclosed hopen halg S cs hcs hS

/-- Machine-readable W317 frontier state. -/
structure WppOpExactAcyclicFromDirectFieldsState : Type where
  seed : String
  provedConsumer : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W317 state for downstream workers. -/
def currentWppOpExactAcyclicFromDirectFieldsState :
    WppOpExactAcyclicFromDirectFieldsState where
  seed := "w317-parent-20260521T0300Z"
  provedConsumer :=
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_direct_fields"
  removedInputs :=
    ["CategoryWithHomology MetrizableLCA",
      "PreservesHomology for forget₂ MetrizableLCA AddCommGrpCat",
      "ShortComplex.Exact at the WPP-op colimit point"]
  remainingInputs :=
    ["leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure",
      "algebraicExact_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpExactAcyclicFromDirectFieldsState_productSuccess :
    currentWppOpExactAcyclicFromDirectFieldsState.productSuccessClaimed = false := rfl

section Checks

#check degreeShortComplexFunctor
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure
#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check algebraicExact_walkingParallelPairOp_colimitClosure
#check strictShortExact_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_direct_fields
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_direct_fields
#check currentWppOpExactAcyclicFromDirectFieldsState
#check currentWppOpExactAcyclicFromDirectFieldsState_productSuccess
#check HomologicalComplex.shortComplexFunctor
#check ShortComplex.isColimitOfIsColimitπ
#check colim.map_epi'
#check MetrizableLCA.strictShortExact

end Checks

end WppOpExactAcyclicFromDirectFieldsW317

end LeanLCAExactChallenge
