import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
W314: connecting the W313 exact/topology route back to the W271 exact-acyclic
WPP-op colimit closure input.

W299 reduced exact-acyclic WPP-op colimit closure to a degreewise short-complex
comparison plus short-complex conflation closure.  W300 discharged the comparison.
W313 reduced the short-complex closure to colimit-point exactness, homology
availability/preservation, left closed embedding, and right open map.

This file checks that those W313-style short-complex inputs are sufficient for
the original exact-acyclic WPP-op colimit-closure target.  It does not prove the
remaining exactness/topology inputs themselves and makes no product-success
claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpExactAcyclicFromExactTopologyW314

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

/-- Homology availability for a WPP-op colimit point in short complexes. -/
abbrev hasHomology_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.HasHomology

/-- Exactness for a WPP-op colimit point in short complexes. -/
abbrev exact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          cs.pt.Exact

/-- Closedness of the left map for a WPP-op colimit point in short complexes. -/
abbrev leftClosedEmbedding_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/-- Openness of the right map for a WPP-op colimit point in short complexes. -/
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

/-- W313-style strictness consumer, repeated locally for standalone checking. -/
theorem strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology
    (hhom : hasHomology_walkingParallelPairOp_colimitClosure)
    (hpres : (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology)
    (hexact : exact_walkingParallelPairOp_colimitClosure)
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            MetrizableLCA.strictShortExact cs.pt := by
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

/--
The W313-style exact/topology inputs imply W271's exact-acyclic WPP-op colimit
closure.  The degreewise comparison is discharged directly as in W300.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_exact_topology
    (hhom : hasHomology_walkingParallelPairOp_colimitClosure)
    (hpres : (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology)
    (hexact : exact_walkingParallelPairOp_colimitClosure)
    (hclosed : leftClosedEmbedding_walkingParallelPairOp_colimitClosure)
    (hopen : rightOpenMap_walkingParallelPairOp_colimitClosure) :
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
  exact strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology
    hhom hpres hexact hclosed hopen S cs hcs hS

/-- Machine-readable W314 frontier state. -/
structure WppOpExactAcyclicFromExactTopologyState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W314 state for downstream workers. -/
def currentWppOpExactAcyclicFromExactTopologyState :
    WppOpExactAcyclicFromExactTopologyState where
  seed := "w314-parent-20260521T0215Z"
  provedConsumer :=
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_exact_topology"
  remainingInputs :=
    ["hasHomology_walkingParallelPairOp_colimitClosure",
      "PreservesHomology for forget₂ MetrizableLCA AddCommGrpCat",
      "exact_walkingParallelPairOp_colimitClosure",
      "leftClosedEmbedding_walkingParallelPairOp_colimitClosure",
      "rightOpenMap_walkingParallelPairOp_colimitClosure"]
  productSuccessClaimed := false

theorem currentWppOpExactAcyclicFromExactTopologyState_productSuccess :
    currentWppOpExactAcyclicFromExactTopologyState.productSuccessClaimed = false := rfl

section Checks

#check degreeShortComplexFunctor
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check hasHomology_walkingParallelPairOp_colimitClosure
#check exact_walkingParallelPairOp_colimitClosure
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure
#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_exact_topology
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_exact_topology
#check currentWppOpExactAcyclicFromExactTopologyState
#check currentWppOpExactAcyclicFromExactTopologyState_productSuccess
#check HomologicalComplex.shortComplexFunctor
#check ShortComplex.isColimitOfIsColimitπ
#check MetrizableLCA.strictShortExact_of_exact_of_topology

end Checks

end WppOpExactAcyclicFromExactTopologyW314

end LeanLCAExactChallenge
