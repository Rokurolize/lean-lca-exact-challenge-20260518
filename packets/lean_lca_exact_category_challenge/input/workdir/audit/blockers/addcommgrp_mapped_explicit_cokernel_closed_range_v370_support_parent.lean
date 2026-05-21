import LeanLCAExactChallenge.LCA.StrictExact
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
Parent support: closed-range comparison for W433's mapped explicit cokernel
cocone.

This standalone audit file repeats the small W429/W433 definitions it needs.
The point checked here is that the set-level closed-range cokernel comparison
also proves W433's `mappedExplicitCokernelCocone f` colimiting statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpMappedExplicitCokernelClosedRangeV370SupportParent

variable {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)

/-- The forgetful functor under comparison. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The algebraic range of a local LCA morphism. -/
abbrev algebraicRange : AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom ⊤

/-- Set-level closed range gives the closure comparison for the local cokernel subgroup. -/
theorem algebraicRange_topologicalClosure_le_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    (algebraicRange f).topologicalClosure ≤ algebraicRange f := by
  have hclosedAlg : IsClosed ((algebraicRange f : AddSubgroup Y) : Set Y) := by
    simpa [algebraicRange, MetrizableLCA.rangeSubgroup_coe f] using hclosed
  apply AddSubgroup.topologicalClosure_minimal
  · intro y hy
    exact hy
  · exact hclosedAlg

/-- Closed range makes every algebraic map killing `f` kill the local closed cokernel subgroup. -/
theorem cokernelSubgroup_le_ker_of_comp_zero_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : X → Y)))
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    MetrizableLCA.cokernelSubgroup f ≤ k.hom.ker := by
  intro y hy
  have hy_alg : y ∈ algebraicRange f :=
    algebraicRange_topologicalClosure_le_of_isClosed_range f hclosed (by
      simpa [MetrizableLCA.cokernelSubgroup, algebraicRange] using hy)
  rcases hy_alg with ⟨x, _hx, rfl⟩
  change k.hom (f x) = 0
  have hk_apply := congrArg (fun q : underlyingForgetfulFunctor.obj X ⟶ Z => q x) hk
  simpa using hk_apply

/-- The explicit local cokernel cofork, before forgetting topology. -/
def explicitMetrizableCokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (MetrizableLCA.cokernelπ f) (MetrizableLCA.comp_cokernelπ f)

/--
The mapped concrete cokernel cocone.  Its vertex is the underlying abelian group
of the quotient of `Y` by the topological closure of the range of `f`.
-/
def mappedExplicitCokernelCocone :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The same forgotten quotient projection as a cokernel cofork for `F.map f`. -/
def forgottenCokernelCofork : CokernelCofork (underlyingForgetfulFunctor.map f) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)

/-- The diagram obtained by forgetting `parallelPair f 0` is the expected algebraic pair. -/
def mappedExplicitDiagramIso :
    parallelPair (underlyingForgetfulFunctor.map f) 0 ≅
      parallelPair f 0 ⋙ underlyingForgetfulFunctor :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- W433's mapped cocone is the reindexed forgotten cokernel cofork. -/
def mappedExplicitCokernelCoconeIsoPrecomposeForgotten :
    mappedExplicitCokernelCocone f ≅
      (Cocone.precompose (mappedExplicitDiagramIso f).inv).obj
        (forgottenCokernelCofork f) :=
  Cocone.ext (Iso.refl _) (fun j => by
    cases j <;>
      simp [mappedExplicitCokernelCocone, explicitMetrizableCokernelCofork,
        forgottenCokernelCofork, mappedExplicitDiagramIso])

/--
Closed range of `f` makes the mapped explicit local cokernel cocone colimiting
in `AddCommGrpCat`.
-/
def mappedExplicitCokernelCocone_isColimit_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (mappedExplicitCokernelCocone f) := by
  let hForgotten : IsColimit (forgottenCokernelCofork f) :=
    CokernelCofork.IsColimit.ofπ
    (underlyingForgetfulFunctor.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)
    (fun {Z} k hk =>
      AddCommGrpCat.ofHom
        (QuotientAddGroup.lift (MetrizableLCA.cokernelSubgroup f) k.hom
          (cokernelSubgroup_le_ker_of_comp_zero_of_isClosed_range f hclosed k hk)))
    (fun {Z} k hk => by
      ext y
      rfl)
    (fun {Z} k hk m hm => by
      ext q
      refine QuotientAddGroup.induction_on q ?_
      intro y
      have hm_apply := congrArg (fun g : underlyingForgetfulFunctor.obj Y ⟶ Z => g y) hm
      simpa using hm_apply)
  let hReindexed :
      IsColimit
        ((Cocone.precompose (mappedExplicitDiagramIso f).inv).obj
          (forgottenCokernelCofork f)) :=
    (IsColimit.precomposeInvEquiv (mappedExplicitDiagramIso f)
      (forgottenCokernelCofork f)).symm hForgotten
  exact IsColimit.ofIsoColimit hReindexed
    (mappedExplicitCokernelCoconeIsoPrecomposeForgotten f).symm

/--
Uniform closed-range input for all morphisms supplies ordinary
`WalkingParallelPair` preservation.
-/
theorem underlyingForgetfulPreservesWalkingParallelPair_of_all_isClosed_range
    (hclosed : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsClosed (Set.range (f : X → Y))) :
    PreservesColimitsOfShape WalkingParallelPair underlyingForgetfulFunctor := by
  haveI :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
    fun f => preservesColimit_of_preserves_colimit_cocone
      (MetrizableLCA.cokernelIsColimit f)
      (mappedExplicitCokernelCocone_isColimit_of_isClosed_range f (hclosed f))
  exact CategoryTheory.Functor.preservesCoequalizers_of_preservesCokernels
    underlyingForgetfulFunctor

/-- The same closed-range input also supplies finite-colimit preservation. -/
theorem underlyingForgetfulPreservesFiniteColimits_of_all_isClosed_range
    (hclosed : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsClosed (Set.range (f : X → Y))) :
    PreservesFiniteColimits underlyingForgetfulFunctor := by
  haveI :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
    fun f => preservesColimit_of_preserves_colimit_cocone
      (MetrizableLCA.cokernelIsColimit f)
      (mappedExplicitCokernelCocone_isColimit_of_isClosed_range f (hclosed f))
  exact CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels
    underlyingForgetfulFunctor

/-- Checked parent state for the W433 closed-range bridge. -/
structure AddCommGrpMappedExplicitCokernelClosedRangeV370SupportState : Type where
  seed : String
  checkedTheorems : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpMappedExplicitCokernelClosedRangeV370SupportState :
    AddCommGrpMappedExplicitCokernelClosedRangeV370SupportState where
  seed := "parent-20260521-mapped-explicit-cokernel-closed-range"
  checkedTheorems :=
    ["mappedExplicitCokernelCocone_isColimit_of_isClosed_range",
      "underlyingForgetfulPreservesWalkingParallelPair_of_all_isClosed_range",
      "underlyingForgetfulPreservesFiniteColimits_of_all_isClosed_range"]
  remainingInputs :=
    ["prove the required closed-range hypothesis for the actual WPP-op difference morphism, or a selected analogue rather than a global all-morphisms claim",
      "transport the objectwise result into the selected short-complex target row",
      "avoid claiming arbitrary all-morphism closed range for MetrizableLCA"]
  productSuccessClaimed := false

theorem currentAddCommGrpMappedExplicitCokernelClosedRangeV370SupportState_productSuccess :
    currentAddCommGrpMappedExplicitCokernelClosedRangeV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check mappedExplicitCokernelCocone_isColimit_of_isClosed_range
#check underlyingForgetfulPreservesWalkingParallelPair_of_all_isClosed_range
#check underlyingForgetfulPreservesFiniteColimits_of_all_isClosed_range
#check currentAddCommGrpMappedExplicitCokernelClosedRangeV370SupportState_productSuccess

end Checks

end AddCommGrpMappedExplicitCokernelClosedRangeV370SupportParent

end LeanLCAExactChallenge
