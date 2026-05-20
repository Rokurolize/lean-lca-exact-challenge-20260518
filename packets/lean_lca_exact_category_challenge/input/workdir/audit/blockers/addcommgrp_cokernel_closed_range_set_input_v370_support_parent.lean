import LeanLCAExactChallenge.LCA.StrictExact
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
Parent support: convert the usual set-level closed-range hypothesis into W334's
algebraic-range closure input.

W334 already proves that a local `MetrizableLCA` cokernel forgets to an
`AddCommGrpCat` cokernel once the algebraic range is closed enough.  This file
records the checked adapter from the more natural hypothesis
`IsClosed (Set.range (f : A -> B))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpCokernelClosedRangeSetInputV370SupportParent

variable {A B : MetrizableLCA.{0}} (f : A ⟶ B)

/-- The forgetful functor under comparison. -/
abbrev FgtCat : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The algebraic subgroup used by the algebraic cokernel quotient. -/
abbrev algebraicRange : AddSubgroup B :=
  AddSubgroup.map f.hom.toAddMonoidHom ⊤

/-- The cofork obtained by forgetting the local `MetrizableLCA` cokernel cofork. -/
def forgottenCokernelCofork : CokernelCofork (FgtCat.map f) :=
  CokernelCofork.ofπ
    (FgtCat.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)

/--
Algebraic additive maps killing `f` must kill the closed subgroup used by the
topological cokernel.
-/
structure ClosureKernelInput : Prop where
  closure_le_ker_of_comp_zero :
    forall {Z : AddCommGrpCat.{0}} (k : FgtCat.obj B ⟶ Z),
      FgtCat.map f ≫ k = 0 ->
        MetrizableLCA.cokernelSubgroup f ≤ k.hom.ker

/--
Set-level closed range is exactly the closedness input needed by W334's
algebraic subgroup route.
-/
theorem algebraicRange_topologicalClosure_le_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : A → B))) :
    (algebraicRange f).topologicalClosure ≤ algebraicRange f := by
  have hclosedAlg : IsClosed ((algebraicRange f : AddSubgroup B) : Set B) := by
    simpa [algebraicRange, MetrizableLCA.rangeSubgroup_coe f] using hclosed
  apply AddSubgroup.topologicalClosure_minimal
  · intro b hb
    exact hb
  · exact hclosedAlg

/-- Set-level closed range supplies the closure-kernel input. -/
theorem closureKernelInput_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : A → B))) :
    ClosureKernelInput f where
  closure_le_ker_of_comp_zero := by
    intro Z k hk b hb
    have hb_alg : b ∈ algebraicRange f :=
      algebraicRange_topologicalClosure_le_of_isClosed_range f hclosed (by
        simpa [MetrizableLCA.cokernelSubgroup, algebraicRange] using hb)
    rcases hb_alg with ⟨a, _ha, rfl⟩
    change k.hom (f a) = 0
    have hk_apply := congrArg (fun q : FgtCat.obj A ⟶ Z => q a) hk
    simpa using hk_apply

/--
If the range of `f` is closed as a subset of the target LCA group, the forgotten
local cokernel cofork is an `AddCommGrpCat` cokernel.
-/
def forgottenCokernelCofork_isColimit_of_isClosed_range
    (hclosed : IsClosed (Set.range (f : A → B))) :
    IsColimit (forgottenCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ
    (FgtCat.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)
    (fun {Z} k hk =>
      AddCommGrpCat.ofHom
        (QuotientAddGroup.lift (MetrizableLCA.cokernelSubgroup f) k.hom
          ((closureKernelInput_of_isClosed_range f hclosed).closure_le_ker_of_comp_zero k hk)))
    (fun {Z} k hk => by
      ext b
      rfl)
    (fun {Z} k hk m hm => by
      ext q
      refine QuotientAddGroup.induction_on q ?_
      intro b
      have hm_apply := congrArg (fun g : FgtCat.obj B ⟶ Z => g b) hm
      simpa using hm_apply)

/-- Checked parent state for the set-level closed-range adapter. -/
structure AddCommGrpCokernelClosedRangeSetInputV370SupportState : Type where
  seed : String
  checkedTheorems : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpCokernelClosedRangeSetInputV370SupportState :
    AddCommGrpCokernelClosedRangeSetInputV370SupportState where
  seed := "parent-20260521-closed-range-set-input"
  checkedTheorems :=
    ["algebraicRange_topologicalClosure_le_of_isClosed_range",
      "closureKernelInput_of_isClosed_range",
      "forgottenCokernelCofork_isColimit_of_isClosed_range"]
  remainingInputs :=
    ["instantiate the closed-range hypothesis for the actual WPP-op difference morphism",
      "transport this objectwise cokernel colimit into the selected short-complex target row"]
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelClosedRangeSetInputV370SupportState_productSuccess :
    currentAddCommGrpCokernelClosedRangeSetInputV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check algebraicRange_topologicalClosure_le_of_isClosed_range
#check closureKernelInput_of_isClosed_range
#check forgottenCokernelCofork_isColimit_of_isClosed_range
#check currentAddCommGrpCokernelClosedRangeSetInputV370SupportState_productSuccess

end Checks

end AddCommGrpCokernelClosedRangeSetInputV370SupportParent

end LeanLCAExactChallenge
