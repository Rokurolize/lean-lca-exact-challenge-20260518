import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W334: closed-range boundary for forgetting a topological cokernel to
`AddCommGrpCat`.

W331 reduced the AddCommGrp cokernel comparison to the input that every
algebraic additive target map killing `f` also kills the closed subgroup
`MetrizableLCA.cokernelSubgroup f`.  This file records the checked
closed-range sufficient condition: if the algebraic range is already closed
inside `B`, equivalently if the local cokernel subgroup equals the algebraic
range, then that missing input is available and W331's forgotten cofork is an
`AddCommGrpCat` cokernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpCokernelClosedRangeSupportW334

/-- The forgetful functor under comparison. -/
abbrev FgtCat : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

variable {A B : MetrizableLCA.{0}} (f : A ⟶ B)

/-- The algebraic subgroup used by `AddCommGrpCat.cokernelIsoQuotient`. -/
abbrev algebraicRange : AddSubgroup B :=
  AddSubgroup.map f.hom.toAddMonoidHom ⊤

/-- The range term that appears in the algebraic cokernel quotient. -/
abbrev addCommGrpCokernelRange : AddSubgroup B :=
  AddMonoidHom.range (FgtCat.map f).hom

/-- The local topological cokernel subgroup is the closure of the algebraic range. -/
theorem cokernelSubgroup_eq_algebraicRange_closure :
    MetrizableLCA.cokernelSubgroup f = (algebraicRange f).topologicalClosure := by
  rfl

/-- The algebraic range is contained in the closed subgroup used by the topological cokernel. -/
theorem algebraicRange_le_cokernelSubgroup :
    algebraicRange f ≤ MetrizableLCA.cokernelSubgroup f := by
  intro b hb
  rw [cokernelSubgroup_eq_algebraicRange_closure f]
  exact AddSubgroup.le_topologicalClosure _ hb

/-- The cofork obtained by forgetting the local `MetrizableLCA` cokernel cofork. -/
def forgottenCokernelCofork : CokernelCofork (FgtCat.map f) :=
  CokernelCofork.ofπ
    (FgtCat.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)

/--
The exact W331 comparison input: algebraic additive maps killing `f` must kill
the closed subgroup used by the topological cokernel.
-/
structure ClosureKernelInput : Prop where
  closure_le_ker_of_comp_zero :
    forall {Z : AddCommGrpCat.{0}} (k : FgtCat.obj B ⟶ Z),
      FgtCat.map f ≫ k = 0 ->
        MetrizableLCA.cokernelSubgroup f ≤ k.hom.ker

/--
Closed-range sufficient condition in subgroup form.

If the topological closure of the algebraic range is contained in the algebraic
range, then every algebraic map killing `f` kills the closed cokernel subgroup.
-/
theorem closureKernelInput_of_algebraicRange_topologicalClosure_le
    (hclosed : (algebraicRange f).topologicalClosure ≤ algebraicRange f) :
    ClosureKernelInput f where
  closure_le_ker_of_comp_zero := by
    intro Z k hk b hb
    rw [cokernelSubgroup_eq_algebraicRange_closure f] at hb
    have hb_alg : b ∈ algebraicRange f := hclosed hb
    rcases hb_alg with ⟨a, _ha, rfl⟩
    change k.hom (f a) = 0
    have hk_apply := congrArg (fun q : FgtCat.obj A ⟶ Z => q a) hk
    simpa using hk_apply

/-- Closed-range sufficient condition as equality with its topological closure. -/
theorem closureKernelInput_of_algebraicRange_topologicalClosure_eq
    (hclosed : (algebraicRange f).topologicalClosure = algebraicRange f) :
    ClosureKernelInput f :=
  closureKernelInput_of_algebraicRange_topologicalClosure_le f (by
    intro b hb
    rwa [hclosed] at hb)

/-- Closed-range sufficient condition as equality of the local subgroup with the algebraic range. -/
theorem closureKernelInput_of_cokernelSubgroup_eq_algebraicRange
    (hclosed : MetrizableLCA.cokernelSubgroup f = algebraicRange f) :
    ClosureKernelInput f :=
  closureKernelInput_of_algebraicRange_topologicalClosure_eq f (by
    rwa [← cokernelSubgroup_eq_algebraicRange_closure f])

/--
Checked reduction carried forward from W331: once `ClosureKernelInput` is
known, the forgotten local cokernel cofork has the algebraic cokernel universal
property.
-/
def forgottenCokernelCofork_isColimit_of_closureKernelInput
    (h : ClosureKernelInput f) :
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
          (h.closure_le_ker_of_comp_zero k hk)))
    (fun {Z} k hk => by
      ext b
      rfl)
    (fun {Z} k hk m hm => by
      ext q
      refine QuotientAddGroup.induction_on q ?_
      intro b
      have hm_apply := congrArg (fun g : FgtCat.obj B ⟶ Z => g b) hm
      simpa using hm_apply)

/-- Closed-range quotient comparison: the forgotten cofork is an `AddCommGrpCat` cokernel. -/
def forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_le
    (hclosed : (algebraicRange f).topologicalClosure ≤ algebraicRange f) :
    IsColimit (forgottenCokernelCofork f) :=
  forgottenCokernelCofork_isColimit_of_closureKernelInput f
    (closureKernelInput_of_algebraicRange_topologicalClosure_le f hclosed)

/-- Equality variant of the closed-range quotient comparison. -/
def forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_eq
    (hclosed : (algebraicRange f).topologicalClosure = algebraicRange f) :
    IsColimit (forgottenCokernelCofork f) :=
  forgottenCokernelCofork_isColimit_of_closureKernelInput f
    (closureKernelInput_of_algebraicRange_topologicalClosure_eq f hclosed)

/-- Local-subgroup equality variant of the closed-range quotient comparison. -/
def forgottenCokernelCofork_isColimit_of_cokernelSubgroup_eq_algebraicRange
    (hclosed : MetrizableLCA.cokernelSubgroup f = algebraicRange f) :
    IsColimit (forgottenCokernelCofork f) :=
  forgottenCokernelCofork_isColimit_of_closureKernelInput f
    (closureKernelInput_of_cokernelSubgroup_eq_algebraicRange f hclosed)

/-- Declaration-level survey for the checked W334 boundary. -/
def closedRangeRouteSurvey : List String :=
  ["AddSubgroup.le_topologicalClosure gives algebraicRange f <= MetrizableLCA.cokernelSubgroup f",
    "MetrizableLCA.cokernelSubgroup f is definitionally (algebraicRange f).topologicalClosure",
    "closed-range input (algebraicRange f).topologicalClosure <= algebraicRange f gives ClosureKernelInput f",
    "ClosureKernelInput f gives IsColimit (forgottenCokernelCofork f)",
    "there is still no arbitrary-f preservation claim without such a closed-range or closure-kernel input"]

theorem closedRangeRouteSurvey_count :
    closedRangeRouteSurvey.length = 5 := rfl

/-- Machine-readable W334 support state. -/
structure AddCommGrpCokernelClosedRangeSupportState : Type where
  seed : String
  checkedTheorems : List String
  closedRangeInputs : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

/-- Reproducible W334 state for parent review. -/
def currentAddCommGrpCokernelClosedRangeSupportState :
    AddCommGrpCokernelClosedRangeSupportState where
  seed := "w334-20260520T195341Z-49c0a6741e889b3b3d816f13"
  checkedTheorems :=
    ["cokernelSubgroup_eq_algebraicRange_closure",
      "algebraicRange_le_cokernelSubgroup",
      "closureKernelInput_of_algebraicRange_topologicalClosure_le",
      "closureKernelInput_of_algebraicRange_topologicalClosure_eq",
      "closureKernelInput_of_cokernelSubgroup_eq_algebraicRange",
      "forgottenCokernelCofork_isColimit_of_closureKernelInput",
      "forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_le",
      "forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_eq",
      "forgottenCokernelCofork_isColimit_of_cokernelSubgroup_eq_algebraicRange",
      "closedRangeRouteSurvey_count"]
  closedRangeInputs :=
    ["(algebraicRange f).topologicalClosure <= algebraicRange f",
      "(algebraicRange f).topologicalClosure = algebraicRange f",
      "MetrizableLCA.cokernelSubgroup f = algebraicRange f"]
  remainingInputs :=
    ["for arbitrary f, provide one closed-range hypothesis above or provide ClosureKernelInput f directly",
      "only after that can W328's ZeroPairCokernelPreservationInput be supplied for the given morphism",
      "this file does not claim preservation for every morphism"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelClosedRangeSupportState_productSuccess :
    currentAddCommGrpCokernelClosedRangeSupportState.productSuccessClaimed = false := rfl

section Checks

#check FgtCat
#check algebraicRange
#check addCommGrpCokernelRange
#check cokernelSubgroup_eq_algebraicRange_closure
#check algebraicRange_le_cokernelSubgroup
#check forgottenCokernelCofork
#check ClosureKernelInput
#check closureKernelInput_of_algebraicRange_topologicalClosure_le
#check closureKernelInput_of_algebraicRange_topologicalClosure_eq
#check closureKernelInput_of_cokernelSubgroup_eq_algebraicRange
#check forgottenCokernelCofork_isColimit_of_closureKernelInput
#check forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_le
#check forgottenCokernelCofork_isColimit_of_algebraicRange_topologicalClosure_eq
#check forgottenCokernelCofork_isColimit_of_cokernelSubgroup_eq_algebraicRange
#check closedRangeRouteSurvey
#check closedRangeRouteSurvey_count
#check currentAddCommGrpCokernelClosedRangeSupportState
#check currentAddCommGrpCokernelClosedRangeSupportState_productSuccess
#check MetrizableLCA.cokernelIsColimit
#check MetrizableLCA.cokernelπ
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.comp_cokernelπ
#check AddCommGrpCat.cokernelIsoQuotient
#check CokernelCofork.IsColimit.ofπ
#check CokernelCofork.IsColimit.desc'
#check AddSubgroup.le_topologicalClosure
#check QuotientAddGroup.lift
#check QuotientAddGroup.eq_zero_iff

end Checks

end AddCommGrpCokernelClosedRangeSupportW334

end LeanLCAExactChallenge
