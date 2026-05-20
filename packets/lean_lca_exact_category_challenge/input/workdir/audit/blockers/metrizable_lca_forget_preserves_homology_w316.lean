import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
W316: isolating the forgetful `PreservesHomology` input in W313/W314.

Mathlib defines `Functor.PreservesHomology` as preservation of kernels and
cokernels, and provides an instance from `PreservesFiniteLimits` plus
`PreservesFiniteColimits`.  This file records the checked consumer for the local
forgetful functor `forget₂ MetrizableLCA AddCommGrpCat`.

This is intentionally nonterminal.  For `MetrizableLCA`, categorical cokernels
are quotients by closed range, whereas the algebraic forgetful target sees
ordinary abelian-group cokernels.  Therefore the finite-colimit-preservation
input is a genuine mathematical obligation and should not be treated as solved
by instance search alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCAForgetPreservesHomologyW316

/-- Local name for the forgetful functor used by the strict-exactness bridge. -/
abbrev forgetLCAAddCommGrp :
    MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The W313/W314 forgetful homology-preservation input. -/
abbrev forgetPreservesHomologyInput : Prop :=
  forgetLCAAddCommGrp.PreservesHomology

/--
Checked consumer: finite-limit and finite-colimit preservation of the forgetful
functor imply the W313/W314 `PreservesHomology` input.
-/
theorem forgetPreservesHomology_of_preservesFiniteLimitsColimits
    [PreservesFiniteLimits forgetLCAAddCommGrp]
    [PreservesFiniteColimits forgetLCAAddCommGrp] :
    forgetPreservesHomologyInput := by
  infer_instance

/-- The split inputs needed to establish the forgetful homology-preservation route. -/
structure ForgetPreservesHomologyInputs : Prop where
  preservesFiniteLimits : PreservesFiniteLimits forgetLCAAddCommGrp
  preservesFiniteColimits : PreservesFiniteColimits forgetLCAAddCommGrp

/-- Package form of the same checked consumer. -/
theorem forgetPreservesHomology_of_inputs
    (h : ForgetPreservesHomologyInputs) :
    forgetPreservesHomologyInput := by
  haveI : PreservesFiniteLimits forgetLCAAddCommGrp := h.preservesFiniteLimits
  haveI : PreservesFiniteColimits forgetLCAAddCommGrp := h.preservesFiniteColimits
  exact forgetPreservesHomology_of_preservesFiniteLimitsColimits

/-- Machine-readable W316 frontier state. -/
structure MetrizableLCAForgetPreservesHomologyState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W316 state for downstream workers. -/
def currentMetrizableLCAForgetPreservesHomologyState :
    MetrizableLCAForgetPreservesHomologyState where
  seed := "w316-parent-20260521T0240Z"
  provedConsumer :=
    "forgetPreservesHomology_of_preservesFiniteLimitsColimits"
  remainingInputs :=
    ["PreservesFiniteLimits (forget₂ MetrizableLCA AddCommGrpCat)",
      "PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)",
      "or replace W313/W314 with a direct algebraic-kernel bridge avoiding global forgetful homology preservation"]
  productSuccessClaimed := false

theorem currentMetrizableLCAForgetPreservesHomologyState_productSuccess :
    currentMetrizableLCAForgetPreservesHomologyState.productSuccessClaimed = false := rfl

section Checks

#check forgetLCAAddCommGrp
#check forgetPreservesHomologyInput
#check forgetPreservesHomology_of_preservesFiniteLimitsColimits
#check ForgetPreservesHomologyInputs
#check forgetPreservesHomology_of_inputs
#check currentMetrizableLCAForgetPreservesHomologyState
#check currentMetrizableLCAForgetPreservesHomologyState_productSuccess
#check Functor.PreservesHomology
#check PreservesFiniteLimits
#check PreservesFiniteColimits

end Checks

end MetrizableLCAForgetPreservesHomologyW316

end LeanLCAExactChallenge
