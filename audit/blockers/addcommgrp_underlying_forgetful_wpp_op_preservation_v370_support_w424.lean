import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
W424: underlying forgetful WPP-op preservation frontier.

The requested instance
`PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)`
does not synthesize from the local imports.  This file therefore exposes the
weakest checked reduction: once that shape-level instance is supplied, Lean can
derive the exact per-diagram preservation and mapped-cocone colimit facts needed
by W419/W422.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

namespace AddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportW424

/-- The underlying forgetful functor whose WPP-op colimit preservation is missing. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/--
The exact missing shape-level preservation assumption.  This theorem is
intentionally just `inferInstance`: it records the API name that must be
provided by the main thread or a later support worker.
-/
theorem underlyingForgetfulPreservesWppOpColimitsOfShape
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor :=
  inferInstance

/--
The shape-level assumption gives the one-diagram preservation consumed by the
mapped-cocone API.
-/
theorem underlyingForgetfulPreservesWppOpColimit
    (K : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor] :
    PreservesColimit K underlyingForgetfulFunctor :=
  inferInstance

/--
Given the missing shape-level preservation instance, any WPP-op colimit cocone in
`MetrizableLCA` maps to a colimit cocone in `AddCommGrpCat`.
-/
def underlyingForgetfulMappedCoconeIsColimitOfShapePreserves
    (K : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (c : Cocone K)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor]
    (hc : IsColimit c) :
    IsColimit (underlyingForgetfulFunctor.mapCocone c) :=
  (PreservesColimit.preserves (F := underlyingForgetfulFunctor) hc).some

/-- W424 checked support state. -/
structure AddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  underlyingForgetfulPreservationResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState :
    AddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState where
  seed := "sot-fwgamifwhwf109p2"
  checkedConstructors :=
    ["underlyingForgetfulPreservesWppOpColimitsOfShape",
      "underlyingForgetfulPreservesWppOpColimit",
      "underlyingForgetfulMappedCoconeIsColimitOfShapePreserves"]
  underlyingForgetfulPreservationResult := "blocked"
  remainingInputs :=
    ["missing checked instance/API: `[PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)]`",
      "`#synth PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)` fails from the local imports"]
  productSuccessClaimed := false

theorem currentAddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState_productSuccess :
    currentAddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check underlyingForgetfulPreservesWppOpColimitsOfShape
#check underlyingForgetfulPreservesWppOpColimit
#check underlyingForgetfulMappedCoconeIsColimitOfShapePreserves
#check currentAddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportState_productSuccess

end Checks

end AddCommGrpUnderlyingForgetfulWppOpPreservationV370SupportW424

end LeanLCAExactChallenge
