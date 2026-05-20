import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
W428: reduce underlying forgetful WPP-op preservation to finite-colimit
preservation.

W424 exposed the exact missing shape-level instance
`PreservesColimitsOfShape WalkingParallelPairᵒᵖ (forget₂ MetrizableLCA AddCommGrpCat)`.
This file checks that mathlib's finite-colimit preservation class is already
strong enough to supply that instance, because `WalkingParallelPairᵒᵖ` is a
finite category.  The remaining input is therefore an actual
`PreservesFiniteColimits` (or stronger `PreservesColimitsOfSize`) instance for
the underlying forgetful functor.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

namespace AddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportW428

/-- The underlying forgetful functor whose WPP-op colimit preservation is needed. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- `WalkingParallelPairᵒᵖ` is in the finite-shape class consumed below. -/
@[reducible]
def walkingParallelPairOp_finCategory : FinCategory WalkingParallelPairᵒᵖ :=
  inferInstance

/--
The requested WPP-op shape preservation follows immediately from finite-colimit
preservation of the underlying forgetful functor.
-/
theorem underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
    [PreservesFiniteColimits underlyingForgetfulFunctor] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor :=
  inferInstance

/--
A stronger all-small-colimit preservation instance would also supply the same
WPP-op shape preservation, via mathlib's reduction to finite colimits.
-/
theorem underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesColimitsOfSize
    [PreservesColimitsOfSize.{0, 0} underlyingForgetfulFunctor] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctor := by
  haveI : PreservesFiniteColimits underlyingForgetfulFunctor :=
    PreservesColimitsOfSize.preservesFiniteColimits underlyingForgetfulFunctor
  exact
    underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits

/--
The finite-colimit reduction gives the one-diagram preservation consumed by
mapped-cocone APIs.
-/
theorem underlyingForgetfulPreservesWppOpColimit_of_preservesFiniteColimits
    (K : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    [PreservesFiniteColimits underlyingForgetfulFunctor] :
    PreservesColimit K underlyingForgetfulFunctor :=
  inferInstance

/--
Once finite-colimit preservation is supplied, a WPP-op colimit cocone in
`MetrizableLCA` maps to a colimit cocone in `AddCommGrpCat`.
-/
def underlyingForgetfulMappedCoconeIsColimit_of_preservesFiniteColimits
    (K : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (c : Cocone K)
    [PreservesFiniteColimits underlyingForgetfulFunctor]
    (hc : IsColimit c) :
    IsColimit (underlyingForgetfulFunctor.mapCocone c) :=
  (PreservesColimit.preserves (F := underlyingForgetfulFunctor) hc).some

/-- W428 checked support state. -/
structure AddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  underlyingForgetfulPreservationFromFiniteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState :
    AddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState where
  seed := "ceICC4asEHYN2g6OhBgd1fRf"
  checkedConstructors :=
    ["walkingParallelPairOp_finCategory",
      "underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits",
      "underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesColimitsOfSize",
      "underlyingForgetfulPreservesWppOpColimit_of_preservesFiniteColimits",
      "underlyingForgetfulMappedCoconeIsColimit_of_preservesFiniteColimits"]
  underlyingForgetfulPreservationFromFiniteResult := "partial"
  remainingInputs :=
    ["missing checked instance/API: `[PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)]`",
      "alternative sufficient input: `[PreservesColimitsOfSize.{0, 0} (forget₂ MetrizableLCA AddCommGrpCat)]`",
      "`#check (inferInstance : PreservesFiniteColimits underlyingForgetfulFunctor)` fails from the local imports"]
  productSuccessClaimed := false

theorem currentAddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState_productSuccess :
    currentAddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check walkingParallelPairOp_finCategory
#check underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesFiniteColimits
#check underlyingForgetfulPreservesWppOpColimitsOfShape_of_preservesColimitsOfSize
#check underlyingForgetfulPreservesWppOpColimit_of_preservesFiniteColimits
#check underlyingForgetfulMappedCoconeIsColimit_of_preservesFiniteColimits
#check currentAddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportState_productSuccess

end Checks

end AddCommGrpUnderlyingForgetfulWppOpPreservationFromFiniteV370SupportW428

end LeanLCAExactChallenge
