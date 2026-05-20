import LeanLCAExactChallenge.LCA.Pushout
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
Finite-colimit packaging boundary for `MetrizableLCA`.

This file records a compiling local route from the existing finite biproduct data to
`HasFiniteColimits MetrizableLCA`, conditional on the remaining colimit constructor.
The current explicit pushout API only gives pushouts for spans whose left leg is the
first map of a strict short exact complex and whose relation subgroup is closed.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace MetrizableLCAFiniteColimitsW235

/--
The existing zero object and binary biproducts already package finite coproducts for
`MetrizableLCA`.
-/
theorem metrizableLCA_hasFiniteCoproducts :
    HasFiniteCoproducts MetrizableLCA.{u} := by
  haveI : HasInitial MetrizableLCA.{u} := inferInstance
  haveI : HasBinaryCoproducts MetrizableLCA.{u} := inferInstance
  exact hasFiniteCoproducts_of_has_binary_and_initial

/--
If arbitrary pushouts are supplied, mathlib's standard constructor packages finite
colimits for `MetrizableLCA`.
-/
theorem metrizableLCA_hasFiniteColimits_of_hasPushouts
    [HasPushouts MetrizableLCA.{u}] :
    HasFiniteColimits MetrizableLCA.{u} := by
  haveI : HasInitial MetrizableLCA.{u} := inferInstance
  exact hasFiniteColimits_of_hasInitial_and_pushouts

/--
Equivalently in this preadditive category, a `HasCokernels` instance supplies
coequalizers, and finite coproducts then package finite colimits.
-/
theorem metrizableLCA_hasFiniteColimits_of_hasCokernels
    [HasCokernels MetrizableLCA.{u}] :
    HasFiniteColimits MetrizableLCA.{u} := by
  haveI : HasFiniteCoproducts MetrizableLCA.{u} :=
    metrizableLCA_hasFiniteCoproducts
  haveI : HasCoequalizers MetrizableLCA.{u} :=
    Preadditive.hasCoequalizers_of_hasCokernels
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- Minimal remaining constructor for the pushout route. -/
structure PushoutRouteInput : Prop where
  hasPushouts : HasPushouts MetrizableLCA.{u}

/-- Minimal remaining constructor for the cokernel/coequalizer route. -/
structure CokernelRouteInput : Prop where
  hasCokernels : HasCokernels MetrizableLCA.{u}

/-- Wrapped pushout route, for downstream consumers that carry the input as data. -/
theorem pushoutRouteInput_hasFiniteColimits (h : PushoutRouteInput.{u}) :
    HasFiniteColimits MetrizableLCA.{u} := by
  haveI : HasPushouts MetrizableLCA.{u} := h.hasPushouts
  exact metrizableLCA_hasFiniteColimits_of_hasPushouts

/-- Wrapped cokernel route, for downstream consumers that carry the input as data. -/
theorem cokernelRouteInput_hasFiniteColimits (h : CokernelRouteInput.{u}) :
    HasFiniteColimits MetrizableLCA.{u} := by
  haveI : HasCokernels MetrizableLCA.{u} := h.hasCokernels
  exact metrizableLCA_hasFiniteColimits_of_hasCokernels

/--
The exact existing pushout constructor is restricted: it constructs `HasPushout S.f a`
only after closedness of the explicit relation subgroup is known.
-/
def existingRestrictedPushoutConstructorSignature : String :=
  "MetrizableLCA.hasPushout_of_pushoutSubgroup_closed {S} {Y} (a : S.X1 ⟶ Y) " ++
    "(hN : IsClosed (MetrizableLCA.pushoutSubgroup a : Set (S.X2 × Y))) : HasPushout S.f a"

/-- The topological lemma currently producing the closedness hypothesis from strictness. -/
def existingPushoutClosednessSignature : String :=
  "MetrizableLCA.pushoutSubgroup_closed (hS : strictShortExact S) (a : S.X1 ⟶ Y) : " ++
    "IsClosed (MetrizableLCA.pushoutSubgroup a : Set (S.X2 × Y))"

/-- Exact remaining constructor signatures that would close `HasFiniteColimits MetrizableLCA`. -/
def missingFiniteColimitConstructors : List String :=
  ["HasPushouts MetrizableLCA",
    "HasCokernels MetrizableLCA",
    "HasCoequalizers MetrizableLCA"]

theorem missingFiniteColimitConstructors_count :
    missingFiniteColimitConstructors.length = 3 := rfl

/-- Reproducible audit state for this worker. -/
structure AuditState : Type where
  route : Nat
  finiteCoproductsPackaged : Bool
  pushoutRouteConstructor : String
  cokernelRouteConstructor : String
  restrictedExistingPushout : String
  productSuccessClaimed : Bool

/-- Route selected from the SSoT seed for this worker. -/
def currentAuditState : AuditState where
  route := 3
  finiteCoproductsPackaged := true
  pushoutRouteConstructor := "metrizableLCA_hasFiniteColimits_of_hasPushouts"
  cokernelRouteConstructor := "metrizableLCA_hasFiniteColimits_of_hasCokernels"
  restrictedExistingPushout := existingRestrictedPushoutConstructorSignature
  productSuccessClaimed := false

theorem currentAuditState_not_productSuccess :
    currentAuditState.productSuccessClaimed = false := rfl

section Checks

#check MetrizableLCA.instHasFiniteProducts
#check MetrizableLCA.binaryBiproductData
#check MetrizableLCA.pushoutIsColimit
#check MetrizableLCA.hasPushout_of_pushoutSubgroup_closed
#check MetrizableLCA.pushoutSubgroup_closed
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientLift
#check HasPushouts
#check HasCokernels
#check HasCoequalizers
#check Preadditive.hasCoequalizers_of_hasCokernels
#check hasFiniteCoproducts_of_has_binary_and_initial
#check hasFiniteColimits_of_hasInitial_and_pushouts
#check hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
#check metrizableLCA_hasFiniteCoproducts
#check metrizableLCA_hasFiniteColimits_of_hasPushouts
#check metrizableLCA_hasFiniteColimits_of_hasCokernels
#check PushoutRouteInput
#check CokernelRouteInput
#check pushoutRouteInput_hasFiniteColimits
#check cokernelRouteInput_hasFiniteColimits
#check missingFiniteColimitConstructors
#check missingFiniteColimitConstructors_count
#check currentAuditState
#check currentAuditState_not_productSuccess

end Checks

end MetrizableLCAFiniteColimitsW235

end LeanLCAExactChallenge
