import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W398: AddCommGrp forgotten-target cofork-map support.

This standalone audit file isolates the remaining W394 input that cannot be
constructed from W394 alone: the quotient map from the AddCommGrp target row
`L₂` to the forgotten WPP-op colimit point, together with the proof that it is
a cokernel cofork for the same parallel pair `(u - v, 0)`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenTargetCoforkMapV370SupportW398

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/--
The exact forgotten-target cofork-map input needed by W394.

The field `wForgotten` spells the same-parallel-pair condition explicitly:
`qForgotten` coequalizes `(u - v)` and `0`, and `hForgotten` says the resulting
`CokernelCofork.ofπ` is a colimit.
-/
structure ForgottenTargetCoforkMapInputW398
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  qForgotten : L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  wForgotten : (u - v) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

/-- The checked forgotten-target cofork packaged by the W398 input. -/
def ForgottenTargetCoforkMapInputW398.cofork
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : ForgottenTargetCoforkMapInputW398 u v S cs) :
    CokernelCofork (u - v) :=
  CokernelCofork.ofπ I.qForgotten I.wForgotten

/-- The W398 cofork is a colimit over the explicit parallel pair `(u - v, 0)`. -/
def ForgottenTargetCoforkMapInputW398.isColimit_cofork
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : ForgottenTargetCoforkMapInputW398 u v S cs) :
    IsColimit I.cofork :=
  I.hForgotten

/-- W394-shaped canonical-side input, separated from W398's forgotten map. -/
structure ForgottenTargetCanonicalCoforkInputW398
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (canonicalTarget : ShortComplex AddCommGrpCat.{0})
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hcs : IsColimit cs
  qCanonical : L₂ ⟶ canonicalTarget
  wCanonical : (u - v) ≫ qCanonical = 0 := by cat_disch
  hCanonical : IsColimit (CokernelCofork.ofπ qCanonical wCanonical)

/--
Local mirror of W394's `ForgottenTargetColimitIsoInput`.

The audit blocker files are checked by path rather than imported as Lean
modules, so W398 repeats this small target shape and supplies a checked
field-for-field consumer below.
-/
structure ForgottenTargetColimitIsoInputW394Shape
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (canonicalTarget : ShortComplex AddCommGrpCat.{0})
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hcs : IsColimit cs
  qCanonical : L₂ ⟶ canonicalTarget
  wCanonical : (u - v) ≫ qCanonical = 0 := by cat_disch
  hCanonical : IsColimit (CokernelCofork.ofπ qCanonical wCanonical)
  qForgotten : L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  wForgotten : (u - v) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

/--
Consumer into W394's input shape: W398 supplies exactly the missing forgotten
cofork map and same-parallel-pair colimit proof.
-/
def ForgottenTargetCoforkMapInputW398.toW394ColimitIsoInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398 u v canonicalTarget S cs)
    (forgotten : ForgottenTargetCoforkMapInputW398 u v S cs) :
    ForgottenTargetColimitIsoInputW394Shape u v canonicalTarget S cs where
  hcs := canonical.hcs
  qCanonical := canonical.qCanonical
  wCanonical := canonical.wCanonical
  hCanonical := canonical.hCanonical
  qForgotten := forgotten.qForgotten
  wForgotten := forgotten.wForgotten
  hForgotten := forgotten.hForgotten

@[simp]
theorem ForgottenTargetCoforkMapInputW398.toW394_qForgotten
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398 u v canonicalTarget S cs)
    (forgotten : ForgottenTargetCoforkMapInputW398 u v S cs) :
    (forgotten.toW394ColimitIsoInput canonical).qForgotten = forgotten.qForgotten :=
  rfl

@[simp]
theorem ForgottenTargetCoforkMapInputW398.toW394_hForgotten
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398 u v canonicalTarget S cs)
    (forgotten : ForgottenTargetCoforkMapInputW398 u v S cs) :
    (forgotten.toW394ColimitIsoInput canonical).hForgotten = forgotten.hForgotten :=
  rfl

/-- W398 checked support state. -/
structure AddCommGrpForgottenTargetCoforkMapV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  forgottenTargetCoforkMapResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenTargetCoforkMapV370SupportState :
    AddCommGrpForgottenTargetCoforkMapV370SupportState where
  seed := "f009172ba2b3475a"
  checkedConstructors :=
    ["ForgottenTargetCoforkMapInputW398",
      "ForgottenTargetCoforkMapInputW398.cofork",
      "ForgottenTargetCoforkMapInputW398.isColimit_cofork",
      "ForgottenTargetCanonicalCoforkInputW398",
      "ForgottenTargetColimitIsoInputW394Shape",
      "ForgottenTargetCoforkMapInputW398.toW394ColimitIsoInput",
      "ForgottenTargetCoforkMapInputW398.toW394_qForgotten",
      "ForgottenTargetCoforkMapInputW398.toW394_hForgotten"]
  forgottenTargetCoforkMapResult := "partial"
  remainingInputs :=
    ["instantiate qForgotten from the concrete forgotten WPP-op colimit cocone leg",
      "prove that qForgotten is colimit for the same cokernel cofork over (u - v, 0)"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenTargetCoforkMapV370SupportState_productSuccess :
    currentAddCommGrpForgottenTargetCoforkMapV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check ForgottenTargetCoforkMapInputW398
#check ForgottenTargetCoforkMapInputW398.qForgotten
#check ForgottenTargetCoforkMapInputW398.wForgotten
#check ForgottenTargetCoforkMapInputW398.hForgotten
#check ForgottenTargetCoforkMapInputW398.cofork
#check ForgottenTargetCoforkMapInputW398.isColimit_cofork
#check ForgottenTargetCanonicalCoforkInputW398
#check ForgottenTargetColimitIsoInputW394Shape
#check ForgottenTargetCoforkMapInputW398.toW394ColimitIsoInput
#check currentAddCommGrpForgottenTargetCoforkMapV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenTargetCoforkMapV370SupportW398

end LeanLCAExactChallenge
