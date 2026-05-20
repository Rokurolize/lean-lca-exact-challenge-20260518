import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W394: AddCommGrp forgotten-target colimit-uniqueness iso support.

This standalone audit file isolates the checked colimit-uniqueness route for
the W391 remaining `targetIso`: once the canonical AddCommGrp cokernel row and
the forgotten WPP-op target row are presented as cokernel coforks over the same
parallel pair, `IsColimit.coconePointUniqueUpToIso` gives the required
isomorphism of short-complex targets.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenTargetColimitIsoV370SupportW394

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

universe u v

/-- The general checked cokernel-cofork uniqueness isomorphism. -/
def cokernelCoforkPointUniqueIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y P Q : C} {f : X ⟶ Y}
    {πP : Y ⟶ P} {wP : f ≫ πP = 0}
    {πQ : Y ⟶ Q} {wQ : f ≫ πQ = 0}
    (hP : IsColimit (CokernelCofork.ofπ πP wP))
    (hQ : IsColimit (CokernelCofork.ofπ πQ wQ)) :
    P ≅ Q :=
  hP.coconePointUniqueUpToIso hQ

@[simp]
theorem cokernelCoforkPointUniqueIso_hom_π
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y P Q : C} {f : X ⟶ Y}
    {πP : Y ⟶ P} {wP : f ≫ πP = 0}
    {πQ : Y ⟶ Q} {wQ : f ≫ πQ = 0}
    (hP : IsColimit (CokernelCofork.ofπ πP wP))
    (hQ : IsColimit (CokernelCofork.ofπ πQ wQ)) :
    πP ≫ (cokernelCoforkPointUniqueIso hP hQ).hom = πQ := by
  simpa [cokernelCoforkPointUniqueIso, CokernelCofork.π_ofπ] using
    (hP.comp_coconePointUniqueUpToIso_hom hQ WalkingParallelPair.one)

@[simp]
theorem cokernelCoforkPointUniqueIso_inv_π
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {X Y P Q : C} {f : X ⟶ Y}
    {πP : Y ⟶ P} {wP : f ≫ πP = 0}
    {πQ : Y ⟶ Q} {wQ : f ≫ πQ = 0}
    (hP : IsColimit (CokernelCofork.ofπ πP wP))
    (hQ : IsColimit (CokernelCofork.ofπ πQ wQ)) :
    πQ ≫ (cokernelCoforkPointUniqueIso hP hQ).inv = πP := by
  simpa [cokernelCoforkPointUniqueIso, CokernelCofork.π_ofπ] using
    (hP.comp_coconePointUniqueUpToIso_inv hQ WalkingParallelPair.one)

/--
W394 input for the forgotten-target `targetIso` construction.

The `canonicalTarget` is intended to be W391's
`W379Source.canonicalCokernelShortComplex u v`.  The `forgotten` target is the
point of the WPP-op colimit cocone after applying `forget₂`.
-/
structure ForgottenTargetColimitIsoInput
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

/-- The colimit-uniqueness `targetIso` supplied by the W394 input. -/
def ForgottenTargetColimitIsoInput.targetIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (I : ForgottenTargetColimitIsoInput u v canonicalTarget S cs) :
    canonicalTarget ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  cokernelCoforkPointUniqueIso I.hCanonical I.hForgotten

@[simp]
theorem ForgottenTargetColimitIsoInput.qCanonical_targetIso_hom
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (I : ForgottenTargetColimitIsoInput u v canonicalTarget S cs) :
    I.qCanonical ≫ I.targetIso.hom = I.qForgotten :=
  cokernelCoforkPointUniqueIso_hom_π I.hCanonical I.hForgotten

@[simp]
theorem ForgottenTargetColimitIsoInput.qForgotten_targetIso_inv
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (I : ForgottenTargetColimitIsoInput u v canonicalTarget S cs) :
    I.qForgotten ≫ I.targetIso.inv = I.qCanonical :=
  cokernelCoforkPointUniqueIso_inv_π I.hCanonical I.hForgotten

/--
Signature-compatible mirror of W391's remaining iso package.  Instantiating
`canonicalTarget` with W391's canonical AddCommGrp cokernel row gives the exact
field type required by `ForgottenTargetIsoConstructionInputW391.targetIso`.
-/
structure W391CompatibleTargetIsoInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (canonicalTarget : ShortComplex AddCommGrpCat.{0})
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  targetIso :
    canonicalTarget ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/-- Consumer from the checked colimit-uniqueness package to the W391-shaped input. -/
def ForgottenTargetColimitIsoInput.toW391CompatibleTargetIsoInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (I : ForgottenTargetColimitIsoInput u v canonicalTarget S cs) :
    W391CompatibleTargetIsoInput u v canonicalTarget S cs where
  targetIso := I.targetIso

/-- W394 checked support state. -/
structure AddCommGrpForgottenTargetColimitIsoV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  forgottenTargetColimitIsoResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenTargetColimitIsoV370SupportState :
    AddCommGrpForgottenTargetColimitIsoV370SupportState where
  seed := "12074a18ac9118ac"
  checkedConstructors :=
    ["IsColimit.coconePointUniqueUpToIso",
      "IsColimit.comp_coconePointUniqueUpToIso_hom",
      "IsColimit.comp_coconePointUniqueUpToIso_inv",
      "cokernelCoforkPointUniqueIso",
      "cokernelCoforkPointUniqueIso_hom_π",
      "cokernelCoforkPointUniqueIso_inv_π",
      "ForgottenTargetColimitIsoInput",
      "ForgottenTargetColimitIsoInput.targetIso",
      "ForgottenTargetColimitIsoInput.qCanonical_targetIso_hom",
      "ForgottenTargetColimitIsoInput.qForgotten_targetIso_inv",
      "W391CompatibleTargetIsoInput",
      "ForgottenTargetColimitIsoInput.toW391CompatibleTargetIsoInput"]
  forgottenTargetColimitIsoResult := "proved"
  remainingInputs :=
    ["instantiate canonicalTarget with W391's W379Source.canonicalCokernelShortComplex u v",
      "provide the forgotten target cofork map qForgotten and its IsColimit proof over the same parallel pair (u - v, 0)"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenTargetColimitIsoV370SupportState_productSuccess :
    currentAddCommGrpForgottenTargetColimitIsoV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check IsColimit.coconePointUniqueUpToIso
#check IsColimit.comp_coconePointUniqueUpToIso_hom
#check IsColimit.comp_coconePointUniqueUpToIso_inv
#check cokernelCoforkPointUniqueIso
#check cokernelCoforkPointUniqueIso_hom_π
#check cokernelCoforkPointUniqueIso_inv_π
#check ForgottenTargetColimitIsoInput
#check ForgottenTargetColimitIsoInput.targetIso
#check ForgottenTargetColimitIsoInput.qCanonical_targetIso_hom
#check ForgottenTargetColimitIsoInput.qForgotten_targetIso_inv
#check W391CompatibleTargetIsoInput
#check W391CompatibleTargetIsoInput.targetIso
#check ForgottenTargetColimitIsoInput.toW391CompatibleTargetIsoInput
#check currentAddCommGrpForgottenTargetColimitIsoV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenTargetColimitIsoV370SupportW394

end LeanLCAExactChallenge
