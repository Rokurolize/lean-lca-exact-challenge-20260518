import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel

/-!
W339: v362 left LCA coequalizer/colimit transport support.

This file isolates the formal categorical part of the remaining W337 equation.
It does not prove the quotient relation-preimage or closed-map facts.  Instead,
it proves that once the concrete coequalizer/cokernel quotient cocones have the
same leg equations as the abstract WPP-op colimit map, the transported
descended map is definitionally the categorical colimit-induced map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpLeftLcaCoequalizerTransportV362SupportW339

universe v₁ u₁ v₂ u₂

/--
The W337 transport equation follows from leg equations against the concrete
source colimit cocone.  In W337's notation, instantiate `sourceIso` and
`targetIso` as the unique isomorphisms from concrete quotient-presenting
cocones to the arbitrary WPP-op colimit cocones.
-/
theorem coconePointUniqueUpToIso_hom_naturality_of_leg_eq
    {J : Type u₁} [Category.{v₁} J]
    {C : Type u₂} [Category.{v₂} C]
    {X Y : J ⥤ C} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hsource : IsColimit source) (hcx : IsColimit cx)
    (htarget : IsColimit target) (hcy : IsColimit cy)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hφ : ∀ j : J, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j)
    (hdescended : ∀ j : J, source.ι.app j ≫ descended = α.app j ≫ target.ι.app j) :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ =
      descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom := by
  apply hsource.hom_ext
  intro j
  have hsourceLeg :
      source.ι.app j ≫ (IsColimit.coconePointUniqueUpToIso hsource hcx).hom =
        cx.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hsource hcx j
  have htargetLeg :
      target.ι.app j ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
        cy.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom htarget hcy j
  have hleft :
      source.ι.app j ≫
          ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ) =
        α.app j ≫ cy.ι.app j := by
    have hsourceComp :
        source.ι.app j ≫
            ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ) =
          cx.ι.app j ≫ φ := by
      simpa [Category.assoc] using congrArg (fun f => f ≫ φ) hsourceLeg
    exact hsourceComp.trans (hφ j)
  have hright :
      source.ι.app j ≫
          (descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom) =
        α.app j ≫ cy.ι.app j := by
    have hdescComp :
        (source.ι.app j ≫ descended) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
          (α.app j ≫ target.ι.app j) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom :=
      congrArg
        (fun f => f ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom)
        (hdescended j)
    have htargetComp :
        (α.app j ≫ target.ι.app j) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
          α.app j ≫ cy.ι.app j := by
      simpa [Category.assoc] using congrArg (fun f => α.app j ≫ f) htargetLeg
    simpa [Category.assoc] using hdescComp.trans htargetComp
  exact hleft.trans hright.symm

/-- WPP-op specialization of `coconePointUniqueUpToIso_hom_naturality_of_leg_eq`. -/
theorem wppOp_sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom
    {C : Type u₂} [Category.{v₂} C]
    {X Y : WalkingParallelPairᵒᵖ ⥤ C} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hsource : IsColimit source) (hcx : IsColimit cx)
    (htarget : IsColimit target) (hcy : IsColimit cy)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j)
    (hdescended : ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j) :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ =
      descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom :=
  coconePointUniqueUpToIso_hom_naturality_of_leg_eq α hsource hcx htarget hcy
    φ descended hφ hdescended

/--
Machine-readable summary of the W339 contribution.  Product success remains
false because the concrete quotient-presenting cocones and their leg equations
still need to be supplied by the larger LCA coequalizer construction.
-/
structure WppOpLeftLcaCoequalizerTransportV362SupportState : Type where
  seed : String
  selectedRoute : String
  checkedFacts : List String
  transportEquationOrientation : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpLeftLcaCoequalizerTransportV362SupportState :
    WppOpLeftLcaCoequalizerTransportV362SupportState where
  seed := "44e4c59ef83ea05eb1160968ab684e2f"
  selectedRoute := "generic-colimit-leg-transport"
  checkedFacts :=
    ["coconePointUniqueUpToIso_hom_naturality_of_leg_eq",
      "wppOp_sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom"]
  transportEquationOrientation :=
    "sourceIso.hom ≫ φ = descended ≫ targetIso.hom, with sourceIso and targetIso pointing from concrete quotient-presenting cocones to arbitrary colimit cocones"
  remainingInputs :=
    ["construct concrete WPP-op quotient-presenting source and target cocones",
      "prove those concrete cocones are colimit cocones",
      "prove the descended quotient map satisfies source.ι.app j ≫ descended = α.app j ≫ target.ι.app j for every WalkingParallelPairᵒᵖ leg"]
  productSuccessClaimed := false

theorem currentWppOpLeftLcaCoequalizerTransportV362SupportState_productSuccess :
    currentWppOpLeftLcaCoequalizerTransportV362SupportState.productSuccessClaimed = false := rfl

def w339SupportDeclarationNames : List String :=
  ["coconePointUniqueUpToIso_hom_naturality_of_leg_eq",
    "wppOp_sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom",
    "WppOpLeftLcaCoequalizerTransportV362SupportState",
    "currentWppOpLeftLcaCoequalizerTransportV362SupportState",
    "currentWppOpLeftLcaCoequalizerTransportV362SupportState_productSuccess"]

theorem w339SupportDeclarationNames_count :
    w339SupportDeclarationNames.length = 5 := rfl

section Checks

#check coconePointUniqueUpToIso_hom_naturality_of_leg_eq
#check wppOp_sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom
#check IsColimit.coconePointUniqueUpToIso
#check IsColimit.comp_coconePointUniqueUpToIso_hom
#check IsColimit.hom_ext
#check currentWppOpLeftLcaCoequalizerTransportV362SupportState
#check currentWppOpLeftLcaCoequalizerTransportV362SupportState_productSuccess
#check w339SupportDeclarationNames
#check w339SupportDeclarationNames_count

end Checks

end WppOpLeftLcaCoequalizerTransportV362SupportW339

end LeanLCAExactChallenge
