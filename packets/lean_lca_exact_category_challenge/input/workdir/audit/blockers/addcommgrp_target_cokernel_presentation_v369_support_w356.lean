import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel

/-!
W356: AddCommGrp target cokernel-presentation support for the v369 branch.

This file keeps the W353 abstract cokernel-row bridge pointed at the concrete
WPP-op colimit row: once the colimit short complex, after forgetting to
`AddCommGrpCat`, is isomorphic to a cokernel cofork row for `u - v`, it supplies
the target cokernel presentation used by the difference-Snake input boundary.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpTargetCokernelPresentationV369SupportW356

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/--
Local copy of W350's remaining input package.

The first row is the difference-kernel row, the third row is the
difference-cokernel row, and `cokernelRowIso` identifies that cokernel row with
the target short complex.
-/
structure DifferenceSnakeBoundaryInputs
    (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  differenceKernelRow : ShortComplex AddCommGrpCat.{0}
  differenceMiddleRow : ShortComplex AddCommGrpCat.{0}
  differenceCokernelRow : ShortComplex AddCommGrpCat.{0}
  differenceData :
    ParallelPairDifferenceStrictCokernelData
      differenceKernelRow differenceMiddleRow differenceCokernelRow
  cokernelRowIso : differenceCokernelRow ≅ T

/--
A target row `T` presented as a cokernel row for the difference map `u - v`.
-/
structure TargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hT : IsColimit (CokernelCofork.ofπ qT wT)

/--
A WPP-op colimit row, forgotten to `AddCommGrpCat`, with an identified
cokernel-cofork presentation for the same difference map.
-/
structure WppOpForgottenTargetCokernelCoforkPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) : Type 1 where
  S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}
  cs : Cocone S
  hcs : IsColimit cs
  C : ShortComplex AddCommGrpCat.{0}
  qC : L₂ ⟶ C
  wC : (u - v) ≫ qC = 0 := by cat_disch
  hC : IsColimit (CokernelCofork.ofπ qC wC)
  targetIso :
    C ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
Transport a short-complex cokernel proof across an isomorphism of cokernel rows.
-/
def cokernelCofork_isColimit_comp_iso_hom
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    {d : L₁ ⟶ L₂} {q : L₂ ⟶ L₃} {w : d ≫ q = 0}
    (h : IsColimit (CokernelCofork.ofπ q w)) (e : L₃ ≅ T) :
    IsColimit
      (CokernelCofork.ofπ (q ≫ e.hom)
        (by simpa [Category.assoc] using congrArg (fun k => k ≫ e.hom) w)) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {Z} g hg => e.inv ≫ h.desc
    (CokernelCofork.ofπ g hg)) ?_ ?_
  · intro Z g hg
    simpa [Category.assoc] using (CokernelCofork.IsColimit.desc' h g hg).2
  · intro Z g hg m hm
    have hm' : q ≫ e.hom ≫ m = g := by
      simpa [Category.assoc] using hm
    have hfac : q ≫ h.desc (CokernelCofork.ofπ g hg) = g := by
      simpa [Category.assoc] using (CokernelCofork.IsColimit.desc' h g hg).2
    have huniq : e.hom ≫ m = h.desc (CokernelCofork.ofπ g hg) := by
      refine h.hom_ext ?_
      intro j
      cases j
      · simp [w]
      · simpa [CokernelCofork.π_ofπ] using
          (by rw [hm', hfac] : q ≫ e.hom ≫ m =
            q ≫ h.desc (CokernelCofork.ofπ g hg))
    calc
      m = e.inv ≫ e.hom ≫ m := by simp
      _ = e.inv ≫ h.desc (CokernelCofork.ofπ g hg) := by simp [huniq]

/--
The WPP-op colimit row, if isomorphic to a cokernel cofork row for `u - v`,
is exactly W353's target cokernel-row presentation.
-/
def targetCokernelRowPresentation_of_wppOpForgottenColimitIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (P : WppOpForgottenTargetCokernelCoforkPresentation u v) :
    TargetCokernelRowPresentation u v
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) where
  qT := P.qC ≫ P.targetIso.hom
  wT := by
    simpa [Category.assoc] using congrArg (fun k => k ≫ P.targetIso.hom) P.wC
  hT := cokernelCofork_isColimit_comp_iso_hom P.hC P.targetIso

/--
Two cokernel presentations of the same difference map have canonically
isomorphic cokernel rows.
-/
def cokernelRowIsoOfTargetPresentation
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    {T : ShortComplex AddCommGrpCat.{0}}
    (P : TargetCokernelRowPresentation D.u D.v T) :
    L₃ ≅ T :=
  IsColimit.coconePointUniqueUpToIso D.h₃ P.hT

/--
A strict difference-cokernel row plus a target cokernel presentation for the
same map supplies the W350-style boundary input package.
-/
def differenceSnakeBoundaryInputs_of_targetCokernelRowPresentation
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : TargetCokernelRowPresentation D.u D.v T) :
    DifferenceSnakeBoundaryInputs T where
  differenceKernelRow := L₁
  differenceMiddleRow := L₂
  differenceCokernelRow := L₃
  differenceData := D
  cokernelRowIso := cokernelRowIsoOfTargetPresentation D P

/--
The WPP-op forgotten colimit/cokernel identification supplies the W350-style
boundary input package directly.
-/
def differenceSnakeBoundaryInputs_of_wppOpForgottenColimitIso
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetCokernelCoforkPresentation D.u D.v) :
    DifferenceSnakeBoundaryInputs
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  differenceSnakeBoundaryInputs_of_targetCokernelRowPresentation D
    (targetCokernelRowPresentation_of_wppOpForgottenColimitIso P)

/--
The same bridge stated directly for W318's strict SnakeInput certificate.
-/
def strictSnakeCokernelData_of_wppOpForgottenColimitIso
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetCokernelCoforkPresentation D.u D.v) :
    AddCommGrpStrictSnakeCokernelData
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D
    (cokernelRowIsoOfTargetPresentation D
      (targetCokernelRowPresentation_of_wppOpForgottenColimitIso P))

/--
Consumer theorem: the WPP-op forgotten colimit/cokernel identification is enough
to recover the target AddCommGrp kernel exactness expected downstream.
-/
theorem addCommGrpKernelExact_of_wppOpForgottenColimitIso
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetCokernelCoforkPresentation D.u D.v) :
    AddCommGrpKernelExact
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    D
    (cokernelRowIsoOfTargetPresentation D
      (targetCokernelRowPresentation_of_wppOpForgottenColimitIso P))

/-- Machine-readable W356 support state. -/
structure AddCommGrpTargetCokernelPresentationV369SupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpTargetCokernelPresentationV369SupportState :
    AddCommGrpTargetCokernelPresentationV369SupportState where
  seed := "5zi88wDV1BYWcma0LuTN2uTv"
  checkedConstructors :=
    ["WppOpForgottenTargetCokernelCoforkPresentation",
      "targetCokernelRowPresentation_of_wppOpForgottenColimitIso",
      "differenceSnakeBoundaryInputs_of_wppOpForgottenColimitIso",
      "strictSnakeCokernelData_of_wppOpForgottenColimitIso",
      "addCommGrpKernelExact_of_wppOpForgottenColimitIso"]
  remainingInputs :=
    ["construct the concrete difference kernel row",
      "construct the concrete difference cokernel row",
      "prove the WPP-op colimit row, after forgetting to AddCommGrpCat, is isomorphic to that cokernel row",
      "connect ShortComplex.isColimitOfIsColimitπ degreewise colimits to the cokernel cofork row"]
  productSuccessClaimed := false

theorem currentAddCommGrpTargetCokernelPresentationV369SupportState_productSuccess :
    currentAddCommGrpTargetCokernelPresentationV369SupportState.productSuccessClaimed = false := rfl

section Checks

#check DifferenceSnakeBoundaryInputs
#check TargetCokernelRowPresentation
#check WppOpForgottenTargetCokernelCoforkPresentation
#check cokernelCofork_isColimit_comp_iso_hom
#check targetCokernelRowPresentation_of_wppOpForgottenColimitIso
#check cokernelRowIsoOfTargetPresentation
#check differenceSnakeBoundaryInputs_of_targetCokernelRowPresentation
#check differenceSnakeBoundaryInputs_of_wppOpForgottenColimitIso
#check strictSnakeCokernelData_of_wppOpForgottenColimitIso
#check addCommGrpKernelExact_of_wppOpForgottenColimitIso
#check currentAddCommGrpTargetCokernelPresentationV369SupportState
#check currentAddCommGrpTargetCokernelPresentationV369SupportState_productSuccess
#check ShortComplex.isColimitOfIsColimitπ

end Checks

end AddCommGrpTargetCokernelPresentationV369SupportW356

end LeanLCAExactChallenge
