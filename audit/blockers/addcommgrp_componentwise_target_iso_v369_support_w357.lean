import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel

/-!
W357: componentwise target-row isomorphism support for the v369 AddCommGrp route.

W356 leaves the target-side obligation as an isomorphism between a concrete
cokernel row and the WPP-op colimit row after forgetting to `AddCommGrpCat`.
This file isolates a smaller checked constructor for that isomorphism: three
component isomorphisms plus the two short-complex compatibility squares.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpComponentwiseTargetIsoV369SupportW357

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/--
Componentwise isomorphism data from a concrete cokernel row `C` to a target
short complex `T`.
-/
structure ComponentwiseTargetIsoData
    (C T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  e₁ : C.X₁ ≅ T.X₁
  e₂ : C.X₂ ≅ T.X₂
  e₃ : C.X₃ ≅ T.X₃
  comm₁₂ : e₁.hom ≫ T.f = C.f ≫ e₂.hom := by cat_disch
  comm₂₃ : e₂.hom ≫ T.g = C.g ≫ e₃.hom := by cat_disch

/-- Componentwise target data produces an isomorphism of short complexes. -/
def targetIso_of_componentwiseTargetIsoData
    {C T : ShortComplex AddCommGrpCat.{0}}
    (D : ComponentwiseTargetIsoData C T) :
    C ≅ T :=
  ShortComplex.isoMk D.e₁ D.e₂ D.e₃ D.comm₁₂ D.comm₂₃

/--
A WPP-op forgotten colimit row equipped with a concrete componentwise
identification with a cokernel row.
-/
structure WppOpForgottenTargetComponentIsoPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) : Type 1 where
  S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}
  cs : Cocone S
  hcs : IsColimit cs
  C : ShortComplex AddCommGrpCat.{0}
  qC : L₂ ⟶ C
  wC : (u - v) ≫ qC = 0 := by cat_disch
  hC : IsColimit (CokernelCofork.ofπ qC wC)
  componentIso :
    ComponentwiseTargetIsoData C
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/--
The componentwise presentation supplies the target-row isomorphism required by
W356.
-/
def targetIso_of_wppOpForgottenTargetComponentIsoPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (P : WppOpForgottenTargetComponentIsoPresentation u v) :
    P.C ≅ P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  targetIso_of_componentwiseTargetIsoData P.componentIso

/--
Local copy of W356's WPP-op target cokernel presentation, with the target
isomorphism filled from componentwise data.
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
Componentwise target-row data gives the W356-style target cokernel
presentation.
-/
def wppOpForgottenTargetCokernelCoforkPresentation_of_componentIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (P : WppOpForgottenTargetComponentIsoPresentation u v) :
    WppOpForgottenTargetCokernelCoforkPresentation u v where
  S := P.S
  cs := P.cs
  hcs := P.hcs
  C := P.C
  qC := P.qC
  wC := P.wC
  hC := P.hC
  targetIso := targetIso_of_wppOpForgottenTargetComponentIsoPresentation P

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
The componentwise WPP-op forgotten target presentation is a cokernel-row
presentation of the forgotten WPP-op target.
-/
def targetCokernelRowPresentation_of_componentIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (P : WppOpForgottenTargetComponentIsoPresentation u v) :
    TargetCokernelRowPresentation u v
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) where
  qT := P.qC ≫ (targetIso_of_wppOpForgottenTargetComponentIsoPresentation P).hom
  wT := by
    simpa [Category.assoc] using
      congrArg
        (fun k => k ≫ (targetIso_of_wppOpForgottenTargetComponentIsoPresentation P).hom)
        P.wC
  hT :=
    cokernelCofork_isColimit_comp_iso_hom P.hC
      (targetIso_of_wppOpForgottenTargetComponentIsoPresentation P)

/--
Two cokernel presentations of the same difference map have canonically
isomorphic cokernel rows.
-/
def cokernelRowIsoOfComponentwiseTargetPresentation
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetComponentIsoPresentation D.u D.v) :
    L₃ ≅ P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  IsColimit.coconePointUniqueUpToIso D.h₃
    (targetCokernelRowPresentation_of_componentIso P).hT

/--
Direct consumer: a strict difference-cokernel row plus a componentwise WPP-op
target presentation gives the strict SnakeInput certificate for the forgotten
WPP-op colimit row.
-/
def strictSnakeCokernelData_of_componentwiseTargetPresentation
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetComponentIsoPresentation D.u D.v) :
    AddCommGrpStrictSnakeCokernelData
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfComponentwiseTargetPresentation D P)

/--
Element-level exactness consumer for the componentwise target presentation.
-/
theorem addCommGrpKernelExact_of_componentwiseTargetPresentation
    {L₁ L₂ L₃ : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : WppOpForgottenTargetComponentIsoPresentation D.u D.v) :
    AddCommGrpKernelExact
      (P.cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfComponentwiseTargetPresentation D P)

/-- Machine-readable W357 support state. -/
structure AddCommGrpComponentwiseTargetIsoV369SupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpComponentwiseTargetIsoV369SupportState :
    AddCommGrpComponentwiseTargetIsoV369SupportState where
  seed := "w357-componentwise-target-iso-v369"
  checkedConstructors :=
    ["ComponentwiseTargetIsoData",
      "targetIso_of_componentwiseTargetIsoData",
      "WppOpForgottenTargetComponentIsoPresentation",
      "targetIso_of_wppOpForgottenTargetComponentIsoPresentation",
      "wppOpForgottenTargetCokernelCoforkPresentation_of_componentIso",
      "targetCokernelRowPresentation_of_componentIso",
      "cokernelRowIsoOfComponentwiseTargetPresentation",
      "strictSnakeCokernelData_of_componentwiseTargetPresentation",
      "addCommGrpKernelExact_of_componentwiseTargetPresentation"]
  remainingInputs :=
    ["construct the concrete componentwise isomorphisms in degrees 1, 2, and 3",
      "prove the two short-complex compatibility squares",
      "construct the concrete cokernel row and its cokernel cofork proof"]
  productSuccessClaimed := false

theorem currentAddCommGrpComponentwiseTargetIsoV369SupportState_productSuccess :
    currentAddCommGrpComponentwiseTargetIsoV369SupportState.productSuccessClaimed = false := rfl

section Checks

#check ComponentwiseTargetIsoData
#check targetIso_of_componentwiseTargetIsoData
#check WppOpForgottenTargetComponentIsoPresentation
#check targetIso_of_wppOpForgottenTargetComponentIsoPresentation
#check WppOpForgottenTargetCokernelCoforkPresentation
#check wppOpForgottenTargetCokernelCoforkPresentation_of_componentIso
#check TargetCokernelRowPresentation
#check cokernelCofork_isColimit_comp_iso_hom
#check targetCokernelRowPresentation_of_componentIso
#check cokernelRowIsoOfComponentwiseTargetPresentation
#check strictSnakeCokernelData_of_componentwiseTargetPresentation
#check addCommGrpKernelExact_of_componentwiseTargetPresentation
#check currentAddCommGrpComponentwiseTargetIsoV369SupportState
#check currentAddCommGrpComponentwiseTargetIsoV369SupportState_productSuccess
#check ShortComplex.isoMk

end Checks

end AddCommGrpComponentwiseTargetIsoV369SupportW357

end LeanLCAExactChallenge
