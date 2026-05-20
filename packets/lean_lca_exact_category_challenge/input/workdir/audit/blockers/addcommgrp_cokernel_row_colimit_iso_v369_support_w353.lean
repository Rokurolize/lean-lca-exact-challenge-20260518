import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel

/-!
W353: AddCommGrp cokernel-row / colimit-iso support for the v369 branch.

This file isolates the categorical data that turns a concrete cokernel/coequalizer
presentation of the short-complex morphism `u - v` into the W350-style
difference-Snake boundary input package.  The W350 file is a standalone blocker
file rather than a library module, so the small boundary input structure is
copied locally.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpCokernelRowColimitIsoV369SupportW353

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
A target row `T` presented as another cokernel row for the same difference map
`u - v`.
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
The same bridge stated directly for W318's strict SnakeInput certificate.
-/
def strictSnakeCokernelData_of_targetCokernelRowPresentation
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : TargetCokernelRowPresentation D.u D.v T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfTargetPresentation D P)

/--
Consumer theorem: the cokernel-row/colimit-iso bridge is enough to recover the
target AddCommGrp kernel exactness expected downstream.
-/
theorem addCommGrpKernelExact_of_targetCokernelRowPresentation
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : TargetCokernelRowPresentation D.u D.v T) :
    AddCommGrpKernelExact T :=
  addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfTargetPresentation D P)

/-- Machine-readable W353 support state. -/
structure AddCommGrpCokernelRowColimitIsoV369SupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpCokernelRowColimitIsoV369SupportState :
    AddCommGrpCokernelRowColimitIsoV369SupportState where
  seed := "ocSE7BqyRcBUeAnHV4qPSn"
  checkedConstructors :=
    ["TargetCokernelRowPresentation",
      "cokernelCofork_isColimit_comp_iso_hom",
      "cokernelRowIsoOfTargetPresentation",
      "differenceSnakeBoundaryInputs_of_targetCokernelRowPresentation",
      "strictSnakeCokernelData_of_targetCokernelRowPresentation",
      "addCommGrpKernelExact_of_targetCokernelRowPresentation"]
  remainingInputs :=
    ["construct the concrete difference kernel row",
      "construct the concrete difference cokernel row",
      "construct a target cokernel presentation of the WPP-op colimit row for the same u - v"]
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelRowColimitIsoV369SupportState_productSuccess :
    currentAddCommGrpCokernelRowColimitIsoV369SupportState.productSuccessClaimed = false := rfl

section Checks

#check DifferenceSnakeBoundaryInputs
#check TargetCokernelRowPresentation
#check cokernelCofork_isColimit_comp_iso_hom
#check cokernelRowIsoOfTargetPresentation
#check differenceSnakeBoundaryInputs_of_targetCokernelRowPresentation
#check strictSnakeCokernelData_of_targetCokernelRowPresentation
#check addCommGrpKernelExact_of_targetCokernelRowPresentation
#check currentAddCommGrpCokernelRowColimitIsoV369SupportState
#check currentAddCommGrpCokernelRowColimitIsoV369SupportState_productSuccess

end Checks

end AddCommGrpCokernelRowColimitIsoV369SupportW353

end LeanLCAExactChallenge
