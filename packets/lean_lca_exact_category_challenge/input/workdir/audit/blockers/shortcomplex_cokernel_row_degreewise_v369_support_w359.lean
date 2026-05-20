import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W359: degreewise ShortComplex cokernel-row support for the v369 branch.

This standalone blocker file isolates the checked API bridge from degreewise
`ShortComplex.π₁`, `π₂`, and `π₃` cokernel coforks to a cokernel cofork in
`ShortComplex AddCommGrpCat`.  The W356 support file lives under `audit/` and is
not importable as a Lean module in this worktree, so the W356-facing
presentation shape is copied locally.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexCokernelRowDegreewiseV369SupportW359

open AddCommGrpSnakeInputDifferenceCokernel

/--
Degreewise cokernel-cofork data for a short-complex morphism `u - v`.

The three fields `hπ₁`, `hπ₂`, and `hπ₃` are stated after applying the standard
projection functors to the short-complex cofork.  This is the exact shape
consumed by `ShortComplex.isColimitOfIsColimitπ`.
-/
structure DegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))

/--
The degreewise cofork proofs assemble into a cokernel cofork in
`ShortComplex AddCommGrpCat`.
-/
def DegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : DegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ D.qT D.wT) D.hπ₁ D.hπ₂ D.hπ₃

/--
A target row `T` presented as a cokernel row for the difference map `u - v`.
This is the local W356-compatible consumer shape.
-/
structure TargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hT : IsColimit (CokernelCofork.ofπ qT wT)

/-- Degreewise cokernel data is enough to satisfy the W356 target-row input. -/
def targetCokernelRowPresentation_of_degreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : DegreewiseCokernelCoforkData u v T) :
    TargetCokernelRowPresentation u v T where
  qT := D.qT
  wT := D.wT
  hT := D.shortComplexCokernel

/--
Local copy of W356's WPP-op forgotten target cokernel-cofork presentation.

The field names intentionally match W356, so downstream code can replace this
copy with the importable W356 declaration when the audit file is promoted.
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
Boundary package connecting a degreewise cokernel row to the WPP-op colimit row
used by W356.
-/
structure DegreewiseWppOpForgottenBoundary
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) : Type 1 where
  S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}
  cs : Cocone S
  hcs : IsColimit cs
  T : ShortComplex AddCommGrpCat.{0}
  degreewise : DegreewiseCokernelCoforkData u v T
  targetIso :
    T ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
Consumer theorem into the W356-compatible presentation: once the WPP-op colimit
row is identified with a row built from degreewise cokernel coforks, it has the
same cokernel-row presentation fields W356 expects.
-/
def wppOpForgottenTargetCokernelCoforkPresentation_of_degreewise
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (B : DegreewiseWppOpForgottenBoundary u v) :
    WppOpForgottenTargetCokernelCoforkPresentation u v where
  S := B.S
  cs := B.cs
  hcs := B.hcs
  C := B.T
  qC := B.degreewise.qT
  wC := B.degreewise.wT
  hC := B.degreewise.shortComplexCokernel
  targetIso := B.targetIso

/--
Lean-checked frontier statement: no extra short-complex colimit API is needed
after the three mapped coforks are already stated as `IsColimit`s.  The
remaining unbuilt input is the construction of those three mapped cofork proofs
from the concrete row data.
-/
structure ShortComplexCokernelRowDegreewiseSupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexCokernelRowDegreewiseSupportState :
    ShortComplexCokernelRowDegreewiseSupportState where
  seed := "UlCCfwoyhVkBDUfNIkba4W7j"
  checkedConstructors :=
    ["DegreewiseCokernelCoforkData",
      "DegreewiseCokernelCoforkData.shortComplexCokernel",
      "targetCokernelRowPresentation_of_degreewise",
      "DegreewiseWppOpForgottenBoundary",
      "wppOpForgottenTargetCokernelCoforkPresentation_of_degreewise"]
  remainingInputs :=
    ["construct the concrete ShortComplex AddCommGrpCat row T",
      "prove the mapped pi1 cofork is a cokernel cofork",
      "prove the mapped pi2 cofork is a cokernel cofork",
      "prove the mapped pi3 cofork is a cokernel cofork",
      "identify T with the forgotten WPP-op colimit row"]
  productSuccessClaimed := false

theorem currentShortComplexCokernelRowDegreewiseSupportState_productSuccess :
    currentShortComplexCokernelRowDegreewiseSupportState.productSuccessClaimed = false := rfl

section Checks

#check DegreewiseCokernelCoforkData
#check DegreewiseCokernelCoforkData.shortComplexCokernel
#check TargetCokernelRowPresentation
#check targetCokernelRowPresentation_of_degreewise
#check WppOpForgottenTargetCokernelCoforkPresentation
#check DegreewiseWppOpForgottenBoundary
#check wppOpForgottenTargetCokernelCoforkPresentation_of_degreewise
#check ShortComplex.isColimitOfIsColimitπ
#check currentShortComplexCokernelRowDegreewiseSupportState
#check currentShortComplexCokernelRowDegreewiseSupportState_productSuccess

end Checks

end ShortComplexCokernelRowDegreewiseV369SupportW359

end LeanLCAExactChallenge
