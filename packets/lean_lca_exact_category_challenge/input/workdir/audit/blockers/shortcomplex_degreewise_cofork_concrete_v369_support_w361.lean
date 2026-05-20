import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W361: concrete degreewise cokernel-cofork support for W359.

The W359 audit file is checked directly by path and is not importable as a Lean
module from this worktree.  This file therefore keeps a W359-compatible target
schema locally and adds the more concrete component-level data requested by
W361: three `CokernelCofork.ofπ` colimit proofs together with the differential
compatibility equations needed to assemble a `ShortComplex` morphism.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexDegreewiseCoforkConcreteV369SupportW361

/--
Local W359-compatible schema: the fields match
`ShortComplexCokernelRowDegreewiseV369SupportW359.DegreewiseCokernelCoforkData`.
-/
structure W359CompatibleDegreewiseCokernelCoforkData
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

/-- W359-compatible degreewise data assembles to a ShortComplex cokernel cofork. -/
def W359CompatibleDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : W359CompatibleDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ D.qT D.wT) D.hπ₁ D.hπ₂ D.hπ₃

/--
Concrete componentwise cokernel-cofork data for a short-complex morphism
`u - v`.  The `comm₁₂` and `comm₂₃` fields are exactly the differential
compatibility equations needed to turn the three component quotient maps into a
single morphism of short complexes.
-/
structure ConcreteDegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  q₁ : L₂.X₁ ⟶ T.X₁
  q₂ : L₂.X₂ ⟶ T.X₂
  q₃ : L₂.X₃ ⟶ T.X₃
  comm₁₂ : q₁ ≫ T.f = L₂.f ≫ q₂ := by cat_disch
  comm₂₃ : q₂ ≫ T.g = L₂.g ≫ q₃ := by cat_disch
  w₁ : (u.τ₁ - v.τ₁) ≫ q₁ = 0 := by cat_disch
  w₂ : (u.τ₂ - v.τ₂) ≫ q₂ = 0 := by cat_disch
  w₃ : (u.τ₃ - v.τ₃) ≫ q₃ = 0 := by cat_disch
  h₁ : IsColimit (CokernelCofork.ofπ q₁ w₁)
  h₂ : IsColimit (CokernelCofork.ofπ q₂ w₂)
  h₃ : IsColimit (CokernelCofork.ofπ q₃ w₃)

/-- The component maps and differential equations assemble to a ShortComplex morphism. -/
def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

/-- Componentwise zero equations imply the assembled short-complex cofork equation. -/
theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

/--
Consumer into the W359-compatible schema.  The concrete fields record the three
component `CokernelCofork.ofπ` proofs and the differential equations; the three
mapped-cocone inputs are kept explicit because W359's schema consumes exactly
the output type of `ShortComplex.πᵢ.mapCocone`.
-/
def ConcreteDegreewiseCokernelCoforkData.toW359Compatible
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (hπ₁ :
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT)))
    (hπ₂ :
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT)))
    (hπ₃ :
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT))) :
    W359CompatibleDegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := hπ₁
  hπ₂ := hπ₂
  hπ₃ := hπ₃

/-- Concrete degreewise cofork data is enough to build a ShortComplex cokernel cofork. -/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (hπ₁ :
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT)))
    (hπ₂ :
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT)))
    (hπ₃ :
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT))) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  (D.toW359Compatible hπ₁ hπ₂ hπ₃).shortComplexCokernel

/--
Checked boundary: `ShortComplex.isColimitOfIsColimitπ` consumes mapped cocone
colimit proofs.  It does not itself manufacture the three component
`CokernelCofork.ofπ` proofs or the differential compatibility equations.
-/
structure IsColimitOfIsColimitπInputBoundary
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  needsMappedπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  needsMappedπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  needsMappedπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  notProvidedByTheAPI : List String :=
    ["component quotient maps q1 q2 q3",
      "differential compatibility q1 >> T.f = L2.f >> q2",
      "differential compatibility q2 >> T.g = L2.g >> q3",
      "component cokernel cofork colimit proofs"]

def IsColimitOfIsColimitπInputBoundary.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (B : IsColimitOfIsColimitπInputBoundary u v T) :
    IsColimit (CokernelCofork.ofπ B.qT B.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ B.qT B.wT) B.needsMappedπ₁ B.needsMappedπ₂ B.needsMappedπ₃

structure ShortComplexDegreewiseCoforkConcreteSupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexDegreewiseCoforkConcreteSupportState :
    ShortComplexDegreewiseCoforkConcreteSupportState where
  seed := "X0KzMfpBXCmFCmQQEXfx03It"
  checkedConstructors :=
    ["ConcreteDegreewiseCokernelCoforkData",
      "ConcreteDegreewiseCokernelCoforkData.qT",
      "ConcreteDegreewiseCokernelCoforkData.wT",
      "ConcreteDegreewiseCokernelCoforkData.toW359Compatible",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel",
      "IsColimitOfIsColimitπInputBoundary"]
  remainingInputs :=
    ["construct concrete component cokernel coforks in AddCommGrpCat",
      "prove their differential compatibility equations",
      "connect the local W359-compatible schema to the importable W359 declaration once promoted"]
  productSuccessClaimed := false

theorem currentShortComplexDegreewiseCoforkConcreteSupportState_productSuccess :
    currentShortComplexDegreewiseCoforkConcreteSupportState.productSuccessClaimed = false := rfl

section Checks

#check ConcreteDegreewiseCokernelCoforkData
#check ConcreteDegreewiseCokernelCoforkData.qT
#check ConcreteDegreewiseCokernelCoforkData.wT
#check ConcreteDegreewiseCokernelCoforkData.toW359Compatible
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel
#check W359CompatibleDegreewiseCokernelCoforkData.shortComplexCokernel
#check IsColimitOfIsColimitπInputBoundary.shortComplexCokernel
#check currentShortComplexDegreewiseCoforkConcreteSupportState_productSuccess

end Checks

end ShortComplexDegreewiseCoforkConcreteV369SupportW361

end LeanLCAExactChallenge
