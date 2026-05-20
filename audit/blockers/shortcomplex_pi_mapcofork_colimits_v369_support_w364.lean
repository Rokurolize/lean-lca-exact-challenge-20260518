import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W364: `ShortComplex.πᵢ.mapCocone` colimit support for W361/W359.

W361 packages concrete component cokernel coforks, but W359 consumes the
colimit proofs after mapping the assembled short-complex cofork along
`ShortComplex.π₁`, `π₂`, and `π₃`.  This file isolates the remaining checked
transport boundary: once the three mapped cocones are identified with the
component cokernel coforks, the component `IsColimit` proofs become the exact
`hπ₁/hπ₂/hπ₃` inputs required by
`ShortComplex.isColimitOfIsColimitπ`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexPiMapCoforkColimitsV369SupportW364

/--
Local W361-compatible concrete componentwise cokernel-cofork data.

The field names and types intentionally match W361's
`ConcreteDegreewiseCokernelCoforkData`; W361 is an audit file rather than an
importable module in this worktree.
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

/-- The component quotient maps assemble to a short-complex morphism. -/
def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

/-- Component zero equations assemble to the short-complex cofork equation. -/
theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

/-- Local W359-compatible schema for the exact mapped-cocone inputs. -/
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

/-- W359-compatible degreewise data assembles to a short-complex cokernel cofork. -/
def W359CompatibleDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : W359CompatibleDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ D.qT D.wT) D.hπ₁ D.hπ₂ D.hπ₃

/--
The explicit boundary required to turn W361's concrete component proofs into
W359's mapped-`πᵢ` inputs.

The concrete component coforks are cocones on
`parallelPair (u.τᵢ - v.τᵢ) 0`, while the mapped short-complex coforks are
cocones on `parallelPair (u - v) 0 ⋙ ShortComplex.πᵢ`.  The missing mathlib
support is therefore not merely a point isomorphism of two cocones over the
same diagram; it is a diagram/cocone identification plus `IsColimit` transport.
This boundary names exactly the transport theorems that downstream code needs.
-/
structure PiMapCoforkComponentTransportBoundary
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    {u v : L₁ ⟶ L₂} {T : ShortComplex AddCommGrpCat.{0}}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : Type 1 where
  π₁RequiredCoconeIso : String :=
    "π₁.mapCocone (CokernelCofork.ofπ qT wT) identified with the q₁ component cofork"
  π₂RequiredCoconeIso : String :=
    "π₂.mapCocone (CokernelCofork.ofπ qT wT) identified with the q₂ component cofork"
  π₃RequiredCoconeIso : String :=
    "π₃.mapCocone (CokernelCofork.ofπ qT wT) identified with the q₃ component cofork"
  π₁MapCoforkIsColimitOfComponent :
    IsColimit (CokernelCofork.ofπ D.q₁ D.w₁) →
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT))
  π₂MapCoforkIsColimitOfComponent :
    IsColimit (CokernelCofork.ofπ D.q₂ D.w₂) →
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT))
  π₃MapCoforkIsColimitOfComponent :
    IsColimit (CokernelCofork.ofπ D.q₃ D.w₃) →
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ D.qT D.wT))

/-- Transport the component degree-1 cokernel proof across the mapped-cocone isomorphism. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₁MapCoforkIsColimitOfComponent D.h₁

/-- Transport the component degree-2 cokernel proof across the mapped-cocone isomorphism. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₂MapCoforkIsColimitOfComponent D.h₂

/-- Transport the component degree-3 cokernel proof across the mapped-cocone isomorphism. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₃MapCoforkIsColimitOfComponent D.h₃

/--
Consumer from W361's concrete component proofs plus the three mapped-cocone
isomorphisms to the exact W359-compatible `hπ₁/hπ₂/hπ₃` package.
-/
def ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    W359CompatibleDegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁OfComponentIso B
  hπ₂ := D.hπ₂OfComponentIso B
  hπ₃ := D.hπ₃OfComponentIso B

/--
End-to-end checked consumer: concrete component cofork colimits plus the three
mapped-cocone identifications yield the short-complex cokernel colimit proof.
-/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  (D.toW359CompatibleOfComponentIso B).shortComplexCokernel

/-- Machine-readable W364 support state. -/
structure ShortComplexPiMapCoforkColimitsSupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexPiMapCoforkColimitsSupportState :
    ShortComplexPiMapCoforkColimitsSupportState where
  seed := "UtJpgbkla7vnL67vjnSm3CeT"
  checkedConstructors :=
    ["PiMapCoforkComponentTransportBoundary",
      "ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentIso",
      "ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentIso",
      "ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentIso",
      "ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentIso",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentIso"]
  remainingInputs :=
    ["construct π₁.mapCocone (CokernelCofork.ofπ qT wT) ≅ CokernelCofork.ofπ q₁ w₁",
      "construct π₂.mapCocone (CokernelCofork.ofπ qT wT) ≅ CokernelCofork.ofπ q₂ w₂",
      "construct π₃.mapCocone (CokernelCofork.ofπ qT wT) ≅ CokernelCofork.ofπ q₃ w₃"]
  productSuccessClaimed := false

theorem currentShortComplexPiMapCoforkColimitsSupportState_productSuccess :
    currentShortComplexPiMapCoforkColimitsSupportState.productSuccessClaimed = false := rfl

section Checks

#check PiMapCoforkComponentTransportBoundary
#check ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentIso
#check ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentIso
#check ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentIso
#check ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentIso
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentIso
#check W359CompatibleDegreewiseCokernelCoforkData.shortComplexCokernel
#check ShortComplex.isColimitOfIsColimitπ
#check currentShortComplexPiMapCoforkColimitsSupportState_productSuccess

end Checks

end ShortComplexPiMapCoforkColimitsV369SupportW364

end LeanLCAExactChallenge
