import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W367: explicit cocone transport support for W364.

W364 isolated the needed functions from component cokernel cofork colimits to
the three `ShortComplex.πᵢ.mapCocone` colimits.  A direct `simpa` from the
component cofork proof to the mapped-cocone proof fails because the diagrams are
not definitionally equal: the component proof is a cocone on
`parallelPair (u.τᵢ - v.τᵢ) 0`, while the mapped short-complex cofork is a
cocone on `(parallelPair (u - v) 0) ⋙ ShortComplex.πᵢ`.

This file sharpens that boundary.  It names the exact missing data as a natural
isomorphism of the two parallel-pair diagrams plus an isomorphism between the
precomposed component cofork and the mapped cocone.  From those two pieces,
Lean checks the `IsColimit` transport for `π₁`, `π₂`, and `π₃`, and packages
the resulting functions in the same consumer shape as W364.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexPiCoconeTransportV370SupportW367

/--
Local W361/W364-compatible concrete componentwise cokernel-cofork data.

The audit files are checked by path in this worktree rather than imported as
modules, so this file repeats the small shared schema.
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
Exact missing transport data for one projection.

`componentDiagramIso` identifies the component cokernel parallel-pair diagram
with the projected short-complex cokernel diagram.  `componentCoforkIso`
then identifies the component cofork, after precomposition along that diagram
isomorphism, with the mapped cocone consumed by `ShortComplex.isColimitOfIsColimitπ`.
-/
structure PiMapCoforkComponentCoconeTransport
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (componentCofork : Cocone (parallelPair (u.τ₁ - v.τ₁) 0))
    (projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))) :
    Type 1 where
  componentDiagramIso :
    parallelPair (u.τ₁ - v.τ₁) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
  componentCoforkIso :
    (Cocone.precompose componentDiagramIso.inv).obj componentCofork ≅ projectedCofork

/-- Transport a component `π₁` cofork colimit proof to the mapped short-complex cofork. -/
def PiMapCoforkComponentCoconeTransport.isColimit
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {componentCofork : Cocone (parallelPair (u.τ₁ - v.τ₁) 0)}
    {projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))}
    (B : PiMapCoforkComponentCoconeTransport componentCofork projectedCofork)
    (h : IsColimit componentCofork) :
    IsColimit projectedCofork :=
  (IsColimit.equivOfNatIsoOfIso B.componentDiagramIso
    componentCofork projectedCofork B.componentCoforkIso) h

/--
The same boundary specialized to the three projections of a concrete
degreewise cokernel cofork.
-/
structure PiMapCoforkComponentTransportBoundary
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    {u v : L₁ ⟶ L₂} {T : ShortComplex AddCommGrpCat.{0}}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : Type 1 where
  π₁Transport :
    PiMapCoforkComponentCoconeTransport
      (CokernelCofork.ofπ D.q₁ D.w₁)
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

/-- Transport the component degree-1 cokernel proof across the explicit diagram/cocone isomorphisms. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeTransport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₁Transport.isColimit D.h₁

/-- Transport the component degree-2 cokernel proof using W364's still-open function boundary. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₂MapCoforkIsColimitOfComponent D.h₂

/-- Transport the component degree-3 cokernel proof using W364's still-open function boundary. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  B.π₃MapCoforkIsColimitOfComponent D.h₃

/-- Consumer into the exact W359-compatible package. -/
def ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentTransport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    W359CompatibleDegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁OfComponentCoconeTransport B
  hπ₂ := D.hπ₂OfComponentIso B
  hπ₃ := D.hπ₃OfComponentIso B

/--
End-to-end checked consumer: the explicit `π₁` diagram/cocone transport plus
the remaining W364-style transports for `π₂` and `π₃` yield the short-complex
cokernel colimit proof.
-/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentTransport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : PiMapCoforkComponentTransportBoundary D) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  (D.toW359CompatibleOfComponentTransport B).shortComplexCokernel

/-- Machine-readable W367 support state. -/
structure ShortComplexPiCoconeTransportSupportState : Type where
  seed : String
  checkedConstructors : List String
  directTransportResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexPiCoconeTransportSupportState :
    ShortComplexPiCoconeTransportSupportState where
  seed := "2FJ01JGgt34wOeaSxGADFa5a"
  checkedConstructors :=
    ["PiMapCoforkComponentCoconeTransport",
      "PiMapCoforkComponentCoconeTransport.isColimit",
      "PiMapCoforkComponentTransportBoundary",
      "ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeTransport",
      "ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentTransport",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentTransport"]
  directTransportResult := "partial"
  remainingInputs :=
    ["construct π₁ natural isomorphism parallelPair (u.τ₁ - v.τ₁) 0 ≅ parallelPair (u - v) 0 ⋙ ShortComplex.π₁",
      "construct π₁ cocone isomorphism after precomposition",
      "repeat the explicit diagram/cocone transport specialization for π₂ and π₃"]
  productSuccessClaimed := false

theorem currentShortComplexPiCoconeTransportSupportState_productSuccess :
    currentShortComplexPiCoconeTransportSupportState.productSuccessClaimed = false := rfl

section Checks

#check ConcreteDegreewiseCokernelCoforkData.qT
#check ConcreteDegreewiseCokernelCoforkData.wT
#check PiMapCoforkComponentCoconeTransport
#check PiMapCoforkComponentCoconeTransport.isColimit
#check ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeTransport
#check ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfComponentTransport
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfComponentTransport
#check ShortComplex.isColimitOfIsColimitπ
#check currentShortComplexPiCoconeTransportSupportState_productSuccess

end Checks

end ShortComplexPiCoconeTransportV370SupportW367

end LeanLCAExactChallenge
