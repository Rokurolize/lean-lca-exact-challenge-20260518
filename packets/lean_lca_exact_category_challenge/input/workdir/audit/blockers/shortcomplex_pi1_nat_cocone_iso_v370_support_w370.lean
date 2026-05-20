import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W370: explicit `π₁` natural/cocone isomorphism support for W367.

This file checks the missing `π₁` identifications isolated by W367.  The
component parallel-pair diagram and the projected short-complex parallel-pair
diagram are definitionally equal after unfolding the first component of the
short-complex morphism `u - v`.  The corresponding mapped cofork is also
definitionally the component cofork after precomposition along the reflexive
diagram isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexPi1NatCoconeIsoV370SupportW370

/--
Local W367-compatible concrete componentwise cokernel-cofork data.

The audit support files are checked by path rather than imported as modules, so
this file repeats the small schema needed to state the π₁ transport.
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

/-- The projected `π₁` parallel-pair diagram is the component diagram. -/
def pi1ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₁ - v.τ₁) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The component cofork is the `π₁` mapped short-complex cofork. -/
def pi1CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose (pi1ParallelPairDiagramIso u v).inv).obj
        (CokernelCofork.ofπ D.q₁ D.w₁) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [pi1ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [pi1ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT])

/--
Exact W367 transport data for `π₁`, now with both required isomorphisms
constructed.
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

/-- The concrete `π₁` transport package required by W367. -/
def pi1Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    PiMapCoforkComponentCoconeTransport
      (CokernelCofork.ofπ D.q₁ D.w₁)
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi1ParallelPairDiagramIso u v
  componentCoforkIso := pi1CokernelCoforkMapCoconeIso D

/-- The component degree-1 cokernel proof transports to the mapped `π₁` cofork. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi1Transport D).isColimit D.h₁

/-- Boundary for the remaining two projected components. -/
structure Pi23MapCoforkComponentTransportBoundary
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    {u v : L₁ ⟶ L₂} {T : ShortComplex AddCommGrpCat.{0}}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : Type 1 where
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

/-- Consumer into the exact W359-compatible package, with `π₁` no longer assumed. -/
def ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfPi1CoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : Pi23MapCoforkComponentTransportBoundary D) :
    W359CompatibleDegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁OfComponentCoconeIso
  hπ₂ := B.π₂MapCoforkIsColimitOfComponent D.h₂
  hπ₃ := B.π₃MapCoforkIsColimitOfComponent D.h₃

/-- End-to-end checked consumer after constructing the explicit `π₁` isomorphisms. -/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi1CoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (B : Pi23MapCoforkComponentTransportBoundary D) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  (D.toW359CompatibleOfPi1CoconeIso B).shortComplexCokernel

/-- Machine-readable W370 support state. -/
structure ShortComplexPi1NatCoconeIsoSupportState : Type where
  seed : String
  checkedConstructors : List String
  pi1IsoResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexPi1NatCoconeIsoSupportState :
    ShortComplexPi1NatCoconeIsoSupportState where
  seed := "47488eb3b11f3689668abb4b85eff02b"
  checkedConstructors :=
    ["pi1ParallelPairDiagramIso",
      "pi1CokernelCoforkMapCoconeIso",
      "pi1Transport",
      "ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeIso",
      "ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfPi1CoconeIso",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi1CoconeIso"]
  pi1IsoResult := "proved"
  remainingInputs :=
    ["construct analogous π₂ natural/cocone transport",
      "construct analogous π₃ natural/cocone transport",
      "promote the checked audit support into the main importable Lean module"]
  productSuccessClaimed := false

theorem currentShortComplexPi1NatCoconeIsoSupportState_productSuccess :
    currentShortComplexPi1NatCoconeIsoSupportState.productSuccessClaimed = false := rfl

section Checks

#check pi1ParallelPairDiagramIso
#check pi1CokernelCoforkMapCoconeIso
#check pi1Transport
#check PiMapCoforkComponentCoconeTransport.isColimit
#check ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeIso
#check ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfPi1CoconeIso
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi1CoconeIso
#check currentShortComplexPi1NatCoconeIsoSupportState_productSuccess

end Checks

end ShortComplexPi1NatCoconeIsoV370SupportW370

end LeanLCAExactChallenge
