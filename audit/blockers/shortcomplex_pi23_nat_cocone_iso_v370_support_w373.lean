import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W373: explicit `π₂` and `π₃` natural/cocone isomorphism support.

W370 closed the `π₁` projection transport isolated by W367.  This standalone
audit file proves the same definitional diagram/cocone identifications for
`π₂` and `π₃`, and packages all three projected cofork colimit proofs into the
W359-compatible short-complex cokernel consumer.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexPi23NatCoconeIsoV370SupportW373

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

def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

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

def W359CompatibleDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : W359CompatibleDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ D.qT D.wT) D.hπ₁ D.hπ₂ D.hπ₃

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

def pi1ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₁ - v.τ₁) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

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

def pi1Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    PiMapCoforkComponentCoconeTransport
      (CokernelCofork.ofπ D.q₁ D.w₁)
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi1ParallelPairDiagramIso u v
  componentCoforkIso := pi1CokernelCoforkMapCoconeIso D

def ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi1Transport D).isColimit D.h₁

structure Pi2MapCoforkComponentCoconeTransport
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (componentCofork : Cocone (parallelPair (u.τ₂ - v.τ₂) 0))
    (projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))) :
    Type 1 where
  componentDiagramIso :
    parallelPair (u.τ₂ - v.τ₂) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
  componentCoforkIso :
    (Cocone.precompose componentDiagramIso.inv).obj componentCofork ≅ projectedCofork

def Pi2MapCoforkComponentCoconeTransport.isColimit
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {componentCofork : Cocone (parallelPair (u.τ₂ - v.τ₂) 0)}
    {projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))}
    (B : Pi2MapCoforkComponentCoconeTransport componentCofork projectedCofork)
    (h : IsColimit componentCofork) :
    IsColimit projectedCofork :=
  (IsColimit.equivOfNatIsoOfIso B.componentDiagramIso
    componentCofork projectedCofork B.componentCoforkIso) h

def pi2ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₂ - v.τ₂) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

def pi2CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose (pi2ParallelPairDiagramIso u v).inv).obj
        (CokernelCofork.ofπ D.q₂ D.w₂) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [pi2ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [pi2ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT])

def pi2Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    Pi2MapCoforkComponentCoconeTransport
      (CokernelCofork.ofπ D.q₂ D.w₂)
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi2ParallelPairDiagramIso u v
  componentCoforkIso := pi2CokernelCoforkMapCoconeIso D

def ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi2Transport D).isColimit D.h₂

structure Pi3MapCoforkComponentCoconeTransport
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (componentCofork : Cocone (parallelPair (u.τ₃ - v.τ₃) 0))
    (projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))) :
    Type 1 where
  componentDiagramIso :
    parallelPair (u.τ₃ - v.τ₃) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
  componentCoforkIso :
    (Cocone.precompose componentDiagramIso.inv).obj componentCofork ≅ projectedCofork

def Pi3MapCoforkComponentCoconeTransport.isColimit
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {componentCofork : Cocone (parallelPair (u.τ₃ - v.τ₃) 0)}
    {projectedCofork :
      Cocone ((parallelPair (u - v) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))}
    (B : Pi3MapCoforkComponentCoconeTransport componentCofork projectedCofork)
    (h : IsColimit componentCofork) :
    IsColimit projectedCofork :=
  (IsColimit.equivOfNatIsoOfIso B.componentDiagramIso
    componentCofork projectedCofork B.componentCoforkIso) h

def pi3ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₃ - v.τ₃) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

def pi3CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose (pi3ParallelPairDiagramIso u v).inv).obj
        (CokernelCofork.ofπ D.q₃ D.w₃) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [pi3ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [pi3ParallelPairDiagramIso, ConcreteDegreewiseCokernelCoforkData.qT])

def pi3Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    Pi3MapCoforkComponentCoconeTransport
      (CokernelCofork.ofπ D.q₃ D.w₃)
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi3ParallelPairDiagramIso u v
  componentCoforkIso := pi3CokernelCoforkMapCoconeIso D

def ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi3Transport D).isColimit D.h₃

def ConcreteDegreewiseCokernelCoforkData.toW359CompatibleOfPiCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    W359CompatibleDegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁OfComponentCoconeIso
  hπ₂ := D.hπ₂OfComponentCoconeIso
  hπ₃ := D.hπ₃OfComponentCoconeIso

def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPiCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  D.toW359CompatibleOfPiCoconeIso.shortComplexCokernel

structure ShortComplexPi23NatCoconeIsoSupportState : Type where
  seed : String
  checkedConstructors : List String
  projectionIsoResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentShortComplexPi23NatCoconeIsoSupportState :
    ShortComplexPi23NatCoconeIsoSupportState where
  seed := "parent-w373-pi23-cocone-iso"
  checkedConstructors :=
    ["pi2ParallelPairDiagramIso",
      "pi2CokernelCoforkMapCoconeIso",
      "pi2Transport",
      "ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentCoconeIso",
      "pi3ParallelPairDiagramIso",
      "pi3CokernelCoforkMapCoconeIso",
      "pi3Transport",
      "ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentCoconeIso",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPiCoconeIso"]
  projectionIsoResult := "π₁/π₂/π₃ component cofork colimit proofs transport to all ShortComplex.πᵢ.mapCocone colimits"
  remainingInputs :=
    ["concrete degreewise cokernel cofork data",
      "component-row isomorphism to the forgotten WPP-op colimit row",
      "short-complex compatibility squares"]
  productSuccessClaimed := false

#check pi2ParallelPairDiagramIso
#check pi2CokernelCoforkMapCoconeIso
#check pi2Transport
#check ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentCoconeIso
#check pi3ParallelPairDiagramIso
#check pi3CokernelCoforkMapCoconeIso
#check pi3Transport
#check ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentCoconeIso
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPiCoconeIso
#check currentShortComplexPi23NatCoconeIsoSupportState

theorem currentShortComplexPi23NatCoconeIsoSupportState_productSuccess :
    currentShortComplexPi23NatCoconeIsoSupportState.productSuccessClaimed = false := rfl

end ShortComplexPi23NatCoconeIsoV370SupportW373

end LeanLCAExactChallenge
