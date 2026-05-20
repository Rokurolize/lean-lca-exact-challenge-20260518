import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W376: AddCommGrp short-complex cokernel iso support after W373.

The adjacent W373/W350/W353/W356 blocker files are checked by path in this
worktree, not importable Lean modules.  This standalone file therefore keeps the
small local schemas needed to connect them:

* W373-shaped concrete degreewise cokernel cofork data, including the checked
  `shortComplexCokernelOfPi123CoconeIso` consumer.
* W353/W356-shaped target cokernel-row presentations.
* W350-shaped boundary input packages and consumers into the existing
  `AddCommGrpSnakeInputDifferenceCokernel` declarations.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpShortComplexCokernelIsoV370SupportW376

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- W373-shaped concrete componentwise cokernel-cofork data. -/
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

/-- The three component quotient maps assemble to a short-complex morphism. -/
def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

/-- The component zero equations assemble to the short-complex cofork equation. -/
theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

/-- W359-compatible local schema consumed by `ShortComplex.isColimitOfIsColimitπ`. -/
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

/-- Degreewise mapped cofork proofs assemble to a short-complex cokernel cofork. -/
def DegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : DegreewiseCokernelCoforkData u v T) :
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

/-- The projected `π₂` parallel-pair diagram is the component diagram. -/
def pi2ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₂ - v.τ₂) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The component cofork is the `π₂` mapped short-complex cofork. -/
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

/-- The projected `π₃` parallel-pair diagram is the component diagram. -/
def pi3ParallelPairDiagramIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    parallelPair (u.τ₃ - v.τ₃) 0 ≅
      (parallelPair (u - v) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The component cofork is the `π₃` mapped short-complex cofork. -/
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

/-- Transport data for a component cofork. -/
structure PiMapCoforkComponentCoconeTransport
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    {u v : L₁ ⟶ L₂} (π : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
    (componentDiagram : WalkingParallelPair ⥤ AddCommGrpCat.{0})
    (componentCofork : Cocone componentDiagram)
    (projectedCofork : Cocone ((parallelPair (u - v) 0) ⋙ π)) : Type 1 where
  componentDiagramIso : componentDiagram ≅ (parallelPair (u - v) 0) ⋙ π
  componentCoforkIso :
    (Cocone.precompose componentDiagramIso.inv).obj componentCofork ≅ projectedCofork

/-- Transport a component cofork colimit proof to the mapped cofork. -/
def PiMapCoforkComponentCoconeTransport.isColimit
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    {u v : L₁ ⟶ L₂} {π : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}}
    {componentDiagram : WalkingParallelPair ⥤ AddCommGrpCat.{0}}
    {componentCofork : Cocone componentDiagram}
    {projectedCofork : Cocone ((parallelPair (u - v) 0) ⋙ π)}
    (B : PiMapCoforkComponentCoconeTransport π componentDiagram componentCofork projectedCofork)
    (h : IsColimit componentCofork) :
    IsColimit projectedCofork :=
  (IsColimit.equivOfNatIsoOfIso B.componentDiagramIso
    componentCofork projectedCofork B.componentCoforkIso) h

/-- The concrete `π₁` transport package. -/
def pi1Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    PiMapCoforkComponentCoconeTransport
      (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      (parallelPair (u.τ₁ - v.τ₁) 0)
      (CokernelCofork.ofπ D.q₁ D.w₁)
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi1ParallelPairDiagramIso u v
  componentCoforkIso := pi1CokernelCoforkMapCoconeIso D

/-- The concrete `π₂` transport package. -/
def pi2Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    PiMapCoforkComponentCoconeTransport
      (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      (parallelPair (u.τ₂ - v.τ₂) 0)
      (CokernelCofork.ofπ D.q₂ D.w₂)
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi2ParallelPairDiagramIso u v
  componentCoforkIso := pi2CokernelCoforkMapCoconeIso D

/-- The concrete `π₃` transport package. -/
def pi3Transport
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    PiMapCoforkComponentCoconeTransport
      (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      (parallelPair (u.τ₃ - v.τ₃) 0)
      (CokernelCofork.ofπ D.q₃ D.w₃)
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) where
  componentDiagramIso := pi3ParallelPairDiagramIso u v
  componentCoforkIso := pi3CokernelCoforkMapCoconeIso D

/-- The component degree-1 cokernel proof transports to the mapped `π₁` cofork. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₁OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi1Transport D).isColimit D.h₁

/-- The component degree-2 cokernel proof transports to the mapped `π₂` cofork. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₂OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi2Transport D).isColimit D.h₂

/-- The component degree-3 cokernel proof transports to the mapped `π₃` cofork. -/
def ConcreteDegreewiseCokernelCoforkData.hπ₃OfComponentCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (pi3Transport D).isColimit D.h₃

/-- W373's concrete package supplies the exact degreewise input W359 expects. -/
def ConcreteDegreewiseCokernelCoforkData.toDegreewiseOfPi123CoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    DegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁OfComponentCoconeIso
  hπ₂ := D.hπ₂OfComponentCoconeIso
  hπ₃ := D.hπ₃OfComponentCoconeIso

/-- W373's checked consumer: concrete `π₁/π₂/π₃` coforks give a short-complex cokernel. -/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi123CoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  D.toDegreewiseOfPi123CoconeIso.shortComplexCokernel

/-- W353/W356-shaped target row presentation for the same difference map. -/
structure TargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hT : IsColimit (CokernelCofork.ofπ qT wT)

/-- W373's short-complex cokernel proof directly supplies the W353 target presentation. -/
def targetCokernelRowPresentation_of_concreteDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    TargetCokernelRowPresentation u v T where
  qT := D.qT
  wT := D.wT
  hT := D.shortComplexCokernelOfPi123CoconeIso

/--
The minimal checked adapter requested by W376: concrete degreewise cofork data,
the target cokernel-row presentation it supplies, and the short-complex colimit
proof used as the cokernel-row iso input downstream.
-/
structure AddCommGrpShortComplexCokernelIsoAdapter
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  concreteDegreewiseCoforkData : ConcreteDegreewiseCokernelCoforkData u v T
  targetCokernelRowPresentation : TargetCokernelRowPresentation u v T
  shortComplexColimit :
    IsColimit
      (CokernelCofork.ofπ targetCokernelRowPresentation.qT
        targetCokernelRowPresentation.wT)

/-- Canonical W376 adapter built from W373 concrete degreewise data. -/
def addCommGrpShortComplexCokernelIsoAdapter_of_concreteDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    AddCommGrpShortComplexCokernelIsoAdapter u v T where
  concreteDegreewiseCoforkData := D
  targetCokernelRowPresentation := targetCokernelRowPresentation_of_concreteDegreewise D
  shortComplexColimit := D.shortComplexCokernelOfPi123CoconeIso

/-- Local W350-shaped boundary input package. -/
structure DifferenceSnakeBoundaryInputs
    (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  differenceKernelRow : ShortComplex AddCommGrpCat.{0}
  differenceMiddleRow : ShortComplex AddCommGrpCat.{0}
  differenceCokernelRow : ShortComplex AddCommGrpCat.{0}
  differenceData :
    ParallelPairDifferenceStrictCokernelData
      differenceKernelRow differenceMiddleRow differenceCokernelRow
  cokernelRowIso : differenceCokernelRow ≅ T

/-- A strict difference-cokernel row and W373 concrete target presentation identify cokernel rows. -/
def cokernelRowIsoOfConcreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    L₃ ≅ T :=
  IsColimit.coconePointUniqueUpToIso D.h₃
    (targetCokernelRowPresentation_of_concreteDegreewise P).hT

/--
Consumer theorem reducing W350's cokernel-row iso input to W373's concrete
short-complex cokernel proof.
-/
def differenceSnakeBoundaryInputs_of_concreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    DifferenceSnakeBoundaryInputs T where
  differenceKernelRow := L₁
  differenceMiddleRow := L₂
  differenceCokernelRow := L₃
  differenceData := D
  cokernelRowIso := cokernelRowIsoOfConcreteDegreewise D P

/-- Direct consumer into W318's strict SnakeInput cokernel certificate. -/
def strictSnakeCokernelData_of_concreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfConcreteDegreewise D P)

/-- Element-level exactness consumer supplied by the same W373-to-W350 bridge. -/
theorem addCommGrpKernelExact_of_concreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    AddCommGrpKernelExact T :=
  addCommGrpKernelExact_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfConcreteDegreewise D P)

/-- W356-shaped WPP-op forgotten target cokernel-cofork presentation. -/
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
If the W373 concrete row is identified with the forgotten WPP-op colimit row,
it supplies exactly the W356 target cokernel presentation boundary.
-/
def wppOpForgottenTargetCokernelCoforkPresentation_of_concreteDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs)
    (D : ConcreteDegreewiseCokernelCoforkData u v T)
    (targetIso : T ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :
    WppOpForgottenTargetCokernelCoforkPresentation u v where
  S := S
  cs := cs
  hcs := hcs
  C := T
  qC := D.qT
  wC := D.wT
  hC := D.shortComplexCokernelOfPi123CoconeIso
  targetIso := targetIso

/-- Machine-readable W376 support state. -/
structure AddCommGrpShortComplexCokernelIsoV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  addcommgrpCokernelIsoResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpShortComplexCokernelIsoV370SupportState :
    AddCommGrpShortComplexCokernelIsoV370SupportState where
  seed := "a68dfbe006b36f9f481f27c1c9435e53"
  checkedConstructors :=
    ["ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi123CoconeIso",
      "targetCokernelRowPresentation_of_concreteDegreewise",
      "AddCommGrpShortComplexCokernelIsoAdapter",
      "addCommGrpShortComplexCokernelIsoAdapter_of_concreteDegreewise",
      "cokernelRowIsoOfConcreteDegreewise",
      "differenceSnakeBoundaryInputs_of_concreteDegreewise",
      "strictSnakeCokernelData_of_concreteDegreewise",
      "addCommGrpKernelExact_of_concreteDegreewise",
      "wppOpForgottenTargetCokernelCoforkPresentation_of_concreteDegreewise"]
  addcommgrpCokernelIsoResult := "proved"
  remainingInputs :=
    ["construct the concrete AddCommGrp degreewise cokernel cofork data",
      "construct the strict difference kernel/cokernel rows",
      "identify the resulting concrete cokernel row with the forgotten WPP-op colimit row",
      "promote the standalone audit schemas into importable modules if they are needed outside audit/blockers"]
  productSuccessClaimed := false

theorem currentAddCommGrpShortComplexCokernelIsoV370SupportState_productSuccess :
    currentAddCommGrpShortComplexCokernelIsoV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernelOfPi123CoconeIso
#check targetCokernelRowPresentation_of_concreteDegreewise
#check AddCommGrpShortComplexCokernelIsoAdapter
#check addCommGrpShortComplexCokernelIsoAdapter_of_concreteDegreewise
#check cokernelRowIsoOfConcreteDegreewise
#check differenceSnakeBoundaryInputs_of_concreteDegreewise
#check strictSnakeCokernelData_of_concreteDegreewise
#check addCommGrpKernelExact_of_concreteDegreewise
#check wppOpForgottenTargetCokernelCoforkPresentation_of_concreteDegreewise
#check currentAddCommGrpShortComplexCokernelIsoV370SupportState_productSuccess

end Checks

end AddCommGrpShortComplexCokernelIsoV370SupportW376

end LeanLCAExactChallenge
