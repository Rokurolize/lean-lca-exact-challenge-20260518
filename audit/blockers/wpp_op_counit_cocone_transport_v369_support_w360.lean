import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.CategoryTheory.Whiskering

/-!
W360: WPP-op counit cocone transport support.

W357-left-LCA constructs a concrete quotient cocone over
`walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ X`.
This file transports any such cocone back to the original WPP-op diagram `X`
using the equivalence counit, and preserves colimitness by
`IsColimit.precomposeHomEquiv`.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpCounitCoconeTransportV369SupportW360

/-- The diagram isomorphism from the inverse-whiskered WPP-op diagram back to `X`. -/
def wppOpInverseFunctorCounitDiagramIso
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ X ≅ X :=
  Functor.isoWhiskerRight walkingParallelPairOpEquiv.counitIso X ≪≫
    Functor.leftUnitor X

/-- Transport a cocone over the inverse-whiskered diagram back to a cocone over `X`. -/
def wppOpCoconeOfInverseWhiskered
    {X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (c : Cocone (walkingParallelPairOpEquiv.inverse ⋙
      walkingParallelPairOpEquiv.functor ⋙ X)) :
    Cocone X :=
  (Cocone.precompose (wppOpInverseFunctorCounitDiagramIso X).inv).obj c

/-- The transported cocone has the same point as the inverse-whiskered cocone. -/
theorem wppOpCoconeOfInverseWhiskered_pt
    {X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (c : Cocone (walkingParallelPairOpEquiv.inverse ⋙
      walkingParallelPairOpEquiv.functor ⋙ X)) :
    (wppOpCoconeOfInverseWhiskered c).pt = c.pt :=
  rfl

/-- Colimitness transports along the WPP-op counit diagram isomorphism. -/
def wppOpCoconeOfInverseWhiskeredIsColimit
    {X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {c : Cocone (walkingParallelPairOpEquiv.inverse ⋙
      walkingParallelPairOpEquiv.functor ⋙ X)}
    (hc : IsColimit c) :
    IsColimit (wppOpCoconeOfInverseWhiskered c) :=
  (IsColimit.precomposeHomEquiv (wppOpInverseFunctorCounitDiagramIso X).symm c).symm hc

/-- Boundary package produced by the WPP-op counit transport. -/
structure WppOpCounitTransportedCoconeBoundary
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : Type 1 where
  inverseWhiskeredCocone :
    Cocone (walkingParallelPairOpEquiv.inverse ⋙
      walkingParallelPairOpEquiv.functor ⋙ X)
  inverseWhiskeredIsColimit : IsColimit inverseWhiskeredCocone
  transportedCocone : Cocone X
  transportedIsColimit : IsColimit transportedCocone
  transportedPointEq : transportedCocone.pt = inverseWhiskeredCocone.pt

/-- Build the transported boundary package from any inverse-whiskered colimit cocone. -/
def wppOpCounitTransportedCoconeBoundary
    {X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (c : Cocone (walkingParallelPairOpEquiv.inverse ⋙
      walkingParallelPairOpEquiv.functor ⋙ X))
    (hc : IsColimit c) :
    WppOpCounitTransportedCoconeBoundary X where
  inverseWhiskeredCocone := c
  inverseWhiskeredIsColimit := hc
  transportedCocone := wppOpCoconeOfInverseWhiskered c
  transportedIsColimit := wppOpCoconeOfInverseWhiskeredIsColimit hc
  transportedPointEq := wppOpCoconeOfInverseWhiskered_pt c

/-- Machine-readable W360 state. -/
structure WppOpCounitCoconeTransportV369SupportState : Type where
  seed : String
  checkedConstructors : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpCounitCoconeTransportV369SupportState :
    WppOpCounitCoconeTransportV369SupportState where
  seed := "w360-wpp-op-counit-cocone-transport-v369"
  checkedConstructors :=
    ["wppOpInverseFunctorCounitDiagramIso",
      "wppOpCoconeOfInverseWhiskered",
      "wppOpCoconeOfInverseWhiskeredIsColimit",
      "WppOpCounitTransportedCoconeBoundary",
      "wppOpCounitTransportedCoconeBoundary"]
  remainingInputs :=
    ["rewrite the transported cocone legs into W354 source.ι.app j equations",
      "combine the transported concrete quotient cocone with W357-left-LCA descended map equations",
      "combine with W352/W355 topological fields"]
  productSuccessClaimed := false

theorem currentWppOpCounitCoconeTransportV369SupportState_productSuccess :
    currentWppOpCounitCoconeTransportV369SupportState.productSuccessClaimed = false := rfl

section Checks

#check wppOpInverseFunctorCounitDiagramIso
#check wppOpCoconeOfInverseWhiskered
#check wppOpCoconeOfInverseWhiskered_pt
#check wppOpCoconeOfInverseWhiskeredIsColimit
#check WppOpCounitTransportedCoconeBoundary
#check wppOpCounitTransportedCoconeBoundary
#check currentWppOpCounitCoconeTransportV369SupportState
#check currentWppOpCounitCoconeTransportV369SupportState_productSuccess

end Checks

end WppOpCounitCoconeTransportV369SupportW360

end LeanLCAExactChallenge
