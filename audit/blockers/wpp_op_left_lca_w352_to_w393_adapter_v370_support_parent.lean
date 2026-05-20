import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
Parent support: W352-to-W393 ordinary descended-field adapter.

W352 already packages the three ordinary descended quotient-map fields
for concrete parallel pairs. W393 asks for the same three fields on the
ordinary quotient points attached to a `WalkingParallelPairᵒᵖ` diagram.
This file checks that the former field shape directly supplies the latter.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaW352ToW393AdapterV370SupportParent

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagram (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeft (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRight (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.right

/-- W387/W393 ordinary quotient point for a WPP-op diagram. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W352-style descended quotient fields for ordinary parallel pairs. -/
structure DescendedQuotientFieldsW352
    {A B A' B' : MetrizableLCA.{0}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (descended :
      MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  injective : Function.Injective (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  inducing : IsInducing (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  closed_range : IsClosed (Set.range (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)))

/-- W393 ordinary-side certificate on WPP-op ordinary quotient points. -/
structure OrdinaryDescendedQuotientFieldsW393
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop where
  injective : Function.Injective (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  inducing : IsInducing (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  closed_range : IsClosed (Set.range (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y))

/--
W352's ordinary concrete descended fields directly instantiate the W393
ordinary WPP-op quotient-field input.
-/
def descendedQuotientFieldsW352_to_ordinaryDescendedQuotientFieldsW393
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h :
      DescendedQuotientFieldsW352
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        ordinaryDescended) :
    OrdinaryDescendedQuotientFieldsW393 ordinaryDescended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/-- Machine-readable state for this adapter. -/
structure WppOpLeftLcaW352ToW393AdapterV370SupportState : Type where
  checkedFacts : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpLeftLcaW352ToW393AdapterV370SupportState :
    WppOpLeftLcaW352ToW393AdapterV370SupportState where
  checkedFacts :=
    ["descendedQuotientFieldsW352_to_ordinaryDescendedQuotientFieldsW393"]
  remainingInputs :=
    ["instantiate the W352 concrete descended quotient fields for the actual ordinary WPP-op map"]
  productSuccessClaimed := false

theorem currentWppOpLeftLcaW352ToW393AdapterV370SupportState_productSuccess :
    currentWppOpLeftLcaW352ToW393AdapterV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check DescendedQuotientFieldsW352
#check OrdinaryDescendedQuotientFieldsW393
#check descendedQuotientFieldsW352_to_ordinaryDescendedQuotientFieldsW393
#check currentWppOpLeftLcaW352ToW393AdapterV370SupportState_productSuccess

end Checks

end WppOpLeftLcaW352ToW393AdapterV370SupportParent

end LeanLCAExactChallenge
