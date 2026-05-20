import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W405: quotient compatibility for the ordinary descended quotient map.

This standalone audit file isolates the W402 `quotient_compat` field and proves
it for the concrete map induced by `ordinaryMap.app WalkingParallelPair.one`.
The remaining concrete fields are repackaged as relation-pullback equality and
closed-map inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

universe u

/-- W399/W402 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW405
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem relationPreimageForwardOfSquaresW405
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    ∀ b : B, b ∈ cokernelSubgroup (f - g) →
      iB b ∈ cokernelSubgroup (f' - g') := by
  intro b hb
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g'))
  have hrange_le :
      AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤
        targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ cokernelSubgroup (f' - g')
    have hleft : iB (f a) = f' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_left
    have hright : iB (g a) = g' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_right
    have hval : iB ((f - g) a) = (f' - g') (iA a) := by
      calc
        iB ((f - g) a) = iB (f a - g a) := by rfl
        _ = iB (f a) - iB (g a) := by
          exact map_sub iB.hom.toAddMonoidHom (f a) (g a)
        _ = f' (iA a) - g' (iA a) := by rw [hleft, hright]
        _ = (f' - g') (iA a) := by rfl
    rw [hval]
    exact map_mem_cokernelSubgroup (f' - g') (iA a)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (cokernelSubgroup (f' - g') : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  have hclosure_le : cokernelSubgroup (f - g) ≤ targetPreimage :=
    AddSubgroup.topologicalClosure_minimal
      (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A))
      hrange_le htargetPreimage_closed
  exact hclosure_le hb

/-- Kernel condition needed to descend the ordinary component map through quotient objects. -/
theorem ordinaryDescendedTargetKernel_leW405
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    cokernelSubgroup (f - g) ≤
      (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact relationPreimageForwardOfSquaresW405 iA iB hsquare_left hsquare_right b hb

/-- The concrete ordinary descended quotient map induced by compatible component squares. -/
def ordinaryDescendedQuotientMapW405
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientObj B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW405 iA iB hsquare_left hsquare_right)

/-- The concrete ordinary descended quotient map satisfies W402's quotient-compatibility field. -/
theorem ordinaryDescendedQuotientMap_quotient_compatW405
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedQuotientMapW405 iA iB hsquare_left hsquare_right =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift_quotientMap B (cokernelSubgroup (f - g))
    (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW405 iA iB hsquare_left hsquare_right)

end MetrizableLCA

namespace WppOpLeftLcaOrdinaryDescendedConcreteInputsV370SupportW402

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpOrdinaryDiagram (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

abbrev wppOpDomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.zero

abbrev wppOpCodomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.one

abbrev wppOpLeft (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.left

abbrev wppOpRight (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.right

abbrev wppOpOrdinaryQuotientPoint (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- Minimal W402-shaped concrete input package. -/
structure OrdinaryDescendedConcreteInputsW402
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) : Prop where
  relation_pullback : MetrizableLCA.relationPreimagePullbackConditionW405
    (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)
  quotient_compat :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)

theorem ordinarySquareLeftW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpLeft X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simpa [wppOpLeft] using ordinaryMap.naturality WalkingParallelPairHom.left

theorem ordinarySquareRightW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpRight X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simpa [wppOpRight] using ordinaryMap.naturality WalkingParallelPairHom.right

end WppOpLeftLcaOrdinaryDescendedConcreteInputsV370SupportW402

namespace WppOpLeftLcaOrdinaryDescendedQuotientCompatV370SupportW405

open WppOpLeftLcaOrdinaryDescendedConcreteInputsV370SupportW402

/-- The ordinary descended quotient map induced by `ordinaryMap.app WalkingParallelPair.one`. -/
def ordinaryDescendedOfOrdinaryMapW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y :=
  MetrizableLCA.ordinaryDescendedQuotientMapW405
    (ordinaryMap.app WalkingParallelPair.zero)
    (ordinaryMap.app WalkingParallelPair.one)
    (ordinarySquareLeftW405 ordinaryMap)
    (ordinarySquareRightW405 ordinaryMap)

/-- W402 quotient compatibility for the ordinary descended map induced by the ordinary component map. -/
theorem ordinaryDescendedOfOrdinaryMap_quotient_compatW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedOfOrdinaryMapW405 ordinaryMap =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) := by
  simpa [ordinaryDescendedOfOrdinaryMapW405] using
    MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW405
      (ordinaryMap.app WalkingParallelPair.zero)
      (ordinaryMap.app WalkingParallelPair.one)
      (ordinarySquareLeftW405 ordinaryMap)
      (ordinarySquareRightW405 ordinaryMap)

/--
Checked W405 input package after quotient compatibility has been discharged.
Only relation pullback and closed-map evidence remain external.
-/
structure OrdinaryDescendedConcreteInputsWithoutQuotientCompatW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  relation_pullback : MetrizableLCA.relationPreimagePullbackConditionW405
    (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)
  descended_closedMap : IsClosedMap (ordinaryDescendedOfOrdinaryMapW405 ordinaryMap :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)

/-- Consumer into W402's ordinary concrete input package. -/
def ordinaryConcreteInputsW402_of_withoutQuotientCompatW405
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : OrdinaryDescendedConcreteInputsWithoutQuotientCompatW405 ordinaryMap) :
    OrdinaryDescendedConcreteInputsW402 ordinaryMap
      (ordinaryDescendedOfOrdinaryMapW405 ordinaryMap) where
  relation_pullback := h.relation_pullback
  quotient_compat := ordinaryDescendedOfOrdinaryMap_quotient_compatW405 ordinaryMap
  descended_closedMap := h.descended_closedMap

/-- Remaining ordinary descended inputs after W405 proves quotient compatibility. -/
def remainingOrdinaryDescendedInputsAfterQuotientCompatW405 : List String :=
  ["prove the concrete relation-pullback equality, equivalently reverse preimage or closed-range preimage equality",
    "prove IsClosedMap for the ordinary descended quotient map"]

theorem remainingOrdinaryDescendedInputsAfterQuotientCompatW405_count :
    remainingOrdinaryDescendedInputsAfterQuotientCompatW405.length = 2 := rfl

/-- Declaration names exported by this W405 support layer. -/
def w405SupportDeclarationNames : List String :=
  ["MetrizableLCA.relationPreimagePullbackConditionW405",
    "MetrizableLCA.relationPreimageForwardOfSquaresW405",
    "MetrizableLCA.ordinaryDescendedTargetKernel_leW405",
    "MetrizableLCA.ordinaryDescendedQuotientMapW405",
    "MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW405",
    "ordinaryDescendedOfOrdinaryMapW405",
    "ordinaryDescendedOfOrdinaryMap_quotient_compatW405",
    "OrdinaryDescendedConcreteInputsWithoutQuotientCompatW405",
    "ordinaryConcreteInputsW402_of_withoutQuotientCompatW405",
    "remainingOrdinaryDescendedInputsAfterQuotientCompatW405"]

theorem w405SupportDeclarationNames_count :
    w405SupportDeclarationNames.length = 10 := rfl

structure WppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryDescendedQuotientCompatResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405 :
    WppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405 where
  seed := "w405-0d77ff99069b97de5cd994cc2a75bac9"
  checkedFacts :=
    ["isolated W402's quotient_compat field as the quotient projection equation",
      "defined the ordinary descended quotient map from ordinaryMap.app WalkingParallelPair.one via quotientLift",
      "proved the quotient compatibility equation for that concrete descended map",
      "provided a consumer into the W402-shaped OrdinaryDescendedConcreteInputsW402 package with only relation_pullback and descended_closedMap remaining"]
  remainingInputs := remainingOrdinaryDescendedInputsAfterQuotientCompatW405
  ordinaryDescendedQuotientCompatResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405_productSuccess :
    currentWppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405.productSuccessClaimed = false := rfl

section Checks

#check MetrizableLCA.relationPreimagePullbackConditionW405
#check MetrizableLCA.relationPreimageForwardOfSquaresW405
#check MetrizableLCA.ordinaryDescendedTargetKernel_leW405
#check MetrizableLCA.ordinaryDescendedQuotientMapW405
#check MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW405
#check OrdinaryDescendedConcreteInputsW402
#check ordinaryDescendedOfOrdinaryMapW405
#check ordinaryDescendedOfOrdinaryMap_quotient_compatW405
#check OrdinaryDescendedConcreteInputsWithoutQuotientCompatW405
#check ordinaryConcreteInputsW402_of_withoutQuotientCompatW405
#check remainingOrdinaryDescendedInputsAfterQuotientCompatW405
#check remainingOrdinaryDescendedInputsAfterQuotientCompatW405_count
#check w405SupportDeclarationNames
#check w405SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405
#check currentWppOpLeftLcaOrdinaryDescendedQuotientCompatV370StateW405_productSuccess

end Checks

end WppOpLeftLcaOrdinaryDescendedQuotientCompatV370SupportW405

end LeanLCAExactChallenge
