import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W415: reverse closed-range membership to relation-pullback support.

This standalone audit file packages the W407 -> W412 -> W399 route locally.
For ordinary arrows, reverse closed-range membership plus the two square
equations first gives the closed-range preimage equality; by unfolding
`cokernelSubgroup`, this is exactly the relation-pullback equality used by the
ordinary descended quotient topology input.  The result is then specialized to
`WalkingParallelPairᵒᵖ` diagrams using naturality.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

universe u

namespace MetrizableLCA

/-- W407 closed-range membership spelling of the reverse-preimage input. -/
abbrev relationReverseClosedRangeMembershipW407
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B,
    iB b ∈
        (AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure →
      b ∈
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure

/-- W409 closed-range preimage equality through the ordinary codomain component. -/
abbrev relationClosedRangePreimageEqualityW409
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- W399 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W399 closed-range spelling of the same relation-pullback equality. -/
abbrev relationClosedRangePreimageEqualityW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- W399's relation-pullback and closed-range spellings are definitionally equal. -/
theorem relationPreimagePullbackConditionIffClosedRangeEqualityW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW399 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW399 f g f' g' iB := by
  rfl

/-- Under square equations, the source closed range maps into the target closed range. -/
theorem relationClosedRangeForwardOfSquaresW412
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
        (⊤ : AddSubgroup A)).topologicalClosure ≤
      AddSubgroup.comap iB.hom.toAddMonoidHom
        ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure) := by
  let sourceRange : AddSubgroup B :=
    AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)
  let targetClosed : AddSubgroup B' :=
    (AddSubgroup.map (f' - g').hom.toAddMonoidHom
      (⊤ : AddSubgroup A')).topologicalClosure
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom targetClosed
  have hrange_le : sourceRange ≤ targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ targetClosed
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
    exact AddSubgroup.le_topologicalClosure _
      (show (f' - g') (iA a) ∈
        AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A') from
        ⟨iA a, trivial, rfl⟩)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (targetClosed : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  exact AddSubgroup.topologicalClosure_minimal sourceRange hrange_le htargetPreimage_closed

/--
W407 reverse closed-range membership and the square equations imply W412's
closed-range preimage equality.
-/
theorem relationClosedRangePreimageEquality_of_reverseMembership_and_squares
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    relationClosedRangePreimageEqualityW409 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · exact relationClosedRangeForwardOfSquaresW412 iA iB hsquare_left hsquare_right

/--
Primary ordinary theorem: W407 reverse closed-range membership plus the two
square equations gives W399's relation-pullback equality on `cokernelSubgroup`.
-/
theorem relationPreimagePullbackCondition_of_reverseMembership_and_squares
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    relationPreimagePullbackConditionW399 f g f' g' iB :=
  (relationPreimagePullbackConditionIffClosedRangeEqualityW399 iB).mpr
    (relationClosedRangePreimageEquality_of_reverseMembership_and_squares
      iA iB hsquare_left hsquare_right hreverse)

/-- W399 ordinary descended quotient topology input shape. -/
structure RelationPullbackDescendedFieldsInputsW399
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  relation_pullback : relationPreimagePullbackConditionW399 f g f' g' iB
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))

/--
Consumer into W399's ordinary input shape: after W415 supplies
`relation_pullback`, the remaining caller obligations are quotient
compatibility and closedness of the descended quotient map.
-/
theorem RelationPullbackDescendedFieldsInputsW399.of_reverseMembership
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB)
    (hquotient :
      quotientMap B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
        iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))
    (hclosed : IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))) :
    RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB descended where
  square_left := hsquare_left
  square_right := hsquare_right
  relation_pullback :=
    relationPreimagePullbackCondition_of_reverseMembership_and_squares
      iA iB hsquare_left hsquare_right hreverse
  quotient_compat := hquotient
  descended_closedMap := hclosed

end MetrizableLCA

namespace WppOpReverseMembershipToRelationPullbackV370SupportW415

open LeanLCAExactChallenge.MetrizableLCA

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

/-- Concrete WPP-op component at the ordinary source object. -/
abbrev wppOpOrdinaryDomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpDomain X ⟶ wppOpDomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero)

/-- Concrete WPP-op component at the ordinary target object. -/
abbrev wppOpOrdinaryCodomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpCodomain X ⟶ wppOpCodomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)

/-- WPP-op closed-range membership spelling of W407's reverse-preimage input. -/
abbrev WppOpRelationReverseClosedRangeMembershipW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  MetrizableLCA.relationReverseClosedRangeMembershipW407
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op relation-pullback equality through the ordinary codomain component. -/
abbrev WppOpRelationPreimagePullbackConditionW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  MetrizableLCA.relationPreimagePullbackConditionW399
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- The ordinary quotient point used by the WPP-op adapter. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- WPP-op left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW415
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation, from naturality. -/
theorem wppOpRightSquareEquationW415
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/--
WPP-op specialization: W407 reverse membership implies the ordinary
relation-pullback equality used by W399.
-/
theorem WppOpRelationReverseClosedRangeMembershipW407.to_relationPullbackW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationReverseClosedRangeMembershipW407 α) :
    WppOpRelationPreimagePullbackConditionW399 α :=
  MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW415 α) (wppOpRightSquareEquationW415 α) h

/-- WPP-op W399 ordinary input shape using naturality square equations. -/
abbrev WppOpRelationPullbackDescendedFieldsInputsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399
    (wppOpDomain X) (wppOpCodomain X)
    (wppOpDomain Y) (wppOpCodomain Y)
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    ordinaryDescended

/--
Checked WPP-op consumer into W399's relation/topology input shape.  W415 fills
the relation-pullback field; quotient compatibility and descended closed-map
evidence remain explicit inputs.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_reverseMembership
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (hreverse : WppOpRelationReverseClosedRangeMembershipW407 α)
    (hquotient :
      MetrizableLCA.quotientMap (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
        wppOpOrdinaryCodomainMap α ≫
          MetrizableLCA.quotientMap (wppOpCodomain Y)
            (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
            (AddSubgroup.isClosed_topologicalClosure _))
    (hclosed : IsClosedMap (ordinaryDescended :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)) :
    WppOpRelationPullbackDescendedFieldsInputsW399 α ordinaryDescended :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership
    (wppOpLeftSquareEquationW415 α) (wppOpRightSquareEquationW415 α)
    hreverse hquotient hclosed

/-- Machine-readable W415 state. -/
structure WppOpReverseMembershipToRelationPullbackV370SupportStateW415 : Type where
  seed : String
  checkedFacts : List String
  reverseMembershipToRelationPullbackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpReverseMembershipToRelationPullbackV370SupportStateW415 :
    WppOpReverseMembershipToRelationPullbackV370SupportStateW415 where
  seed := "286de6faabce6d651a3afdd4"
  checkedFacts :=
    ["MetrizableLCA.relationClosedRangeForwardOfSquaresW412",
      "MetrizableLCA.relationClosedRangePreimageEquality_of_reverseMembership_and_squares",
      "MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership",
      "WppOpRelationReverseClosedRangeMembershipW407.to_relationPullbackW399",
      "relationPullbackDescendedFieldsInputsW399_of_reverseMembership"]
  reverseMembershipToRelationPullbackResult := "proved"
  remainingInputs :=
    ["quotient compatibility for the ordinary descended quotient map",
      "IsClosedMap evidence for the ordinary descended quotient map"]
  productSuccessClaimed := false

theorem currentWppOpReverseMembershipToRelationPullbackV370SupportStateW415_productSuccess :
    currentWppOpReverseMembershipToRelationPullbackV370SupportStateW415.productSuccessClaimed =
      false := rfl

section Checks

#check MetrizableLCA.relationReverseClosedRangeMembershipW407
#check MetrizableLCA.relationClosedRangePreimageEqualityW409
#check MetrizableLCA.relationPreimagePullbackConditionW399
#check MetrizableLCA.relationClosedRangePreimageEquality_of_reverseMembership_and_squares
#check MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership
#check WppOpRelationReverseClosedRangeMembershipW407.to_relationPullbackW399
#check relationPullbackDescendedFieldsInputsW399_of_reverseMembership
#check currentWppOpReverseMembershipToRelationPullbackV370SupportStateW415_productSuccess

end Checks

end WppOpReverseMembershipToRelationPullbackV370SupportW415

end LeanLCAExactChallenge
