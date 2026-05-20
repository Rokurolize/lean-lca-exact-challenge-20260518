import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W412: closed-range preimage equality from W407 reverse membership.

This file sharpens W409's remaining closed-range preimage equality condition:
for ordinary arrows, the commuting square equations give the forward
closed-range inclusion, and W407's reverse closed-range membership gives the
opposite inclusion.  The result is then specialized to WPP-op diagrams using
the naturality square equations.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpClosedRangePreimageEqualityV370SupportW412

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W407 closed-range membership spelling of the reverse-preimage input. -/
abbrev relationReverseClosedRangeMembershipW407
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ b : B,
    iB b ∈
        (AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure →
      b ∈
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure

/-- W409 closed-range preimage equality through the ordinary codomain component. -/
abbrev relationClosedRangePreimageEqualityW409
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- Under square equations, the source closed range maps into the target closed range. -/
theorem relationClosedRangeForwardOfSquaresW412
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
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
W407 reverse closed-range membership and the square equations imply W409's
closed-range preimage equality.
-/
theorem relationClosedRangePreimageEquality_of_reverseMembership_and_squares
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    relationClosedRangePreimageEqualityW409 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · exact relationClosedRangeForwardOfSquaresW412 iA iB hsquare_left hsquare_right

/-- The equality immediately recovers W407 reverse membership. -/
theorem relationReverseClosedRangeMembership_of_closedRangePreimageEquality
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : relationClosedRangePreimageEqualityW409 f g f' g' iB) :
    relationReverseClosedRangeMembershipW407 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈
        AddSubgroup.comap iB.hom.toAddMonoidHom
          ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
            (⊤ : AddSubgroup A')).topologicalClosure) := hb
  simpa [relationClosedRangePreimageEqualityW409] using h ▸ hbcomap

/-- Under square equations, W407 membership is equivalent to W409 equality. -/
theorem relationClosedRangePreimageEquality_iff_reverseMembership_and_squares
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    relationClosedRangePreimageEqualityW409 f g f' g' iB ↔
      relationReverseClosedRangeMembershipW407 f g f' g' iB := by
  constructor
  · exact relationReverseClosedRangeMembership_of_closedRangePreimageEquality
  · exact relationClosedRangePreimageEquality_of_reverseMembership_and_squares
      iA iB hsquare_left hsquare_right

end ConcreteMetrizableLCA

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
  ConcreteMetrizableLCA.relationReverseClosedRangeMembershipW407
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op spelling of W409's closed-range preimage equality. -/
abbrev WppOpRelationClosedRangePreimageEqualityW409
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW409
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation, from naturality. -/
theorem wppOpRightSquareEquationW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/--
W407's WPP-op reverse closed-range membership implies W409's closed-range
preimage equality by naturality of the two WPP-op arrows.
-/
theorem WppOpRelationReverseClosedRangeMembershipW407.to_w409_closedRangePreimageEquality
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationReverseClosedRangeMembershipW407 α) :
    WppOpRelationClosedRangePreimageEqualityW409 α :=
  ConcreteMetrizableLCA.relationClosedRangePreimageEquality_of_reverseMembership_and_squares
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW407 α) (wppOpRightSquareEquationW407 α) h

/-- W409's WPP-op equality recovers W407's reverse closed-range membership. -/
theorem WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationClosedRangePreimageEqualityW409 α) :
    WppOpRelationReverseClosedRangeMembershipW407 α :=
  ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality h

/-- Checked two-way bridge between W407 membership and W409 equality for WPP-op diagrams. -/
theorem WppOpRelationClosedRangePreimageEqualityW409_iff_w407_membership
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    WppOpRelationClosedRangePreimageEqualityW409 α ↔
      WppOpRelationReverseClosedRangeMembershipW407 α := by
  constructor
  · exact WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership
  · exact WppOpRelationReverseClosedRangeMembershipW407.to_w409_closedRangePreimageEquality

/-- Machine-readable W412 state. -/
structure WppOpClosedRangePreimageEqualityV370SupportStateW412 : Type where
  seed : String
  checkedFacts : List String
  closedRangePreimageEqualityResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpClosedRangePreimageEqualityV370SupportStateW412 :
    WppOpClosedRangePreimageEqualityV370SupportStateW412 where
  seed := "beam-citrine-7429"
  checkedFacts :=
    ["ConcreteMetrizableLCA.relationClosedRangeForwardOfSquaresW412",
      "ConcreteMetrizableLCA.relationClosedRangePreimageEquality_of_reverseMembership_and_squares",
      "ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality",
      "ConcreteMetrizableLCA.relationClosedRangePreimageEquality_iff_reverseMembership_and_squares",
      "WppOpRelationReverseClosedRangeMembershipW407.to_w409_closedRangePreimageEquality",
      "WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership",
      "WppOpRelationClosedRangePreimageEqualityW409_iff_w407_membership"]
  closedRangePreimageEqualityResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentWppOpClosedRangePreimageEqualityV370SupportStateW412_productSuccess :
    currentWppOpClosedRangePreimageEqualityV370SupportStateW412.productSuccessClaimed = false := rfl

section Checks

#check ConcreteMetrizableLCA.relationReverseClosedRangeMembershipW407
#check ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW409
#check ConcreteMetrizableLCA.relationClosedRangeForwardOfSquaresW412
#check ConcreteMetrizableLCA.relationClosedRangePreimageEquality_of_reverseMembership_and_squares
#check ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality
#check ConcreteMetrizableLCA.relationClosedRangePreimageEquality_iff_reverseMembership_and_squares
#check WppOpRelationReverseClosedRangeMembershipW407.to_w409_closedRangePreimageEquality
#check WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership
#check WppOpRelationClosedRangePreimageEqualityW409_iff_w407_membership
#check currentWppOpClosedRangePreimageEqualityV370SupportStateW412_productSuccess

end Checks

end WppOpClosedRangePreimageEqualityV370SupportW412

end LeanLCAExactChallenge
