import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W407: reverse relation-preimage support for the WPP-op relation-pullback route.

The W404 support file isolates the remaining relation-pullback input as the
reverse preimage statement through the ordinary codomain component.  This file
keeps that boundary explicit and reduces the input to the smallest checked
closed-range membership statement obtained by unfolding `cokernelSubgroup`.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationPullbackEqualityV370SupportW404

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W404 spelling of W389/W401's relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W404 spelling of the remaining reverse relation-preimage proposition. -/
abbrev relationPreimageReverseConditionW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/-- The commuting squares give the forward relation-preimage inclusion. -/
theorem relationPreimageForwardOfSquaresW404
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
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

/-- Reverse relation-preimage plus the two square equations gives the equality. -/
theorem relationPreimagePullbackConditionOfReverseW404
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW404 f g f' g' iB) :
    relationPreimagePullbackConditionW404 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · intro b hb
    exact relationPreimageForwardOfSquaresW404 iA iB hsquare_left hsquare_right b hb

/-- W389 relation-pullback equality certificate. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW404 f g f' g' iB

/--
Single-field package for the exact remaining input needed to build the W389
certificate by the reverse-preimage route.
-/
structure RelationPullbackReverseInputW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  reverse_relation_preimage : relationPreimageReverseConditionW404 f g f' g' iB

/-- The reverse-input package produces the W389 certificate once squares are supplied. -/
theorem RelationPullbackReverseInputW404.to_w389_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (h : RelationPullbackReverseInputW404 f g f' g' iA iB) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB where
  relation_pullback :=
    relationPreimagePullbackConditionOfReverseW404 iA iB
      hsquare_left hsquare_right h.reverse_relation_preimage

end ConcreteMetrizableLCA

end WppOpRelationPullbackEqualityV370SupportW404

namespace WppOpRelationReversePreimageV370SupportW407

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/--
The reverse-preimage condition with both `cokernelSubgroup`s unfolded to
closed algebraic ranges.
-/
abbrev relationReverseClosedRangeMembershipW407
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ b : B,
    iB b ∈
        (AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure →
      b ∈
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure

/-- The W407 closed-range membership spelling is definitionally W404's reverse input. -/
theorem relationReverseClosedRangeMembership_iff_w404_reverse
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B') :
    relationReverseClosedRangeMembershipW407 f g f' g' iB ↔
      LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationPreimageReverseConditionW404
        f g f' g' iB := by
  rfl

/-- Closed-range membership directly supplies W404's reverse input package. -/
theorem relationReverseClosedRangeMembership_to_w404_reverseInput
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h :
      relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404
      f g f' g' iA iB where
  reverse_relation_preimage :=
    (relationReverseClosedRangeMembership_iff_w404_reverse iB).mp h

/--
Checked consumer into W404's `to_w389_certificate`: the only mathematical input
is the unfolded reverse closed-range membership statement.
-/
theorem relationReverseClosedRangeMembership_to_w404_w389_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (h :
      relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
      f g f' g' iB :=
  LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404.to_w389_certificate
      hsquare_left hsquare_right
      (relationReverseClosedRangeMembership_to_w404_reverseInput h)

/--
Closed-range preimage equality is a stronger route: it immediately gives the
reverse closed-range membership condition.
-/
theorem relationReverseClosedRangeMembership_of_closedRangePreimageEquality
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h :
      AddSubgroup.comap iB.hom.toAddMonoidHom
          ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
            (⊤ : AddSubgroup A')).topologicalClosure) =
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure) :
    relationReverseClosedRangeMembershipW407 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈
        AddSubgroup.comap iB.hom.toAddMonoidHom
          ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
            (⊤ : AddSubgroup A')).topologicalClosure) := hb
  simpa [relationReverseClosedRangeMembershipW407] using h ▸ hbcomap

/--
Closed-range preimage equality therefore also feeds W404's W389 certificate
through the reverse-preimage route.
-/
theorem closedRangePreimageEquality_to_w404_w389_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (h :
      AddSubgroup.comap iB.hom.toAddMonoidHom
          ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
            (⊤ : AddSubgroup A')).topologicalClosure) =
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
      f g f' g' iB :=
  relationReverseClosedRangeMembership_to_w404_w389_certificate
    hsquare_left hsquare_right
    (relationReverseClosedRangeMembership_of_closedRangePreimageEquality h)

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

/-- WPP-op closed-range membership spelling of the reverse-preimage input. -/
abbrev WppOpRelationReverseClosedRangeMembershipW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationReverseClosedRangeMembershipW407
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

/-- W407 closed-range membership gives the W404 reverse-preimage input package. -/
theorem WppOpRelationReverseClosedRangeMembershipW407.to_w404_reverseInput
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationReverseClosedRangeMembershipW407 α) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α) :=
  ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_reverseInput h

/-- W407 closed-range membership feeds W404's W389 certificate through naturality squares. -/
theorem WppOpRelationReverseClosedRangeMembershipW407.to_w404_w389_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationReverseClosedRangeMembershipW407 α) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        (wppOpOrdinaryCodomainMap α) :=
  ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_w389_certificate
    (wppOpLeftSquareEquationW407 α) (wppOpRightSquareEquationW407 α) h

/-- Machine-readable W407 state. -/
structure WppOpRelationReversePreimageV370SupportStateW407 : Type where
  seed : String
  checkedFacts : List String
  relationReversePreimageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationReversePreimageV370SupportStateW407 :
    WppOpRelationReversePreimageV370SupportStateW407 where
  seed := "1WmpKdhFlGDCltNQ3zhX9Pae"
  checkedFacts :=
    ["ConcreteMetrizableLCA.relationReverseClosedRangeMembership_iff_w404_reverse",
      "ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_reverseInput",
      "ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_w389_certificate",
      "ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality",
      "ConcreteMetrizableLCA.closedRangePreimageEquality_to_w404_w389_certificate",
      "WppOpRelationReverseClosedRangeMembershipW407.to_w404_reverseInput",
      "WppOpRelationReverseClosedRangeMembershipW407.to_w404_w389_certificate"]
  relationReversePreimageResult := "partial"
  remainingInputs :=
    ["prove the unfolded closed-range membership statement for the concrete WPP-op morphism",
      "or prove the stronger closed-range preimage equality"]
  productSuccessClaimed := false

theorem currentWppOpRelationReversePreimageV370SupportStateW407_productSuccess :
    currentWppOpRelationReversePreimageV370SupportStateW407.productSuccessClaimed = false := rfl

section Checks

#check LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404.to_w389_certificate
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembershipW407
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_iff_w404_reverse
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_reverseInput
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_w389_certificate
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.closedRangePreimageEquality_to_w404_w389_certificate
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.WppOpRelationReverseClosedRangeMembershipW407.to_w404_reverseInput
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.WppOpRelationReverseClosedRangeMembershipW407.to_w404_w389_certificate
#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.currentWppOpRelationReversePreimageV370SupportStateW407_productSuccess

end Checks

end WppOpRelationReversePreimageV370SupportW407

end LeanLCAExactChallenge
