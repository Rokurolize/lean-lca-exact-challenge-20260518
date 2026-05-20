import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W409: WPP-op closed-range membership support.

This file keeps the W407 closed-range membership boundary checked and exposes
the smallest stronger premise used by the current W404/W389 relation-pullback
route: equality of the closed-range preimage through the ordinary codomain
component.

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

/-- Closed-range spelling of the same pullback equality. -/
abbrev relationClosedRangePreimageEqualityW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)).topologicalClosure

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

/-- Single-field reverse-preimage input. -/
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

/-- W380 component-closedness certificate, restated in W401's shape. -/
structure ComponentClosedMapCertificateW380 (iB : B ⟶ B') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')

/-- Closed embedding gives the W380 component-closedness certificate. -/
theorem ComponentClosedMapCertificateW380.of_closedEmbedding
    {iB : B ⟶ B'} (hiB : IsClosedEmbedding (iB : B → B')) :
    ComponentClosedMapCertificateW380 iB where
  component_closedMap := hiB.isClosedMap

/-- W392/W386 target-relation lift certificate, restated in W401's shape. -/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts :
    ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
      ∃ d : B, iB d = n

/-- W401 relation-field package. -/
structure ConcreteQuotientClosedMapRelationFieldsW401
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW404 f g f' g' iB
  target_relation_lifts :
    ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
      ∃ d : B, iB d = n

/-- Concrete W401 composer from W380, W389, and W392 certificates. -/
theorem relationFields_of_w380_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW401 f g f' g' iA iB where
  component_closedMap := hclosed.component_closedMap
  relation_pullback := hpullback.relation_pullback
  target_relation_lifts := htarget.target_relation_lifts

end ConcreteMetrizableLCA

end WppOpRelationPullbackEqualityV370SupportW404

namespace WppOpRelationReversePreimageV370SupportW407

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

/-- Closed-range membership directly supplies W404's reverse input package. -/
theorem relationReverseClosedRangeMembership_to_w404_reverseInput
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h :
      relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404
      f g f' g' iA iB where
  reverse_relation_preimage := h

/-- Checked consumer into W404's `to_w389_certificate`. -/
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

/-- Closed-range preimage equality is a stronger route to W407 membership. -/
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

end ConcreteMetrizableLCA

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

/-- W407 closed-range membership feeds W404's W389 certificate through naturality squares. -/
theorem WppOpRelationReverseClosedRangeMembershipW407.to_w404_w389_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationReverseClosedRangeMembershipW407 α) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        (wppOpOrdinaryCodomainMap α) :=
  ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_w389_certificate
    (wppOpLeftSquareEquationW407 α) (wppOpRightSquareEquationW407 α) h

end WppOpRelationReversePreimageV370SupportW407

namespace WppOpClosedRangeMembershipV370SupportW409

open LeanLCAExactChallenge.MetrizableLCA
open LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/--
The closed-range preimage equality isolated as the strongest checked local
premise for W407's reverse membership statement.
-/
abbrev relationClosedRangePreimageEqualityW409
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- Closed-range preimage equality gives W407's unfolded membership statement. -/
theorem relationClosedRangePreimageEquality_to_w407_membership
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : relationClosedRangePreimageEqualityW409 f g f' g' iB) :
    LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembershipW407
      f g f' g' iB :=
  LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_of_closedRangePreimageEquality h

/--
The W409 premise feeds W407's checked consumer into W404/W389 once square
equations are supplied.
-/
theorem relationClosedRangePreimageEquality_to_w404_w389_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (h : relationClosedRangePreimageEqualityW409 f g f' g' iB) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
      f g f' g' iB :=
  LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.ConcreteMetrizableLCA.relationReverseClosedRangeMembership_to_w404_w389_certificate
    hsquare_left hsquare_right
    (relationClosedRangePreimageEquality_to_w407_membership h)

/-- W409's closed-range equality is exactly the W404 closed-range equality spelling. -/
theorem relationClosedRangePreimageEquality_iff_w404_closedRange
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B') :
    relationClosedRangePreimageEqualityW409 f g f' g' iB ↔
      LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW404
        f g f' g' iB := by
  rfl

end ConcreteMetrizableLCA

/-- WPP-op spelling of the W409 closed-range preimage equality premise. -/
abbrev WppOpRelationClosedRangePreimageEqualityW409
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW409
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- The W409 WPP-op premise gives W407's closed-range membership condition. -/
theorem WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationClosedRangePreimageEqualityW409 α) :
    WppOpRelationReverseClosedRangeMembershipW407 α :=
  ConcreteMetrizableLCA.relationClosedRangePreimageEquality_to_w407_membership h

/-- Checked consumer through W407 into W404's W389 certificate. -/
theorem WppOpRelationClosedRangePreimageEqualityW409.to_w404_w389_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationClosedRangePreimageEqualityW409 α) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        (wppOpOrdinaryCodomainMap α) :=
  (WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership h).to_w404_w389_certificate

/-- Checked W401-shaped relation-field consumer, when W380 and W392 inputs are also supplied. -/
theorem WppOpRelationClosedRangePreimageEqualityW409.to_w401_relation_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hclosedRange : WppOpRelationClosedRangePreimageEqualityW409 α)
    (htarget :
      LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
        (wppOpLeft Y) (wppOpRight Y) (wppOpOrdinaryCodomainMap α)) :
    LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW401
        (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
        (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α) :=
  LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationFields_of_w380_w389_w392
    (LeanLCAExactChallenge.WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.ComponentClosedMapCertificateW380.of_closedEmbedding
      (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)))
    (WppOpRelationClosedRangePreimageEqualityW409.to_w404_w389_certificate hclosedRange)
    htarget

/-- Machine-readable W409 state. -/
structure WppOpClosedRangeMembershipV370SupportStateW409 : Type where
  seed : String
  checkedFacts : List String
  closedRangeMembershipResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpClosedRangeMembershipV370SupportStateW409 :
    WppOpClosedRangeMembershipV370SupportStateW409 where
  seed := "d207df574b3a0ebbd2652bab39ee674d"
  checkedFacts :=
    ["ConcreteMetrizableLCA.relationClosedRangePreimageEquality_to_w407_membership",
      "ConcreteMetrizableLCA.relationClosedRangePreimageEquality_to_w404_w389_certificate",
      "ConcreteMetrizableLCA.relationClosedRangePreimageEquality_iff_w404_closedRange",
      "WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership",
      "WppOpRelationClosedRangePreimageEqualityW409.to_w404_w389_certificate",
      "WppOpRelationClosedRangePreimageEqualityW409.to_w401_relation_fields"]
  closedRangeMembershipResult := "partial"
  remainingInputs :=
    ["prove WppOpRelationClosedRangePreimageEqualityW409 for the concrete WPP-op morphism",
      "equivalently, prove W407's WppOpRelationReverseClosedRangeMembershipW407 directly"]
  productSuccessClaimed := false

theorem currentWppOpClosedRangeMembershipV370SupportStateW409_productSuccess :
    currentWppOpClosedRangeMembershipV370SupportStateW409.productSuccessClaimed = false := rfl

section Checks

#check LeanLCAExactChallenge.WppOpRelationReversePreimageV370SupportW407.WppOpRelationReverseClosedRangeMembershipW407.to_w404_w389_certificate
#check ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW409
#check ConcreteMetrizableLCA.relationClosedRangePreimageEquality_to_w407_membership
#check ConcreteMetrizableLCA.relationClosedRangePreimageEquality_to_w404_w389_certificate
#check ConcreteMetrizableLCA.relationClosedRangePreimageEquality_iff_w404_closedRange
#check WppOpRelationClosedRangePreimageEqualityW409.to_w407_membership
#check WppOpRelationClosedRangePreimageEqualityW409.to_w404_w389_certificate
#check WppOpRelationClosedRangePreimageEqualityW409.to_w401_relation_fields
#check currentWppOpClosedRangeMembershipV370SupportStateW409_productSuccess

end Checks

end WppOpClosedRangeMembershipV370SupportW409

end LeanLCAExactChallenge
