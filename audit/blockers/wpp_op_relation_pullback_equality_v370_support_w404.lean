import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W404: WPP-op relation-pullback equality support.

This file sharpens W389's boundary.  It checks constructors for the W389
relation-pullback equality certificate from either of the two isolated remaining
mathematical inputs:

* reverse relation-preimage through the ordinary codomain component;
* the definitionally equivalent closed-range preimage equality.

It also supplies W401-shaped consumers into the relation-field and W371-input
routes.  The file leaves the reverse-preimage or closed-range equality as an
explicit caller input and makes no product-completion claim.
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

/--
Closed-range spelling of the same pullback equality.  This unfolds the two
`cokernelSubgroup` terms to the topological closures of algebraic ranges.
-/
abbrev relationClosedRangePreimageEqualityW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)).topologicalClosure

/-- The two closed-range and cokernel-subgroup spellings are definitionally equal. -/
theorem relationPreimagePullbackConditionIffClosedRangeEqualityW404
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B') :
    relationPreimagePullbackConditionW404 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW404 f g f' g' iB := by
  rfl

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

/-- The pullback equality immediately recovers the reverse elementwise form. -/
theorem relationPreimageReverseOfPullbackConditionW404
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW404 f g f' g' iB) :
    relationPreimageReverseConditionW404 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackConditionW404] using (hpullback ▸ hbcomap)

/-- Under square equations, equality and reverse-preimage are equivalent. -/
theorem relationPreimagePullbackConditionIffReverseW404
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    relationPreimagePullbackConditionW404 f g f' g' iB ↔
      relationPreimageReverseConditionW404 f g f' g' iB := by
  constructor
  · exact relationPreimageReverseOfPullbackConditionW404 iB
  · exact relationPreimagePullbackConditionOfReverseW404 iA iB hsquare_left hsquare_right

/-- W389 relation-pullback equality certificate. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW404 f g f' g' iB

/-- The certificate is exactly the W401 relation-pullback field. -/
theorem RelationPullbackEqualityCertificateW389.to_w401_relation_pullback
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    relationPreimagePullbackConditionW404 f g f' g' iB :=
  h.relation_pullback

/-- Construct the W389 certificate from the reverse-preimage proposition. -/
theorem RelationPullbackEqualityCertificateW389.of_reverse
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW404 f g f' g' iB) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB where
  relation_pullback :=
    relationPreimagePullbackConditionOfReverseW404 iA iB
      hsquare_left hsquare_right hreverse

/-- Construct the W389 certificate from the closed-range preimage equality. -/
theorem RelationPullbackEqualityCertificateW389.of_closedRangeEquality
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (hclosedRange : relationClosedRangePreimageEqualityW404 f g f' g' iB) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB where
  relation_pullback :=
    (relationPreimagePullbackConditionIffClosedRangeEqualityW404 iB).mpr hclosedRange

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
    RelationPullbackEqualityCertificateW389 f g f' g' iB :=
  RelationPullbackEqualityCertificateW389.of_reverse
    hsquare_left hsquare_right h.reverse_relation_preimage

/--
Single-field package for the exact remaining input needed to build the W389
certificate by the closed-range route.
-/
structure RelationPullbackClosedRangeInputW404
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  closed_range_preimage_equality : relationClosedRangePreimageEqualityW404 f g f' g' iB

/-- The closed-range package produces the W389 certificate directly. -/
theorem RelationPullbackClosedRangeInputW404.to_w389_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : RelationPullbackClosedRangeInputW404 f g f' g' iB) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB :=
  RelationPullbackEqualityCertificateW389.of_closedRangeEquality
    h.closed_range_preimage_equality

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

/-- W401 W371 input package after the two square equations are fixed. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (_hsquare_left : f ≫ iB = iA ≫ f')
    (_hsquare_right : g ≫ iB = iA ≫ g') : Prop where
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
  relation_pullback := hpullback.to_w401_relation_pullback
  target_relation_lifts := htarget.target_relation_lifts

/-- Concrete W401 route from the reverse-preimage input package. -/
theorem relationFields_of_w380_reverse_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hreverse : RelationPullbackReverseInputW404 f g f' g' iA iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW401 f g f' g' iA iB :=
  relationFields_of_w380_w389_w392 hclosed
    (hreverse.to_w389_certificate hsquare_left hsquare_right) htarget

/-- Concrete W401 route from the closed-range input package. -/
theorem relationFields_of_w380_closedRange_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hclosedRange : RelationPullbackClosedRangeInputW404 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW401 f g f' g' iA iB :=
  relationFields_of_w380_w389_w392 hclosed
    hclosedRange.to_w389_certificate htarget

/-- W401 fields project to the W371 input package once squares are supplied. -/
theorem ConcreteQuotientClosedMapRelationFieldsW401.to_w371_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRelationFieldsW401 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- Direct concrete W401 W371 route from W380, W389, and W392 certificates. -/
theorem w371Inputs_of_w380_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right :=
  (relationFields_of_w380_w389_w392 hclosed hpullback htarget).to_w371_inputs

/-- Direct concrete W401 W371 route from the reverse-preimage input package. -/
theorem w371Inputs_of_w380_reverse_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hreverse : RelationPullbackReverseInputW404 f g f' g' iA iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right :=
  (relationFields_of_w380_reverse_w392
    hsquare_left hsquare_right hclosed hreverse htarget).to_w371_inputs

/-- Direct concrete W401 W371 route from the closed-range input package. -/
theorem w371Inputs_of_w380_closedRange_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hclosedRange : RelationPullbackClosedRangeInputW404 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right :=
  (relationFields_of_w380_closedRange_w392 hclosed hclosedRange htarget).to_w371_inputs

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

/-- WPP-op relation-pullback equality through the ordinary codomain component. -/
abbrev WppOpRelationPreimagePullbackConditionW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationPreimagePullbackConditionW404
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op reverse relation-preimage condition. -/
abbrev WppOpRelationPreimageReverseConditionW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationPreimageReverseConditionW404
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op closed-range preimage equality through the ordinary codomain component. -/
abbrev WppOpRelationClosedRangePreimageEqualityW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW404
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W389 relation-pullback equality certificate. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W380 component-closedness certificate. -/
abbrev WppOpComponentClosedMapCertificateW380
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ComponentClosedMapCertificateW380
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W392/W386 target-relation lift certificate. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W401 relation-field package. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW401
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW401
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation, from naturality. -/
theorem wppOpRightSquareEquationW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- WPP-op W371 input package using naturality square equations. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW404 α)
    (wppOpRightSquareEquationW404 α)

/-- WPP-op single-field reverse-preimage input package. -/
structure WppOpRelationPullbackReverseInputW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop where
  reverse_relation_preimage : WppOpRelationPreimageReverseConditionW404 α

/-- WPP-op single-field closed-range input package. -/
structure WppOpRelationPullbackClosedRangeInputW404
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop where
  closed_range_preimage_equality : WppOpRelationClosedRangePreimageEqualityW404 α

/-- Objectwise closed embeddings supply the W380 component-closedness certificate. -/
theorem WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    WppOpComponentClosedMapCertificateW380 α :=
  ConcreteMetrizableLCA.ComponentClosedMapCertificateW380.of_closedEmbedding
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))

/-- WPP-op reverse-preimage input produces the W389 certificate. -/
theorem WppOpRelationPullbackReverseInputW404.to_w389_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationPullbackReverseInputW404 α) :
    WppOpRelationPullbackEqualityCertificateW389 α :=
  ConcreteMetrizableLCA.RelationPullbackReverseInputW404.to_w389_certificate
    (wppOpLeftSquareEquationW404 α)
    (wppOpRightSquareEquationW404 α)
    { reverse_relation_preimage := h.reverse_relation_preimage }

/-- WPP-op closed-range input produces the W389 certificate. -/
theorem WppOpRelationPullbackClosedRangeInputW404.to_w389_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationPullbackClosedRangeInputW404 α) :
    WppOpRelationPullbackEqualityCertificateW389 α :=
  ConcreteMetrizableLCA.RelationPullbackClosedRangeInputW404.to_w389_certificate
    { closed_range_preimage_equality := h.closed_range_preimage_equality }

/-- WPP-op W401 composition of W380, W389, and W392 into relation fields. -/
theorem relationFields_of_w380_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed : WppOpComponentClosedMapCertificateW380 α)
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW401 α :=
  ConcreteMetrizableLCA.relationFields_of_w380_w389_w392 hclosed hpullback htarget

/-- WPP-op W401 route from objectwise closed embeddings and reverse-preimage input. -/
theorem relationFields_of_objectwise_closedEmbedding_reverse_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hreverse : WppOpRelationPullbackReverseInputW404 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW401 α :=
  relationFields_of_w380_w389_w392
    (WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding α hclosed)
    hreverse.to_w389_certificate
    htarget

/-- WPP-op W401 route from objectwise closed embeddings and closed-range input. -/
theorem relationFields_of_objectwise_closedEmbedding_closedRange_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hclosedRange : WppOpRelationPullbackClosedRangeInputW404 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW401 α :=
  relationFields_of_w380_w389_w392
    (WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding α hclosed)
    hclosedRange.to_w389_certificate
    htarget

/-- WPP-op W371 route from W380, W389, and W392 certificates. -/
theorem w371Inputs_of_w380_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed : WppOpComponentClosedMapCertificateW380 α)
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  ConcreteMetrizableLCA.w371Inputs_of_w380_w389_w392 hclosed hpullback htarget

/-- WPP-op W371 route from objectwise closed embeddings and reverse-preimage input. -/
theorem w371Inputs_of_objectwise_closedEmbedding_reverse_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hreverse : WppOpRelationPullbackReverseInputW404 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  w371Inputs_of_w380_w389_w392
    (WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding α hclosed)
    hreverse.to_w389_certificate
    htarget

/-- WPP-op W371 route from objectwise closed embeddings and closed-range input. -/
theorem w371Inputs_of_objectwise_closedEmbedding_closedRange_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hclosedRange : WppOpRelationPullbackClosedRangeInputW404 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  w371Inputs_of_w380_w389_w392
    (WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding α hclosed)
    hclosedRange.to_w389_certificate
    htarget

/-- Machine-readable W404 state. -/
structure WppOpRelationPullbackEqualityV370SupportStateW404 : Type where
  seed : String
  checkedFacts : List String
  relationPullbackEqualityResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationPullbackEqualityV370SupportStateW404 :
    WppOpRelationPullbackEqualityV370SupportStateW404 where
  seed := "8e6028be-be73-4a65-8517-641c3d991783"
  checkedFacts :=
    ["ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.of_reverse",
      "ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.of_closedRangeEquality",
      "ConcreteMetrizableLCA.RelationPullbackReverseInputW404.to_w389_certificate",
      "ConcreteMetrizableLCA.RelationPullbackClosedRangeInputW404.to_w389_certificate",
      "ConcreteMetrizableLCA.relationFields_of_w380_reverse_w392",
      "ConcreteMetrizableLCA.relationFields_of_w380_closedRange_w392",
      "ConcreteMetrizableLCA.w371Inputs_of_w380_reverse_w392",
      "ConcreteMetrizableLCA.w371Inputs_of_w380_closedRange_w392",
      "WppOpRelationPullbackReverseInputW404.to_w389_certificate",
      "WppOpRelationPullbackClosedRangeInputW404.to_w389_certificate",
      "relationFields_of_objectwise_closedEmbedding_reverse_w392",
      "relationFields_of_objectwise_closedEmbedding_closedRange_w392",
      "w371Inputs_of_objectwise_closedEmbedding_reverse_w392",
      "w371Inputs_of_objectwise_closedEmbedding_closedRange_w392"]
  relationPullbackEqualityResult := "partial"
  remainingInputs :=
    ["reverse relation-preimage through the ordinary codomain component",
      "or the equivalent closed-range preimage equality",
      "target relation lift certificate remains supplied by W392/W386"]
  productSuccessClaimed := false

theorem currentWppOpRelationPullbackEqualityV370SupportStateW404_productSuccess :
    currentWppOpRelationPullbackEqualityV370SupportStateW404.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationPreimagePullbackConditionW404
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationPreimageReverseConditionW404
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationClosedRangePreimageEqualityW404
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW404
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationPreimagePullbackConditionIffReverseW404
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.of_reverse
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.of_closedRangeEquality
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackReverseInputW404.to_w389_certificate
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.RelationPullbackClosedRangeInputW404.to_w389_certificate
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationFields_of_w380_reverse_w392
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.relationFields_of_w380_closedRange_w392
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.w371Inputs_of_w380_reverse_w392
#check WppOpRelationPullbackEqualityV370SupportW404.ConcreteMetrizableLCA.w371Inputs_of_w380_closedRange_w392
#check WppOpRelationPullbackEqualityV370SupportW404.WppOpRelationPullbackReverseInputW404.to_w389_certificate
#check WppOpRelationPullbackEqualityV370SupportW404.WppOpRelationPullbackClosedRangeInputW404.to_w389_certificate
#check WppOpRelationPullbackEqualityV370SupportW404.relationFields_of_objectwise_closedEmbedding_reverse_w392
#check WppOpRelationPullbackEqualityV370SupportW404.relationFields_of_objectwise_closedEmbedding_closedRange_w392
#check WppOpRelationPullbackEqualityV370SupportW404.w371Inputs_of_objectwise_closedEmbedding_reverse_w392
#check WppOpRelationPullbackEqualityV370SupportW404.w371Inputs_of_objectwise_closedEmbedding_closedRange_w392
#check WppOpRelationPullbackEqualityV370SupportW404.currentWppOpRelationPullbackEqualityV370SupportStateW404_productSuccess

end Checks

end WppOpRelationPullbackEqualityV370SupportW404

end LeanLCAExactChallenge
