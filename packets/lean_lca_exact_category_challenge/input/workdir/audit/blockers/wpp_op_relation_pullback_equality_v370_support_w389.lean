import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W389: WPP-op relation-pullback equality support.

This standalone audit file isolates the remaining relation-pullback equality
through the ordinary codomain component.  A direct proof from closed embedding
alone is not claimed.  Instead, the file checks the W349-shaped reduction from
reverse relation-preimage to the subgroup pullback equality and exposes the
smallest certificate whose single mathematical field is exactly that equality.

Together with the W386 target-relation lift certificate, this leaves no
relation input except the target lift certificate for the W383-to-W377 consumer.
No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationPullbackEqualityV370SupportW389

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W389-local spelling of W383's relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W389-local spelling of the reverse elementwise relation-preimage condition. -/
abbrev relationPreimageReverseConditionW349
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/-- W389-local spelling of W383's target relation lifting through the component. -/
abbrev targetRelationLiftsThroughComponentW383
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
The square equations give the forward relation-preimage inclusion by taking the
closure of the algebraic range inclusion.
-/
theorem relationPreimageForwardOfSquaresW389
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

/-- Reverse relation-preimage plus the square equations imply the full pullback equality. -/
theorem relationPreimagePullbackConditionOfReverseW389
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW349 f g f' g' iB) :
    relationPreimagePullbackConditionW383 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · intro b hb
    exact relationPreimageForwardOfSquaresW389 iA iB hsquare_left hsquare_right b hb

/-- The pullback equality immediately gives the reverse elementwise condition. -/
theorem relationPreimageReverseOfPullbackConditionW389
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW383 f g f' g' iB) :
    relationPreimageReverseConditionW349 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackConditionW383] using (hpullback ▸ hbcomap)

/-- Under square equations, W383's equality is equivalent to W349's reverse condition. -/
theorem relationPreimagePullbackConditionIffReverseW389
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    relationPreimagePullbackConditionW383 f g f' g' iB ↔
      relationPreimageReverseConditionW349 f g f' g' iB := by
  constructor
  · exact relationPreimageReverseOfPullbackConditionW389 iB
  · exact relationPreimagePullbackConditionOfReverseW389 iA iB hsquare_left hsquare_right

/--
Objectwise relation-pullback certificate for the ordinary codomain component.
The single mathematical field is exactly W383's relation-pullback equality.
-/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB

/-- The certificate is exactly sufficient to recover W383's relation-pullback predicate. -/
theorem RelationPullbackEqualityCertificateW389.to_w383_relation_pullback
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    relationPreimagePullbackConditionW383 f g f' g' iB :=
  h.relation_pullback

/-- W386-shaped target-lift certificate, restated locally for standalone checking. -/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W383's two-input package, restated locally for direct standalone checking. -/
structure ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W377-shaped reduced fields used by W383 after component closedness is supplied. -/
structure ConcreteQuotientClosedMapRelationFieldsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- Closed embedding of the ordinary component supplies W377's closed-map field. -/
theorem componentClosedMap_of_closedEmbeddingW389
    {B B' : MetrizableLCA.{u}} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B')) :
    IsClosedMap (iB : B → B') :=
  hiB.isClosedMap

/-- Local W383 adapter into W377-shaped reduced relation fields. -/
theorem ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (h : ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383 f g f' g' iA iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB where
  component_closedMap := componentClosedMap_of_closedEmbeddingW389 hiB
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/--
Concrete checked consumer into W386's W383 route: relation equality is supplied
by the W389 certificate, leaving target relation lift as the remaining relation
certificate input.
-/
theorem RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB :=
  ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    hiB
    { relation_pullback := hpullback.to_w383_relation_pullback
      target_relation_lifts := htarget.target_relation_lifts }

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
abbrev WppOpRelationPreimagePullbackConditionW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationPreimagePullbackConditionW383
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op reverse relation-preimage condition through the ordinary codomain component. -/
abbrev WppOpRelationPreimageReverseConditionW349
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.relationPreimageReverseConditionW349
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op target relation lifting through the ordinary codomain component. -/
abbrev WppOpTargetRelationLiftsThroughCodomainComponentW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW383
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- Objectwise WPP-op relation-pullback certificate for the ordinary codomain component. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- Objectwise WPP-op target-lift certificate matching W386. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- W383's two WPP-op relation inputs, restated locally for direct checking. -/
structure WppOpRelationPullbackTargetLiftInputsW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop where
  relation_pullback : WppOpRelationPreimagePullbackConditionW383 α
  target_relation_lifts : WppOpTargetRelationLiftsThroughCodomainComponentW383 α

/-- WPP-op W377-shaped reduced fields after component closedness has been supplied. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- Objectwise closed embeddings supply the ordinary codomain component as a closed map. -/
theorem wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    IsClosedMap (wppOpOrdinaryCodomainMap α : wppOpCodomain X → wppOpCodomain Y) :=
  (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)).isClosedMap

/-- The WPP-op relation-pullback certificate is exactly W383's equality. -/
theorem WppOpRelationPullbackEqualityCertificateW389.to_w383_relation_pullback
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpRelationPullbackEqualityCertificateW389 α) :
    WppOpRelationPreimagePullbackConditionW383 α :=
  h.relation_pullback

/-- WPP-op certificate consumer: with relation equality packaged, target lift remains. -/
theorem WppOpRelationPullbackEqualityCertificateW389.to_w383_inputs
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpRelationPullbackTargetLiftInputsW383 α where
  relation_pullback := hpullback.to_w383_relation_pullback
  target_relation_lifts := htarget.target_relation_lifts

/--
Checked WPP-op consumer into the W386/W383 route.  The relation-pullback
equality is supplied by the W389 certificate, so the remaining relation-side
input is exactly the W386 target-lift certificate.
-/
theorem WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
    hpullback htarget

/-- Machine-readable W389 state. -/
structure WppOpRelationPullbackEqualityV370SupportStateW389 : Type where
  seed : String
  checkedFacts : List String
  relationPullbackEqualityResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationPullbackEqualityV370SupportStateW389 :
    WppOpRelationPullbackEqualityV370SupportStateW389 where
  seed := "beccfed1-cefe-4b6f-b2fb-7e8b5b587ccc"
  checkedFacts :=
    ["ConcreteMetrizableLCA.relationPreimagePullbackConditionOfReverseW389",
      "ConcreteMetrizableLCA.relationPreimagePullbackConditionIffReverseW389",
      "ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w383_relation_pullback",
      "ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386",
      "WppOpRelationPullbackEqualityCertificateW389.to_w383_relation_pullback",
      "WppOpRelationPullbackEqualityCertificateW389.to_w383_inputs",
      "WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386"]
  relationPullbackEqualityResult := "partial"
  remainingInputs :=
    ["target relation lift certificate from W386",
      "or reverse relation-preimage condition to construct the W389 equality certificate"]
  productSuccessClaimed := false

theorem currentWppOpRelationPullbackEqualityV370SupportStateW389_productSuccess :
    currentWppOpRelationPullbackEqualityV370SupportStateW389.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimagePullbackConditionW383
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimageReverseConditionW349
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimageForwardOfSquaresW389
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimagePullbackConditionOfReverseW389
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimageReverseOfPullbackConditionW389
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.relationPreimagePullbackConditionIffReverseW389
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w383_relation_pullback
#check WppOpRelationPullbackEqualityV370SupportW389.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPreimagePullbackConditionW383
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPreimageReverseConditionW349
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPullbackEqualityCertificateW389
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPullbackEqualityCertificateW389.to_w383_relation_pullback
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPullbackEqualityCertificateW389.to_w383_inputs
#check WppOpRelationPullbackEqualityV370SupportW389.WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
#check WppOpRelationPullbackEqualityV370SupportW389.currentWppOpRelationPullbackEqualityV370SupportStateW389
#check WppOpRelationPullbackEqualityV370SupportW389.currentWppOpRelationPullbackEqualityV370SupportStateW389_productSuccess

end Checks

end WppOpRelationPullbackEqualityV370SupportW389

end LeanLCAExactChallenge
