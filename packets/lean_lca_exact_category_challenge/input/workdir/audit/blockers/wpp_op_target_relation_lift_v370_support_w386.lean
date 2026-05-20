import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W386: WPP-op target relation lift support.

This standalone audit file sharpens W383's target relation lifting condition
through the ordinary codomain component.  It does not prove the broad target
lift from weaker hypotheses; instead it exposes a checked objectwise
certificate whose single mathematical field is exactly W383's target-lift
predicate.  Given that certificate, the only relation input left explicit for
the W383-to-W377 adapter is the relation-pullback equality.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpTargetRelationLiftV370SupportW386

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W386-local spelling of W383's relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W386-local spelling of W383's target relation lifting through the component. -/
abbrev targetRelationLiftsThroughComponentW383
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
Objectwise target-lift certificate for the ordinary codomain component.  The
field is intentionally no stronger and no weaker than W383's target-lift
predicate.
-/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- The certificate is exactly sufficient to recover W383's target-lift predicate. -/
theorem TargetRelationLiftCertificateW386.to_w383_target_relation_lifts
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : TargetRelationLiftCertificateW386 f' g' iB) :
    targetRelationLiftsThroughComponentW383 f' g' iB :=
  h.target_relation_lifts

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
theorem componentClosedMap_of_closedEmbeddingW386
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
  component_closedMap := componentClosedMap_of_closedEmbeddingW386 hiB
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/--
Concrete certificate consumer: after target lifting is packaged as a
certificate, the only explicit relation input left before the W383 adapter is
the relation-pullback equality.
-/
theorem TargetRelationLiftCertificateW386.to_w383_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hpullback : relationPreimagePullbackConditionW383 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383 f g f' g' iA iB where
  relation_pullback := hpullback
  target_relation_lifts := htarget.to_w383_target_relation_lifts

/--
Concrete checked consumer into
`ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields`.
The remaining explicit relation input is exactly the relation-pullback equality.
-/
theorem TargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (hpullback : relationPreimagePullbackConditionW383 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB :=
  ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    hiB (htarget.to_w383_inputs hpullback)

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

/-- WPP-op target relation lifting through the ordinary codomain component. -/
abbrev WppOpTargetRelationLiftsThroughCodomainComponentW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW383
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- Objectwise WPP-op target-lift certificate for the ordinary codomain component. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- The WPP-op certificate is exactly W383's target relation lifting predicate. -/
theorem WppOpTargetRelationLiftCertificateW386.to_w383_target_relation_lifts
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpTargetRelationLiftsThroughCodomainComponentW383 α :=
  h.target_relation_lifts

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
theorem wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    IsClosedMap (wppOpOrdinaryCodomainMap α : wppOpCodomain X → wppOpCodomain Y) :=
  (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)).isClosedMap

/-- Local W383 adapter into W377's reduced WPP-op relation fields. -/
theorem WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (h : WppOpRelationPullbackTargetLiftInputsW383 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
    { relation_pullback := h.relation_pullback
      target_relation_lifts := h.target_relation_lifts }

/--
WPP-op certificate consumer: with target lifting packaged, the only explicit
relation input left before W383 is the relation-pullback equality.
-/
theorem WppOpTargetRelationLiftCertificateW386.to_w383_inputs
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hpullback : WppOpRelationPreimagePullbackConditionW383 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpRelationPullbackTargetLiftInputsW383 α where
  relation_pullback := hpullback
  target_relation_lifts := htarget.to_w383_target_relation_lifts

/--
Checked WPP-op consumer into
`WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields`.  The target
relation lift is supplied by the W386 certificate, so only relation-pullback
equality remains as an explicit relation input.
-/
theorem WppOpTargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPreimagePullbackConditionW383 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    hclosed (htarget.to_w383_inputs hpullback)

/-- Machine-readable W386 state. -/
structure WppOpTargetRelationLiftV370SupportStateW386 : Type where
  seed : String
  checkedFacts : List String
  targetRelationLiftResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpTargetRelationLiftV370SupportStateW386 :
    WppOpTargetRelationLiftV370SupportStateW386 where
  seed := "99ce38c8-307b-4d4e-8723-19ad602ede54"
  checkedFacts :=
    ["ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w383_target_relation_lifts",
      "ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w383_inputs",
      "ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383",
      "WppOpTargetRelationLiftCertificateW386.to_w383_target_relation_lifts",
      "WppOpTargetRelationLiftCertificateW386.to_w383_inputs",
      "WppOpTargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383"]
  targetRelationLiftResult := "partial"
  remainingInputs :=
    ["relation-pullback equality through the ordinary codomain component"]
  productSuccessClaimed := false

theorem currentWppOpTargetRelationLiftV370SupportStateW386_productSuccess :
    currentWppOpTargetRelationLiftV370SupportStateW386.productSuccessClaimed = false := rfl

section Checks

#check WppOpTargetRelationLiftV370SupportW386.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
#check WppOpTargetRelationLiftV370SupportW386.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w383_target_relation_lifts
#check WppOpTargetRelationLiftV370SupportW386.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w383_inputs
#check WppOpTargetRelationLiftV370SupportW386.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383
#check WppOpTargetRelationLiftV370SupportW386.WppOpTargetRelationLiftsThroughCodomainComponentW383
#check WppOpTargetRelationLiftV370SupportW386.WppOpTargetRelationLiftCertificateW386
#check WppOpTargetRelationLiftV370SupportW386.WppOpTargetRelationLiftCertificateW386.to_w383_target_relation_lifts
#check WppOpTargetRelationLiftV370SupportW386.WppOpTargetRelationLiftCertificateW386.to_w383_inputs
#check WppOpTargetRelationLiftV370SupportW386.WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
#check WppOpTargetRelationLiftV370SupportW386.WppOpTargetRelationLiftCertificateW386.to_w377_relation_fields_via_w383
#check WppOpTargetRelationLiftV370SupportW386.currentWppOpTargetRelationLiftV370SupportStateW386_productSuccess

end Checks

end WppOpTargetRelationLiftV370SupportW386

end LeanLCAExactChallenge
