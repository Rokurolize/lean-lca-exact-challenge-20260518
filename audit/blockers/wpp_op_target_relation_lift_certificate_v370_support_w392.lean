import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W392: WPP-op target relation lift certificate bridge.

The audit files in `audit/blockers` are checked as standalone Lean files, so
this file restates the small interfaces needed from W368/W371/W377/W386/W389.
It proves that every existing concrete target-relation-lift field has exactly
the right elementwise shape to build the W386 target-lift certificate.  It also
provides a checked consumer matching W389's
`to_w377_relation_fields_via_w386`: once the target lift is packaged as a W386
certificate, the other explicit relation-side input is only the W389
relation-pullback equality certificate.

No direct proof of the target lift from weaker hypotheses is claimed, and no
product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpTargetRelationLiftCertificateV370SupportW392

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W392-local spelling of the relation-pullback equality used by W383/W389. -/
abbrev relationPreimagePullbackConditionW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- The W368 target relation lift field. -/
abbrev targetRelationLiftsThroughComponentW368
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- The W377 target relation lift field. -/
abbrev targetRelationLiftsThroughComponentW377
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- The W383/W386 target relation lift field. -/
abbrev targetRelationLiftsThroughComponentW383
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
W386 target-lift certificate.  Its field is exactly the W383 target-relation
lift statement.
-/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- The W386 certificate recovers the exact W383 target-lift predicate. -/
theorem TargetRelationLiftCertificateW386.to_w383_target_relation_lifts
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : TargetRelationLiftCertificateW386 f' g' iB) :
    targetRelationLiftsThroughComponentW383 f' g' iB :=
  h.target_relation_lifts

/-- W368's elementwise target-lift field packages directly as W386. -/
theorem targetRelationLiftsThroughComponentW368.to_w386_certificate
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : targetRelationLiftsThroughComponentW368 f' g' iB) :
    TargetRelationLiftCertificateW386 f' g' iB where
  target_relation_lifts := h

/-- W377's elementwise target-lift field packages directly as W386. -/
theorem targetRelationLiftsThroughComponentW377.to_w386_certificate
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : targetRelationLiftsThroughComponentW377 f' g' iB) :
    TargetRelationLiftCertificateW386 f' g' iB where
  target_relation_lifts := h

/-- W383's elementwise target-lift field packages directly as W386. -/
theorem targetRelationLiftsThroughComponentW383.to_w386_certificate
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : targetRelationLiftsThroughComponentW383 f' g' iB) :
    TargetRelationLiftCertificateW386 f' g' iB where
  target_relation_lifts := h

/-- W389 relation-pullback certificate. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB

/-- W389's certificate recovers the exact W383 relation-pullback equality. -/
theorem RelationPullbackEqualityCertificateW389.to_w383_relation_pullback
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    relationPreimagePullbackConditionW383 f g f' g' iB :=
  h.relation_pullback

/-- W377-shaped reduced fields used after component closedness is supplied. -/
structure ConcreteQuotientClosedMapRelationFieldsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W371 concrete input package; its target field is the W368/W377 elementwise lift. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (_hsquare_left : f ≫ iB = iA ≫ f')
    (_hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW368 f' g' iB

/-- W377 reduced relation fields also expose the exact target-lift statement. -/
structure ConcreteQuotientClosedMapRelationFieldsW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW377 f' g' iB

/-- Extract the W386 certificate from the W371 concrete input package. -/
theorem ConcreteQuotientClosedMapInputsW371.to_w386_target_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h :
      ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
        hsquare_left hsquare_right) :
    TargetRelationLiftCertificateW386 f' g' iB :=
  h.target_relation_lifts.to_w386_certificate

/-- Extract the W386 certificate from W377's reduced relation fields. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    TargetRelationLiftCertificateW386 f' g' iB :=
  h.target_relation_lifts.to_w386_certificate

/--
Concrete W389-compatible consumer: relation equality is supplied by the W389
certificate and target lifting by the W386 certificate.
-/
theorem RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedMap (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB where
  component_closedMap := hiB
  relation_pullback := hpullback.to_w383_relation_pullback
  target_relation_lifts := htarget.to_w383_target_relation_lifts

/-- W371 input package feeds the W389/W386 consumer with only W389 relation equality explicit. -/
theorem ConcreteQuotientClosedMapInputsW371.to_w377_relation_fields_via_w389
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h :
      ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
        hsquare_left hsquare_right)
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB :=
  hpullback.to_w377_relation_fields_via_w386
    h.component_closedMap h.to_w386_target_certificate

/-- W377 reduced fields feed the W389/W386 consumer with only W389 relation equality explicit. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w377_relation_fields_via_w389
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB)
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB :=
  hpullback.to_w377_relation_fields_via_w386
    h.component_closedMap h.to_w386_target_certificate

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

/-- WPP-op W386 target-lift certificate. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op target relation lifting through the ordinary codomain component. -/
abbrev WppOpTargetRelationLiftsThroughCodomainComponentW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW383
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W389 relation-pullback equality certificate. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W377-shaped relation fields after component closedness is supplied. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- The WPP-op certificate recovers the exact target-lift predicate. -/
theorem WppOpTargetRelationLiftCertificateW386.to_w383_target_relation_lifts
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpTargetRelationLiftsThroughCodomainComponentW383 α :=
  h.target_relation_lifts

/--
WPP-op consumer matching W389's route through W386: the only relation-side
input besides the target certificate is the W389 relation-pullback certificate.
-/
theorem WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedMap (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
    hpullback htarget

/-- Machine-readable W392 state. -/
structure WppOpTargetRelationLiftCertificateV370SupportStateW392 : Type where
  seed : String
  checkedFacts : List String
  targetRelationLiftCertificateResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpTargetRelationLiftCertificateV370SupportStateW392 :
    WppOpTargetRelationLiftCertificateV370SupportStateW392 where
  seed := "3278e9241f6f30f705068d538539f9bd"
  checkedFacts :=
    ["ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW368.to_w386_certificate",
      "ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW377.to_w386_certificate",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w386_target_certificate",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_certificate",
      "ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386",
      "WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386"]
  targetRelationLiftCertificateResult := "partial"
  remainingInputs :=
    ["elementwise target relation lift through the ordinary codomain component",
      "W389 relation-pullback equality certificate"]
  productSuccessClaimed := false

theorem currentWppOpTargetRelationLiftCertificateV370SupportStateW392_productSuccess :
    currentWppOpTargetRelationLiftCertificateV370SupportStateW392.productSuccessClaimed = false := rfl

section Checks

#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW368.to_w386_certificate
#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW377.to_w386_certificate
#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w386_target_certificate
#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_certificate
#check WppOpTargetRelationLiftCertificateV370SupportW392.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
#check WppOpTargetRelationLiftCertificateV370SupportW392.WppOpTargetRelationLiftCertificateW386
#check WppOpTargetRelationLiftCertificateV370SupportW392.WppOpTargetRelationLiftCertificateW386.to_w383_target_relation_lifts
#check WppOpTargetRelationLiftCertificateV370SupportW392.WppOpRelationPullbackEqualityCertificateW389.to_w377_relation_fields_via_w386
#check WppOpTargetRelationLiftCertificateV370SupportW392.currentWppOpTargetRelationLiftCertificateV370SupportStateW392_productSuccess

end Checks

end WppOpTargetRelationLiftCertificateV370SupportW392

end LeanLCAExactChallenge
