import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W395: WPP-op relation-fields composer support.

This standalone audit file composes the W389 relation-pullback equality
certificate and the W392 target-relation lift certificate into the reduced
W377/W383 relation-field package.  It also exposes the exact W371 input package
obtained after inserting the WPP-op naturality square equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationFieldsComposerV370SupportW395

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W395-local spelling of the relation-pullback equality used by W377/W383. -/
abbrev relationPreimagePullbackConditionW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W395-local spelling of the target relation lift used by W377/W383. -/
abbrev targetRelationLiftsThroughComponentW383
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- W389 relation-pullback equality certificate. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB

/-- W392/W386 target relation lift certificate. -/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W377/W383 reduced relation-field shape. -/
structure ConcreteQuotientClosedMapRelationFieldsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W371 concrete input package after square equations select the descended quotient map. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (_hsquare_left : f ≫ iB = iA ≫ f')
    (_hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W389's certificate recovers the exact W377/W383 relation-pullback field. -/
theorem RelationPullbackEqualityCertificateW389.to_w383_relation_pullback
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : RelationPullbackEqualityCertificateW389 f g f' g' iB) :
    relationPreimagePullbackConditionW383 f g f' g' iB :=
  h.relation_pullback

/-- W392's target certificate recovers the exact W377/W383 target-lift field. -/
theorem TargetRelationLiftCertificateW386.to_w383_target_relation_lifts
    {f' g' : A' ⟶ B'} {iB : B ⟶ B'}
    (h : TargetRelationLiftCertificateW386 f' g' iB) :
    targetRelationLiftsThroughComponentW383 f' g' iB :=
  h.target_relation_lifts

/-- Objectwise closed embedding supplies the ordinary closed-map field. -/
theorem componentClosedMap_of_closedEmbeddingW395
    {B B' : MetrizableLCA.{u}} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B')) :
    IsClosedMap (iB : B → B') :=
  hiB.isClosedMap

/-- Core composer from closed-map plus W389 and W392 certificates to W377/W383 relation fields. -/
theorem relationFields_of_closedMap_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hclosed : IsClosedMap (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB where
  component_closedMap := hclosed
  relation_pullback := hpullback.to_w383_relation_pullback
  target_relation_lifts := htarget.to_w383_target_relation_lifts

/-- Closed-embedding variant of the core composer. -/
theorem relationFields_of_closedEmbedding_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hclosed : IsClosedEmbedding (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB :=
  relationFields_of_closedMap_w389_w392
    (componentClosedMap_of_closedEmbeddingW395 hclosed) hpullback htarget

/-- Reduced relation fields are exactly the remaining W371 input package. -/
theorem ConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- Direct composer into the W371 input package. -/
theorem w371Inputs_of_closedMap_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (hclosed : IsClosedMap (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right :=
  (relationFields_of_closedMap_w389_w392 hclosed hpullback htarget).to_w371_inputs

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

/-- WPP-op W389 relation-pullback equality certificate. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W392/W386 target-lift certificate. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W377/W383 reduced relation-field package. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation, from naturality. -/
theorem wppOpRightSquareEquationW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- WPP-op W371 input package with naturality squares made explicit. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW395 α)
    (wppOpRightSquareEquationW395 α)

/-- Objectwise closed maps compose W389 and W392 into W377/W383 relation fields. -/
theorem WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedMap (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  ConcreteMetrizableLCA.relationFields_of_closedMap_w389_w392
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
    hpullback htarget

/-- Objectwise closed embeddings also compose W389 and W392 into relation fields. -/
theorem WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392_closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW383 α :=
  ConcreteMetrizableLCA.relationFields_of_closedEmbedding_w389_w392
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
    hpullback htarget

/-- The composed relation fields expose the exact W371 input package. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW383 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs h

/-- Direct WPP-op composer into the exact W371 input package. -/
theorem WppOpRelationPullbackEqualityCertificateW389.to_w371_inputs_via_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedMap (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  (hpullback.to_relation_fields_via_w392 hclosed htarget).to_w371_inputs

/-- Machine-readable W395 state. -/
structure WppOpRelationFieldsComposerV370SupportStateW395 : Type where
  seed : String
  checkedFacts : List String
  relationFieldsComposerResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationFieldsComposerV370SupportStateW395 :
    WppOpRelationFieldsComposerV370SupportStateW395 where
  seed := "94a6cd2fe6c1524192c51fa0a88eea38"
  checkedFacts :=
    ["ConcreteMetrizableLCA.relationFields_of_closedMap_w389_w392",
      "ConcreteMetrizableLCA.relationFields_of_closedEmbedding_w389_w392",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs",
      "WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392",
      "WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392_closedEmbedding",
      "WppOpConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs",
      "WppOpRelationPullbackEqualityCertificateW389.to_w371_inputs_via_w392"]
  relationFieldsComposerResult := "proved"
  remainingInputs :=
    ["objectwise closed-map or closed-embedding component field",
      "W389 relation-pullback equality certificate",
      "W392/W386 elementwise target relation lift certificate"]
  productSuccessClaimed := false

theorem currentWppOpRelationFieldsComposerV370SupportStateW395_productSuccess :
    currentWppOpRelationFieldsComposerV370SupportStateW395.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationFieldsComposerV370SupportW395.ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
#check WppOpRelationFieldsComposerV370SupportW395.ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
#check WppOpRelationFieldsComposerV370SupportW395.ConcreteMetrizableLCA.relationFields_of_closedMap_w389_w392
#check WppOpRelationFieldsComposerV370SupportW395.ConcreteMetrizableLCA.relationFields_of_closedEmbedding_w389_w392
#check WppOpRelationFieldsComposerV370SupportW395.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs
#check WppOpRelationFieldsComposerV370SupportW395.WppOpConcreteQuotientClosedMapRelationFieldsW383
#check WppOpRelationFieldsComposerV370SupportW395.WppOpConcreteQuotientClosedMapInputsW371
#check WppOpRelationFieldsComposerV370SupportW395.WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392
#check WppOpRelationFieldsComposerV370SupportW395.WppOpRelationPullbackEqualityCertificateW389.to_relation_fields_via_w392_closedEmbedding
#check WppOpRelationFieldsComposerV370SupportW395.WppOpConcreteQuotientClosedMapRelationFieldsW383.to_w371_inputs
#check WppOpRelationFieldsComposerV370SupportW395.WppOpRelationPullbackEqualityCertificateW389.to_w371_inputs_via_w392
#check WppOpRelationFieldsComposerV370SupportW395.currentWppOpRelationFieldsComposerV370SupportStateW395_productSuccess

end Checks

end WppOpRelationFieldsComposerV370SupportW395

end LeanLCAExactChallenge
