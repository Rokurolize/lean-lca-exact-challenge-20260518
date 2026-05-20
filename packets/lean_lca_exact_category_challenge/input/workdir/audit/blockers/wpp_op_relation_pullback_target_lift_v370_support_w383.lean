import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W383: WPP-op relation-pullback and target-lift adapter.

The fixed standalone verification command does not put `audit/blockers` on the
Lean import path, so this file restates the small checked interface needed by
the parent thread.  The adapter leaves exactly the two intended relation inputs:

* relation-pullback equality for the ordinary codomain component;
* target relation lifting through the ordinary codomain component.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationPullbackTargetLiftV370SupportW383

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W383-local spelling of the relation-pullback equality left after W380. -/
abbrev relationPreimagePullbackConditionW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W383-local spelling of target relation lifting through the component. -/
abbrev targetRelationLiftsThroughComponentW383
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- The exact two relation inputs remaining once W380 supplies component closedness. -/
structure ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- W377-shaped reduced fields: component closed-map plus the two relation inputs. -/
structure ConcreteQuotientClosedMapRelationFieldsW383
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW383 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW383 f' g' iB

/-- Closed embedding of the concrete component supplies the component closed-map field. -/
theorem componentClosedMap_of_closedEmbeddingW383
    {B B' : MetrizableLCA.{u}} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B')) :
    IsClosedMap (iB : B → B') :=
  hiB.isClosedMap

/--
Concrete adapter into the W377-shaped reduced relation fields: W380 supplies the
component closed-map field, and W383 carries exactly the two relation fields.
-/
theorem ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (h : ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383 f g f' g' iA iB) :
    ConcreteQuotientClosedMapRelationFieldsW383 f g f' g' iA iB where
  component_closedMap := componentClosedMap_of_closedEmbeddingW383 hiB
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

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

/-- The exact two WPP-op relation inputs left after W380 supplies component closedness. -/
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
theorem wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW383
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    IsClosedMap (wppOpOrdinaryCodomainMap α : wppOpCodomain X → wppOpCodomain Y) :=
  (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)).isClosedMap

/-- W383 adapter into W377's actual reduced WPP-op relation fields. -/
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

/-- Machine-readable W383 state. -/
structure WppOpRelationPullbackTargetLiftV370SupportStateW383 : Type where
  seed : String
  checkedFacts : List String
  relationPullbackTargetLiftResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationPullbackTargetLiftV370SupportStateW383 :
    WppOpRelationPullbackTargetLiftV370SupportStateW383 where
  seed := "8e729f9c-0b03-4141-aca5-bda9685b437c"
  checkedFacts :=
    ["ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields",
      "wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW383",
      "WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields",
      "WppOpConcreteQuotientClosedMapRelationFieldsW383"]
  relationPullbackTargetLiftResult := "partial"
  remainingInputs :=
    ["relation-pullback equality through the ordinary codomain component",
      "target relation lifting through the ordinary codomain component"]
  productSuccessClaimed := false

theorem currentWppOpRelationPullbackTargetLiftV370SupportStateW383_productSuccess :
    currentWppOpRelationPullbackTargetLiftV370SupportStateW383.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.relationPreimagePullbackConditionW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.componentClosedMap_of_closedEmbeddingW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
#check WppOpRelationPullbackTargetLiftV370SupportW383.WppOpRelationPreimagePullbackConditionW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.WppOpTargetRelationLiftsThroughCodomainComponentW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.WppOpRelationPullbackTargetLiftInputsW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.WppOpConcreteQuotientClosedMapRelationFieldsW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW383
#check WppOpRelationPullbackTargetLiftV370SupportW383.WppOpRelationPullbackTargetLiftInputsW383.to_w377_relation_fields
#check WppOpRelationPullbackTargetLiftV370SupportW383.currentWppOpRelationPullbackTargetLiftV370SupportStateW383_productSuccess

end Checks

end WppOpRelationPullbackTargetLiftV370SupportW383

end LeanLCAExactChallenge
