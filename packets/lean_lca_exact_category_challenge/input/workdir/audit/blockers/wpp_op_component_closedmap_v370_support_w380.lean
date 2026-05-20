import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W380: WPP-op component closed-map support.

This standalone audit file supplies W377's component closed-map field from the
standard objectwise closed-embedding hypothesis on a WPP-op natural
transformation.  It also exposes a checked adapter whose callers only need to
provide the two remaining relation fields: relation-pullback equality and
target relation lifting.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpComponentClosedMapV370SupportW380

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W380-local spelling of W377's relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW380
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W380-local spelling of W377's target relation lifting field. -/
abbrev targetRelationLiftsThroughComponentW380
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- W377-shaped reduced fields: component closed-map plus the two relation inputs. -/
structure ConcreteQuotientClosedMapRelationFieldsW377Shape
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW380 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW380 f' g' iB

/-- The two relation inputs left after W380 supplies the component closed-map field. -/
structure ConcreteQuotientClosedMapRelationInputsW380
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  relation_pullback : relationPreimagePullbackConditionW380 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW380 f' g' iB

/-- Closed embedding of the concrete component immediately gives W377's closed-map field. -/
theorem componentClosedMap_of_closedEmbeddingW380
    {B B' : MetrizableLCA.{u}} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B')) :
    IsClosedMap (iB : B → B') :=
  hiB.isClosedMap

/--
Checked concrete adapter: once W380 is given the component closed embedding,
callers only supply relation-pullback equality and target relation lifting.
-/
theorem ConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (h : ConcreteQuotientClosedMapRelationInputsW380 f g f' g' iA iB) :
    ConcreteQuotientClosedMapRelationFieldsW377Shape f g f' g' iA iB where
  component_closedMap := componentClosedMap_of_closedEmbeddingW380 hiB
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

/--
Primary W380 result: objectwise closed embeddings on the WPP-op natural
transformation supply the ordinary codomain component as a closed map.
-/
theorem wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW380
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    IsClosedMap (wppOpOrdinaryCodomainMap α : wppOpCodomain X → wppOpCodomain Y) :=
  (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)).isClosedMap

/-- WPP-op relation fields with the component closed-map field already supplied by W380. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW377Shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377Shape
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- The WPP-op relation inputs left after objectwise closed embeddings supply component closedness. -/
abbrev WppOpConcreteQuotientClosedMapRelationInputsW380
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationInputsW380
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/--
Checked WPP-op adapter for W377-shaped relation fields.  It consumes the
standard objectwise closed-embedding hypothesis and leaves only the
relation-pullback equality plus target relation lifting.
-/
theorem WppOpConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (h : WppOpConcreteQuotientClosedMapRelationInputsW380 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW377Shape α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)) h

/-- Machine-readable W380 state. -/
structure WppOpComponentClosedMapV370SupportStateW380 : Type where
  seed : String
  checkedFacts : List String
  componentClosedMapResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpComponentClosedMapV370SupportStateW380 :
    WppOpComponentClosedMapV370SupportStateW380 where
  seed := "313ef700-6bf6-4bc8-a7bc-5c26e1805535"
  checkedFacts :=
    ["ConcreteMetrizableLCA.componentClosedMap_of_closedEmbeddingW380",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape",
      "wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW380",
      "WppOpConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape"]
  componentClosedMapResult := "proved"
  remainingInputs :=
    ["relation-pullback equality",
      "target relation lifting through the ordinary codomain component"]
  productSuccessClaimed := false

theorem currentWppOpComponentClosedMapV370SupportStateW380_productSuccess :
    currentWppOpComponentClosedMapV370SupportStateW380.productSuccessClaimed = false := rfl

section Checks

#check WppOpComponentClosedMapV370SupportW380.ConcreteMetrizableLCA.componentClosedMap_of_closedEmbeddingW380
#check WppOpComponentClosedMapV370SupportW380.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape
#check WppOpComponentClosedMapV370SupportW380.wppOpOrdinaryCodomainMap_closedMap_of_objectwise_closedEmbeddingW380
#check WppOpComponentClosedMapV370SupportW380.WppOpConcreteQuotientClosedMapRelationInputsW380.to_w377_relation_fields_shape
#check WppOpComponentClosedMapV370SupportW380.currentWppOpComponentClosedMapV370SupportStateW380_productSuccess

end Checks

end WppOpComponentClosedMapV370SupportW380

end LeanLCAExactChallenge
