import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W401: WPP-op relation fields from the W380/W389/W392 certificate shapes.

This standalone audit file composes the already checked tiny certificate shapes:
W380 supplies the component closed-map field, W389 supplies relation-pullback
equality, W392 supplies target-relation lifting, W395 packages the three fields,
and W397 projects the resulting W371 input package to final relation fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationFieldsFromCertificatesV370SupportW401

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W401 spelling of the W389/W383 relation-pullback equality field. -/
abbrev relationPreimagePullbackConditionW401
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W401 spelling of the W392/W386 target-relation lift field. -/
abbrev targetRelationLiftsThroughComponentW401
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- W380 component-closedness certificate. -/
structure ComponentClosedMapCertificateW380 (iB : B ⟶ B') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')

/-- W380 closed-embedding input converted to the closed-map certificate. -/
theorem ComponentClosedMapCertificateW380.of_closedEmbedding
    {iB : B ⟶ B'} (hiB : IsClosedEmbedding (iB : B → B')) :
    ComponentClosedMapCertificateW380 iB where
  component_closedMap := hiB.isClosedMap

/-- W389 relation-pullback equality certificate. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW401 f g f' g' iB

/-- W392/W386 target-relation lift certificate. -/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW401 f' g' iB

/-- W395 final relation-field package. -/
structure ConcreteQuotientClosedMapRelationFieldsW395
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW401 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW401 f' g' iB

/-- W371 input package after the two naturality squares are fixed. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (_hsquare_left : f ≫ iB = iA ≫ f')
    (_hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW401 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW401 f' g' iB

/-- W395 relation fields project to the W371 input package once squares are supplied. -/
theorem ConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRelationFieldsW395 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- W371 input package projects back to W395 final relation fields. -/
theorem ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right) :
    ConcreteQuotientClosedMapRelationFieldsW395 f g f' g' iA iB where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- Concrete composition of W380, W389, and W392 certificates into W395 fields. -/
theorem relationFields_of_w380_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hclosed : ComponentClosedMapCertificateW380 iB)
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW395 f g f' g' iA iB where
  component_closedMap := hclosed.component_closedMap
  relation_pullback := hpullback.relation_pullback
  target_relation_lifts := htarget.target_relation_lifts

/-- Closed-embedding variant of the concrete certificate composer. -/
theorem relationFields_of_closedEmbedding_w389_w392
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hiB : IsClosedEmbedding (iB : B → B'))
    (hpullback : RelationPullbackEqualityCertificateW389 f g f' g' iB)
    (htarget : TargetRelationLiftCertificateW386 f' g' iB) :
    ConcreteQuotientClosedMapRelationFieldsW395 f g f' g' iA iB :=
  relationFields_of_w380_w389_w392
    (ComponentClosedMapCertificateW380.of_closedEmbedding hiB) hpullback htarget

/-- Direct concrete composition into W371 inputs. -/
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

/-- WPP-op W380 component closed-map certificate. -/
abbrev WppOpComponentClosedMapCertificateW380
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ComponentClosedMapCertificateW380
    (wppOpOrdinaryCodomainMap α)

/-- Objectwise closed embeddings supply the W380 component closed-map certificate. -/
theorem WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    WppOpComponentClosedMapCertificateW380 α :=
  ConcreteMetrizableLCA.ComponentClosedMapCertificateW380.of_closedEmbedding
    (hclosed (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))

/-- WPP-op W389 relation-pullback equality certificate. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W392/W386 target-relation lift certificate. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W395 final relation-field package. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW395
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW401
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation, from naturality. -/
theorem wppOpRightSquareEquationW401
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- WPP-op W371 input package using the naturality square equations. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW401 α)
    (wppOpRightSquareEquationW401 α)

/-- WPP-op composition of W380, W389, and W392 certificates into W395 fields. -/
theorem relationFields_of_w380_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed : WppOpComponentClosedMapCertificateW380 α)
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW395 α :=
  ConcreteMetrizableLCA.relationFields_of_w380_w389_w392 hclosed hpullback htarget

/-- WPP-op closed-embedding route into W395 fields. -/
theorem relationFields_of_objectwise_closedEmbedding_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW395 α :=
  relationFields_of_w380_w389_w392
    (WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding α hclosed)
    hpullback htarget

/-- WPP-op W395 relation fields expose the W371 input package. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW395 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs h

/-- WPP-op W371 input package projects to W395 final relation fields. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapInputsW371 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW395 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields h

/-- Direct WPP-op composition into the W371 input package. -/
theorem w371Inputs_of_w380_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed : WppOpComponentClosedMapCertificateW380 α)
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  (relationFields_of_w380_w389_w392 hclosed hpullback htarget).to_w371_inputs

/-- Closed-embedding route directly into the W371 input package. -/
theorem w371Inputs_of_objectwise_closedEmbedding_w389_w392
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hpullback : WppOpRelationPullbackEqualityCertificateW389 α)
    (htarget : WppOpTargetRelationLiftCertificateW386 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α :=
  (relationFields_of_objectwise_closedEmbedding_w389_w392 hclosed hpullback htarget).to_w371_inputs

/-- Machine-readable W401 state. -/
structure WppOpRelationFieldsFromCertificatesV370SupportStateW401 : Type where
  seed : String
  checkedFacts : List String
  relationFieldsFromCertificatesResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationFieldsFromCertificatesV370SupportStateW401 :
    WppOpRelationFieldsFromCertificatesV370SupportStateW401 where
  seed := "8a2973499a8226ecf785955fe25ba551"
  checkedFacts :=
    ["ConcreteMetrizableLCA.ComponentClosedMapCertificateW380.of_closedEmbedding",
      "ConcreteMetrizableLCA.relationFields_of_w380_w389_w392",
      "ConcreteMetrizableLCA.relationFields_of_closedEmbedding_w389_w392",
      "ConcreteMetrizableLCA.w371Inputs_of_w380_w389_w392",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields",
      "WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding",
      "relationFields_of_w380_w389_w392",
      "relationFields_of_objectwise_closedEmbedding_w389_w392",
      "WppOpConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs",
      "WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields",
      "w371Inputs_of_w380_w389_w392",
      "w371Inputs_of_objectwise_closedEmbedding_w389_w392"]
  relationFieldsFromCertificatesResult := "proved"
  remainingInputs :=
    ["for callers: W389 relation-pullback equality certificate",
      "for callers: W392/W386 target-relation lift certificate",
      "component closedness is discharged by W380 from objectwise closed embeddings"]
  productSuccessClaimed := false

theorem currentWppOpRelationFieldsFromCertificatesV370SupportStateW401_productSuccess :
    currentWppOpRelationFieldsFromCertificatesV370SupportStateW401.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.ComponentClosedMapCertificateW380.of_closedEmbedding
#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.relationFields_of_w380_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.relationFields_of_closedEmbedding_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.w371Inputs_of_w380_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs
#check WppOpRelationFieldsFromCertificatesV370SupportW401.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
#check WppOpRelationFieldsFromCertificatesV370SupportW401.WppOpComponentClosedMapCertificateW380.of_objectwise_closedEmbedding
#check WppOpRelationFieldsFromCertificatesV370SupportW401.relationFields_of_w380_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.relationFields_of_objectwise_closedEmbedding_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.WppOpConcreteQuotientClosedMapRelationFieldsW395.to_w371_inputs
#check WppOpRelationFieldsFromCertificatesV370SupportW401.WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
#check WppOpRelationFieldsFromCertificatesV370SupportW401.w371Inputs_of_w380_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.w371Inputs_of_objectwise_closedEmbedding_w389_w392
#check WppOpRelationFieldsFromCertificatesV370SupportW401.currentWppOpRelationFieldsFromCertificatesV370SupportStateW401_productSuccess

end Checks

end WppOpRelationFieldsFromCertificatesV370SupportW401

end LeanLCAExactChallenge
