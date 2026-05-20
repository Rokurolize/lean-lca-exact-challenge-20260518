import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W397: WPP-op relation fields from W371/W377 support.

This standalone audit file checks the exact relation-side projection from the
W371/W377 quotient closed-map input packages into the W395 final relation-field
shape.  The bridge is field-for-field: W371 carries the three W395 relation
fields plus target quotient closed-on-saturated support, and W377 carries
exactly the three W395 relation fields.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpRelationFieldsFromW371V370SupportW397

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W397-local spelling of W371/W377/W395 relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW397
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W397-local spelling of W371/W377/W395 target relation lifting. -/
abbrev targetRelationLiftsThroughComponentW397
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- A quotient-like saturation predicate used only to preserve W371's extra field. -/
def IsSaturatedForW397 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- W371's target quotient closed-on-saturated support field. -/
structure TargetQuotientClosedOnSaturatedSetsW397
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW397 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/-- W389 relation-pullback equality certificate, in the W395 boundary shape. -/
structure RelationPullbackEqualityCertificateW389
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  relation_pullback : relationPreimagePullbackConditionW397 f g f' g' iB

/-- W392/W386 target relation lift certificate, in the W395 boundary shape. -/
structure TargetRelationLiftCertificateW386
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop where
  target_relation_lifts : targetRelationLiftsThroughComponentW397 f' g' iB

/-- W395's final relation-side field package. -/
structure ConcreteQuotientClosedMapRelationFieldsW395
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW397 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW397 f' g' iB

/-- W377's reduced relation/component fields. -/
structure ConcreteQuotientClosedMapRelationFieldsW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW397 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW397 f' g' iB

/-- W371's concrete quotient closed-map input package, with square equations explicit. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (_hsquare_left : f ≫ iB = iA ≫ f')
    (_hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW397 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW397 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW397 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- W371 directly supplies W395's W389 relation-pullback certificate. -/
theorem ConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB where
  relation_pullback := h.relation_pullback

/-- W371 directly supplies W395's W386/W392 target-lift certificate. -/
theorem ConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right) :
    TargetRelationLiftCertificateW386 f' g' iB where
  target_relation_lifts := h.target_relation_lifts

/-- W371 inputs project field-for-field to W395's final relation fields. -/
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

/-- W377's reduced fields directly supply W395 relation fields. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    ConcreteQuotientClosedMapRelationFieldsW395 f g f' g' iA iB where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- W377's reduced fields directly supply W395's W389 certificate. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    RelationPullbackEqualityCertificateW389 f g f' g' iB where
  relation_pullback := h.relation_pullback

/-- W377's reduced fields directly supply W395's W386/W392 target certificate. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    TargetRelationLiftCertificateW386 f' g' iB where
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

/-- WPP-op left square equation from naturality. -/
theorem wppOpLeftSquareEquationW397
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- WPP-op right square equation from naturality. -/
theorem wppOpRightSquareEquationW397
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- WPP-op W395 final relation-side field package. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW395
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op W377 reduced relation/component fields. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW377
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op W371 concrete input package with naturality squares inserted. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    (wppOpLeftSquareEquationW397 α)
    (wppOpRightSquareEquationW397 α)

/-- WPP-op W389 relation-pullback equality certificate. -/
abbrev WppOpRelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.RelationPullbackEqualityCertificateW389
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- WPP-op W386/W392 target relation lift certificate. -/
abbrev WppOpTargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.TargetRelationLiftCertificateW386
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryCodomainMap α)

/-- W371 input package projects to W395's final WPP-op relation fields. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapInputsW371 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW395 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields h

/-- W371 input package projects to W395's W389 certificate. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapInputsW371 α) :
    WppOpRelationPullbackEqualityCertificateW389 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate h

/-- W371 input package projects to W395's W386/W392 target-lift certificate. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapInputsW371 α) :
    WppOpTargetRelationLiftCertificateW386 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate h

/-- W377 reduced fields project to W395's final WPP-op relation fields. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    WppOpConcreteQuotientClosedMapRelationFieldsW395 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields h

/-- W377 reduced fields project to W395's W389 certificate. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    WppOpRelationPullbackEqualityCertificateW389 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate h

/-- W377 reduced fields project to W395's W386/W392 target-lift certificate. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    WppOpTargetRelationLiftCertificateW386 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate h

/-- Machine-readable W397 state. -/
structure WppOpRelationFieldsFromW371V370SupportStateW397 : Type where
  seed : String
  checkedFacts : List String
  relationFieldsFromW371Result : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpRelationFieldsFromW371V370SupportStateW397 :
    WppOpRelationFieldsFromW371V370SupportStateW397 where
  seed := "0d1751407ec79a6f914068ce3fa3d083"
  checkedFacts :=
    ["ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate",
      "WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields",
      "WppOpConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate",
      "WppOpConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate"]
  relationFieldsFromW371Result := "proved"
  remainingInputs :=
    ["W371/W377 callers still supply component closed-map for the ordinary codomain component",
      "W371/W377 callers still supply relation-pullback equality",
      "W371/W377 callers still supply target relation lifting through the ordinary codomain component"]
  productSuccessClaimed := false

theorem currentWppOpRelationFieldsFromW371V370SupportStateW397_productSuccess :
    currentWppOpRelationFieldsFromW371V370SupportStateW397.productSuccessClaimed = false := rfl

section Checks

#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields
#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapInputsW371.to_w395_relation_fields
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapInputsW371.to_w389_relation_pullback_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapInputsW371.to_w386_target_relation_lift_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w395_relation_fields
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w389_relation_pullback_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w386_target_relation_lift_certificate
#check WppOpRelationFieldsFromW371V370SupportW397.currentWppOpRelationFieldsFromW371V370SupportStateW397_productSuccess

end Checks

end WppOpRelationFieldsFromW371V370SupportW397

end LeanLCAExactChallenge
