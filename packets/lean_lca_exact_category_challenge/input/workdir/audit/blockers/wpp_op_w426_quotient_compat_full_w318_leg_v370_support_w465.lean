import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W465: promote W461 quotient-compatibility target-leg inputs to full W318 leg
compatibility.

This standalone support file copies the small W461 target-leg calculation and
the W454/W458 source-from-target argument.  The final theorem consumes only the
W426 quotient-compatibility and W387 point-identification fields.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426QuotientCompatFullW318LegV370SupportW465

/-- Required random seed for this support-search branch. -/
def supportSeed : String :=
  "9ec51505e2879e348bfc6bdc0407361f"

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW465 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomainW465 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW465 X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomainW465 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW465 X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeftW465 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW465 X ⟶ wppOpCodomainW465 X :=
  (wppOpOrdinaryDiagramW465 X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRightW465 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW465 X ⟶ wppOpCodomainW465 X :=
  (wppOpOrdinaryDiagramW465 X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the W426 descended quotient map. -/
abbrev wppOpOrdinaryQuotientPointW465
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomainW465 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW465 X - wppOpRightW465 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- Ordinary quotient map used by the W426 quotient-compatibility equation. -/
abbrev wppOpOrdinaryQuotientMapW465
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpCodomainW465 X ⟶ wppOpOrdinaryQuotientPointW465 X :=
  MetrizableLCA.quotientMap (wppOpCodomainW465 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW465 X - wppOpRightW465 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The WPP-op image of the ordinary left arrow. -/
abbrev ordinaryLeftHom : ordinarySourceIndex ⟶ ordinaryTargetIndex :=
  walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left

/-- W318/W451 per-object compatibility for a map between WPP-op colimit points. -/
abbrev W318ConjugatedLegCompatibilityW465
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- The ordinary-source component equation of W451's concrete leg compatibility. -/
abbrev ordinarySourceComponentEquationW465
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinarySourceIndex ≫ φ =
    α.app ordinarySourceIndex ≫ cy.ι.app ordinarySourceIndex

/-- The ordinary-target component equation of W451's concrete leg compatibility. -/
abbrev ordinaryTargetComponentEquationW465
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinaryTargetIndex ≫ φ =
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex

/--
The ordinary source equation follows from the ordinary target equation by
composing with the WPP-op left arrow and using cocone naturality on both sides
together with naturality of `α`.
-/
theorem source_component_of_target_component_w465
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquationW465 X Y α cx cy φ) :
    ordinarySourceComponentEquationW465 X Y α cx cy φ := by
  change cx.ι.app ordinarySourceIndex ≫ φ =
    α.app ordinarySourceIndex ≫ cy.ι.app ordinarySourceIndex
  have htarget' :
      cx.ι.app ordinaryTargetIndex ≫ φ =
        α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex :=
    htarget
  have h0 :
      cx.ι.app ordinarySourceIndex ≫ φ =
        (X.map ordinaryLeftHom ≫ cx.ι.app ordinaryTargetIndex) ≫ φ :=
    congrArg (fun f => f ≫ φ) (cx.w ordinaryLeftHom).symm
  have h1 :
      (X.map ordinaryLeftHom ≫ cx.ι.app ordinaryTargetIndex) ≫ φ =
        (X.map ordinaryLeftHom ≫ α.app ordinaryTargetIndex) ≫
          cy.ι.app ordinaryTargetIndex := by
    simpa only [Category.assoc] using
      congrArg (fun f => X.map ordinaryLeftHom ≫ f) htarget'
  have h2 :
      (X.map ordinaryLeftHom ≫ α.app ordinaryTargetIndex) ≫
          cy.ι.app ordinaryTargetIndex =
        (α.app ordinarySourceIndex ≫ Y.map ordinaryLeftHom) ≫
          cy.ι.app ordinaryTargetIndex :=
    congrArg (fun f => f ≫ cy.ι.app ordinaryTargetIndex) (α.naturality ordinaryLeftHom)
  have h3 :
      (α.app ordinarySourceIndex ≫ Y.map ordinaryLeftHom) ≫
          cy.ι.app ordinaryTargetIndex =
        α.app ordinarySourceIndex ≫ cy.ι.app ordinarySourceIndex := by
    simpa only [Category.assoc] using
      congrArg (fun f => α.app ordinarySourceIndex ≫ f) (cy.w ordinaryLeftHom)
  exact h0.trans (h1.trans (h2.trans h3))

/-- W318/W451 compatibility follows from only the target-index component. -/
theorem w318_conjugatedLegCompatibility_of_target_component_w465
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquationW465 X Y α cx cy φ) :
    W318ConjugatedLegCompatibilityW465 X Y α cx cy φ := by
  intro j
  cases j using Opposite.rec
  rename_i j
  cases j
  · simpa [ordinaryTargetIndex] using htarget
  · simpa [ordinarySourceIndex] using source_component_of_target_component_w465 htarget

/-- Conjugate an ordinary descended map across W387 point identifications. -/
def transportedDescendedByPointIsoConjugacyW465
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    colimitSource ⟶ colimitTarget :=
  sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom

/--
Inputs that reduce the ordinary-target component to W426 quotient
compatibility and the two W387 point-identification leg equations.
-/
structure W426TargetLegPointIdentificationInputsW465
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinaryMap : wppOpOrdinaryDiagramW465 X ⟶ wppOpOrdinaryDiagramW465 Y
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW465 X ⟶ wppOpOrdinaryQuotientPointW465 Y
  sourcePointIdentification : wppOpOrdinaryQuotientPointW465 X ≅ cx.pt
  targetPointIdentification : wppOpOrdinaryQuotientPointW465 Y ≅ cy.pt
  w426OrdinaryDescendedName : String
  w426QuotientCompatibilityName : String
  w387SourcePointIdentificationName : String
  w387TargetPointIdentificationName : String
  quotient_compat :
    wppOpOrdinaryQuotientMapW465 X ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫ wppOpOrdinaryQuotientMapW465 Y
  sourcePointIdentification_target_leg :
    cx.ι.app ordinaryTargetIndex ≫ sourcePointIdentification.inv =
      wppOpOrdinaryQuotientMapW465 X
  targetPointIdentification_target_leg :
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex =
      ordinaryMap.app WalkingParallelPair.one ≫
        wppOpOrdinaryQuotientMapW465 Y ≫ targetPointIdentification.hom

/-- The concrete W390-conjugated W426 ordinary descended map on colimit points. -/
def W426TargetLegPointIdentificationInputsW465.concreteConjugatedDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW465 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  transportedDescendedByPointIsoConjugacyW465
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/--
The target component follows by associativity from W426 quotient compatibility
after replacing the source and target point-identification legs.
-/
theorem target_component_of_quotient_compat_and_point_identifications_w465
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW465 X Y α cx cy) :
    ordinaryTargetComponentEquationW465 X Y α cx cy
      inputs.concreteConjugatedDescended := by
  have hcalc :
      ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
          inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
        α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
    have hsource :
        ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (wppOpOrdinaryQuotientMapW465 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom :=
      congrArg
        (fun f => (f ≫ inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom)
        inputs.sourcePointIdentification_target_leg
    have hquotient :
        (wppOpOrdinaryQuotientMapW465 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW465 Y) ≫
              inputs.targetPointIdentification.hom :=
      congrArg (fun f => f ≫ inputs.targetPointIdentification.hom) inputs.quotient_compat
    have htarget :
        (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW465 Y) ≫
              inputs.targetPointIdentification.hom =
          α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
      simpa only [Category.assoc] using inputs.targetPointIdentification_target_leg.symm
    exact hsource.trans (hquotient.trans htarget)
  simpa only
    [W426TargetLegPointIdentificationInputsW465.concreteConjugatedDescended,
      transportedDescendedByPointIsoConjugacyW465, Category.assoc] using hcalc

/--
W426 quotient compatibility plus point-identification leg equations imply full
W318/W451 leg compatibility for the concrete conjugated descended map.
-/
theorem w318_conjugatedLegCompatibility_of_quotient_compat_point_identifications_w465
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW465 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW465 X Y α cx cy
      inputs.concreteConjugatedDescended :=
  w318_conjugatedLegCompatibility_of_target_component_w465
    (target_component_of_quotient_compat_and_point_identifications_w465 inputs)

/-- Exact concrete fields needed to instantiate the W465 reduction. -/
def remainingW426FullW318LegInputsW465 : List String :=
  ["W426 ordinary descended map as `ordinaryDescended`",
    "W426 quotient compatibility as `quotient_compat`",
    "W387 source point identification with target leg `cx.ι.app ordinaryTargetIndex ≫ sourcePointIdentification.inv = quotientMapX`",
    "W387 target point identification with target leg `α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex = ordinaryMap.app WalkingParallelPair.one ≫ quotientMapY ≫ targetPointIdentification.hom`"]

/-- Checked declarations exported by W465. -/
def w465CheckedDeclarationNames : List String :=
  ["supportSeed",
    "wppOpOrdinaryDiagramW465",
    "wppOpOrdinaryQuotientPointW465",
    "wppOpOrdinaryQuotientMapW465",
    "ordinarySourceIndex",
    "ordinaryTargetIndex",
    "ordinaryLeftHom",
    "W318ConjugatedLegCompatibilityW465",
    "ordinarySourceComponentEquationW465",
    "ordinaryTargetComponentEquationW465",
    "source_component_of_target_component_w465",
    "w318_conjugatedLegCompatibility_of_target_component_w465",
    "transportedDescendedByPointIsoConjugacyW465",
    "W426TargetLegPointIdentificationInputsW465",
    "W426TargetLegPointIdentificationInputsW465.concreteConjugatedDescended",
    "target_component_of_quotient_compat_and_point_identifications_w465",
    "w318_conjugatedLegCompatibility_of_quotient_compat_point_identifications_w465",
    "remainingW426FullW318LegInputsW465"]

theorem w465CheckedDeclarationNames_count :
    w465CheckedDeclarationNames.length = 18 := rfl

end WppOpW426QuotientCompatFullW318LegV370SupportW465

end LeanLCAExactChallenge
