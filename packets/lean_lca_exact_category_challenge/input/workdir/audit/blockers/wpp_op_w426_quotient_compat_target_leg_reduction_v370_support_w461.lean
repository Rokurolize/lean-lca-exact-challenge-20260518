import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W461: reduce W458's ordinary target-component frontier to W426 quotient
compatibility plus the two point-identification leg equations.

This file is intentionally standalone.  It copies the small W441/W458 surface
needed for the categorical calculation and records the exact W426/W387 fields
that instantiate it.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426QuotientCompatTargetLegReductionV370SupportW461

/-- Required random seed for this support-search branch. -/
def supportSeed : String :=
  "484bac0455dda250b38772e676eb6c9a"

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW461 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomainW461 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW461 X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomainW461 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW461 X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeftW461 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW461 X ⟶ wppOpCodomainW461 X :=
  (wppOpOrdinaryDiagramW461 X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRightW461 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW461 X ⟶ wppOpCodomainW461 X :=
  (wppOpOrdinaryDiagramW461 X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the W426 descended quotient map. -/
abbrev wppOpOrdinaryQuotientPointW461
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomainW461 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW461 X - wppOpRightW461 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- Ordinary quotient map used by the W426 quotient-compatibility equation. -/
abbrev wppOpOrdinaryQuotientMapW461
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpCodomainW461 X ⟶ wppOpOrdinaryQuotientPointW461 X :=
  MetrizableLCA.quotientMap (wppOpCodomainW461 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW461 X - wppOpRightW461 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- W318/W451 per-object compatibility for a map between WPP-op colimit points. -/
abbrev W318ConjugatedLegCompatibilityW461
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- The ordinary-target component equation of W451's concrete leg compatibility. -/
abbrev ordinaryTargetComponentEquationW461
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinaryTargetIndex ≫ φ =
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex

/-- Conjugate an ordinary descended map across W387 point identifications. -/
def transportedDescendedByPointIsoConjugacyW461
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    colimitSource ⟶ colimitTarget :=
  sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom

/--
Inputs that reduce W458's remaining ordinary-target component to W426 quotient
compatibility and the two W387 point-identification leg equations.
-/
structure W426TargetLegPointIdentificationInputsW461
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinaryMap : wppOpOrdinaryDiagramW461 X ⟶ wppOpOrdinaryDiagramW461 Y
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW461 X ⟶ wppOpOrdinaryQuotientPointW461 Y
  sourcePointIdentification : wppOpOrdinaryQuotientPointW461 X ≅ cx.pt
  targetPointIdentification : wppOpOrdinaryQuotientPointW461 Y ≅ cy.pt
  w426OrdinaryDescendedName : String
  w426QuotientCompatibilityName : String
  w387SourcePointIdentificationName : String
  w387TargetPointIdentificationName : String
  quotient_compat :
    wppOpOrdinaryQuotientMapW461 X ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫ wppOpOrdinaryQuotientMapW461 Y
  sourcePointIdentification_target_leg :
    cx.ι.app ordinaryTargetIndex ≫ sourcePointIdentification.inv =
      wppOpOrdinaryQuotientMapW461 X
  targetPointIdentification_target_leg :
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex =
      ordinaryMap.app WalkingParallelPair.one ≫
        wppOpOrdinaryQuotientMapW461 Y ≫ targetPointIdentification.hom

/-- The concrete W390-conjugated W426 ordinary descended map on colimit points. -/
def W426TargetLegPointIdentificationInputsW461.concreteConjugatedDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW461 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  transportedDescendedByPointIsoConjugacyW461
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/--
W458's target component follows by associativity from W426 quotient
compatibility after replacing the source and target point-identification legs.
-/
theorem target_component_of_quotient_compat_and_point_identifications_w461
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW461 X Y α cx cy) :
    ordinaryTargetComponentEquationW461 X Y α cx cy
      inputs.concreteConjugatedDescended := by
  have hcalc :
      ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
          inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
        α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
    have hsource :
        ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (wppOpOrdinaryQuotientMapW461 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom :=
      congrArg
        (fun f => (f ≫ inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom)
        inputs.sourcePointIdentification_target_leg
    have hquotient :
        (wppOpOrdinaryQuotientMapW461 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW461 Y) ≫
              inputs.targetPointIdentification.hom :=
      congrArg (fun f => f ≫ inputs.targetPointIdentification.hom) inputs.quotient_compat
    have htarget :
        (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW461 Y) ≫
              inputs.targetPointIdentification.hom =
          α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
      simpa only [Category.assoc] using inputs.targetPointIdentification_target_leg.symm
    exact hsource.trans (hquotient.trans htarget)
  simpa only
    [W426TargetLegPointIdentificationInputsW461.concreteConjugatedDescended,
      transportedDescendedByPointIsoConjugacyW461, Category.assoc] using hcalc

/--
The W318/W451 compatibility remains the W458 target-component frontier:
instantiate W458's checked reduction with
`target_component_of_quotient_compat_and_point_identifications_w461`.
-/
structure W318ConjugatedLegReductionInputsW461
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  pointIdentificationInputs :
    W426TargetLegPointIdentificationInputsW461 X Y α cx cy
  targetComponentImpliesW318 :
    ordinaryTargetComponentEquationW461 X Y α cx cy
        pointIdentificationInputs.concreteConjugatedDescended →
      W318ConjugatedLegCompatibilityW461 X Y α cx cy
        pointIdentificationInputs.concreteConjugatedDescended
  targetComponentReductionName : String

/--
Combining this file's W426 quotient-compatibility target-leg calculation with
W458's target-component-to-all-components theorem gives the desired
W318/W451 concrete leg compatibility.
-/
theorem w318_conjugatedLegCompatibility_of_quotient_compat_target_leg_w461
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W318ConjugatedLegReductionInputsW461 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW461 X Y α cx cy
      inputs.pointIdentificationInputs.concreteConjugatedDescended :=
  inputs.targetComponentImpliesW318
    (target_component_of_quotient_compat_and_point_identifications_w461
      inputs.pointIdentificationInputs)

/-- Exact concrete fields needed to instantiate the W426/W387/W390 target-leg reduction. -/
def remainingW426TargetLegInputsW461 : List String :=
  ["W426 ordinary descended map as `ordinaryDescended`",
    "W426 quotient compatibility as `quotient_compat`",
    "W387 source point identification with target leg `cx.ι.app ordinaryTargetIndex ≫ sourcePointIdentification.inv = quotientMapX`",
    "W387 target point identification with target leg `α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex = ordinaryMap.app WalkingParallelPair.one ≫ quotientMapY ≫ targetPointIdentification.hom`",
    "W458 theorem turning the ordinary-target component into all W318/W451 components"]

/-- Checked declarations exported by W461. -/
def w461CheckedDeclarationNames : List String :=
  ["supportSeed",
    "wppOpOrdinaryDiagramW461",
    "wppOpOrdinaryQuotientPointW461",
    "wppOpOrdinaryQuotientMapW461",
    "ordinaryTargetIndex",
    "W318ConjugatedLegCompatibilityW461",
    "ordinaryTargetComponentEquationW461",
    "transportedDescendedByPointIsoConjugacyW461",
    "W426TargetLegPointIdentificationInputsW461",
    "W426TargetLegPointIdentificationInputsW461.concreteConjugatedDescended",
    "target_component_of_quotient_compat_and_point_identifications_w461",
    "W318ConjugatedLegReductionInputsW461",
    "w318_conjugatedLegCompatibility_of_quotient_compat_target_leg_w461",
    "remainingW426TargetLegInputsW461"]

theorem w461CheckedDeclarationNames_count :
    w461CheckedDeclarationNames.length = 14 := rfl

end WppOpW426QuotientCompatTargetLegReductionV370SupportW461

end LeanLCAExactChallenge
