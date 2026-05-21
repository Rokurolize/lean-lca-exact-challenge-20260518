import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W458: target-component frontier for the concrete W426/W387/W390 leg theorem.

W454 showed that W451-style per-object compatibility for a WPP-op cocone map
follows from only the ordinary target component.  This standalone support file
connects that reduction to W451's concrete point-isomorphism-conjugated
descended map: a concrete W426/W387/W390 input package now needs just the
ordinary target-index equation for the transported descended map.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426W390TargetComponentFrontierV370SupportW458

/-- Required random seed for this support-search branch. -/
def supportSeed : String :=
  "897db823ac95dd46f9443214e0137cb9"

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The WPP-op image of the ordinary left arrow. -/
abbrev ordinaryLeftHom : ordinarySourceIndex ⟶ ordinaryTargetIndex :=
  walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left

/-- W451/W318 per-object compatibility for a map between WPP-op colimit points. -/
abbrev W318ConjugatedLegCompatibilityW458
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- The ordinary-source component equation of W451's concrete leg compatibility. -/
abbrev ordinarySourceComponentEquation
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinarySourceIndex ≫ φ =
    α.app ordinarySourceIndex ≫ cy.ι.app ordinarySourceIndex

/-- The ordinary-target component equation of W451's concrete leg compatibility. -/
abbrev ordinaryTargetComponentEquation
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinaryTargetIndex ≫ φ =
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex

/--
The ordinary source equation follows from the ordinary target equation by
composing with the WPP-op left arrow and using cocone naturality on both sides
together with naturality of `α`.
-/
theorem source_component_of_target_component_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquation X Y α cx cy φ) :
    ordinarySourceComponentEquation X Y α cx cy φ := by
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

/-- W451's original compatibility follows from only the target-index component. -/
theorem w318_conjugatedLegCompatibility_of_target_component_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquation X Y α cx cy φ) :
    W318ConjugatedLegCompatibilityW458 X Y α cx cy φ := by
  intro j
  cases j using Opposite.rec
  rename_i j
  cases j
  · simpa [ordinaryTargetIndex] using htarget
  · simpa [ordinarySourceIndex] using source_component_of_target_component_w458 htarget

/--
The concrete W390 transported descended map: conjugate an ordinary descended
map across W387's source and target point identifications.
-/
def transportedDescendedByPointIsoConjugacyW458
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    colimitSource ⟶ colimitTarget :=
  sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom

/-- The concrete W390 map satisfies its pointwise conjugacy by reduction. -/
theorem transportedDescendedByPointIsoConjugacyW458_pointwise
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    ∀ x : colimitSource,
      transportedDescendedByPointIsoConjugacyW458
          sourcePointIdentification targetPointIdentification ordinaryDescended x =
        targetPointIdentification.hom
          (ordinaryDescended (sourcePointIdentification.inv x)) := by
  intro x
  rfl

/--
The narrowed W426/W387/W390 input package after W454.

Compared with W451's concrete package, this stores only the ordinary target
component for the transported descended map.  WPP-op naturality then supplies
the ordinary source component and hence the original W318/W451 per-object
compatibility.
-/
structure W426W387W390ConcreteTargetComponentInputsW458
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinarySource : MetrizableLCA.{0}
  ordinaryTarget : MetrizableLCA.{0}
  ordinaryDescended : ordinarySource ⟶ ordinaryTarget
  sourcePointIdentification : ordinarySource ≅ cx.pt
  targetPointIdentification : ordinaryTarget ≅ cy.pt
  w426OrdinaryDescendedName : String
  w426QuotientCompatibilityName : String
  w387SourcePointIdentificationName : String
  w387TargetPointIdentificationName : String
  w390ConjugatedMapName : String
  w390PointwiseConjugacyName : String
  w454ReductionName : String
  targetComponentCompatibility :
    ordinaryTargetComponentEquation X Y α cx cy
      (transportedDescendedByPointIsoConjugacyW458
        sourcePointIdentification targetPointIdentification ordinaryDescended)

/-- The concrete W390-conjugated W426 ordinary descended map on colimit points. -/
def W426W387W390ConcreteTargetComponentInputsW458.concreteConjugatedDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteTargetComponentInputsW458 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  transportedDescendedByPointIsoConjugacyW458
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/-- W390's pointwise conjugacy specialized to the narrowed concrete input package. -/
theorem concreteConjugatedDescended_pointwise_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteTargetComponentInputsW458 X Y α cx cy) :
    ∀ x : cx.pt,
      inputs.concreteConjugatedDescended x =
        inputs.targetPointIdentification.hom
          (inputs.ordinaryDescended (inputs.sourcePointIdentification.inv x)) :=
  transportedDescendedByPointIsoConjugacyW458_pointwise
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/-- The target component projected from the concrete W426/W387/W390 input package. -/
theorem target_component_of_concrete_inputs_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteTargetComponentInputsW458 X Y α cx cy) :
    ordinaryTargetComponentEquation X Y α cx cy
      inputs.concreteConjugatedDescended :=
  inputs.targetComponentCompatibility

/--
The W451/W318 compatibility for the concrete conjugated descended map follows
from the single ordinary-target component field.
-/
theorem w318_conjugatedLegCompatibility_of_concrete_target_component_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteTargetComponentInputsW458 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW458 X Y α cx cy
      inputs.concreteConjugatedDescended :=
  w318_conjugatedLegCompatibility_of_target_component_w458
    (target_component_of_concrete_inputs_w458 inputs)

/--
Explicit name for the remaining W426 quotient and W390 point-identification
calculation at the ordinary target object.
-/
abbrev TargetComponentFromW390PointwiseAndQuotientInputW458
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y)
    (φ : cx.pt ⟶ cy.pt) : Prop :=
  ordinaryTargetComponentEquation X Y α cx cy φ

/--
Consuming the explicit target-leg calculation is enough to finish W451's
concrete per-object compatibility for the supplied map.
-/
theorem target_component_frontier_from_w390_pointwise_and_quotient_w458
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h :
      TargetComponentFromW390PointwiseAndQuotientInputW458 X Y α cx cy φ) :
    W318ConjugatedLegCompatibilityW458 X Y α cx cy φ :=
  w318_conjugatedLegCompatibility_of_target_component_w458 h

/-- Checked declarations exported by W458. -/
def w458CheckedDeclarationNames : List String :=
  ["supportSeed",
    "ordinarySourceIndex",
    "ordinaryTargetIndex",
    "ordinaryLeftHom",
    "W318ConjugatedLegCompatibilityW458",
    "ordinarySourceComponentEquation",
    "ordinaryTargetComponentEquation",
    "source_component_of_target_component_w458",
    "w318_conjugatedLegCompatibility_of_target_component_w458",
    "transportedDescendedByPointIsoConjugacyW458",
    "transportedDescendedByPointIsoConjugacyW458_pointwise",
    "W426W387W390ConcreteTargetComponentInputsW458",
    "W426W387W390ConcreteTargetComponentInputsW458.concreteConjugatedDescended",
    "concreteConjugatedDescended_pointwise_w458",
    "target_component_of_concrete_inputs_w458",
    "w318_conjugatedLegCompatibility_of_concrete_target_component_w458",
    "TargetComponentFromW390PointwiseAndQuotientInputW458",
    "target_component_frontier_from_w390_pointwise_and_quotient_w458"]

theorem w458CheckedDeclarationNames_count :
    w458CheckedDeclarationNames.length = 18 := rfl

/-- Remaining concrete inputs after W458's target-component frontier. -/
def remainingTargetComponentFrontierInputsW458 : List String :=
  ["promote W426's ordinary descended map and quotient-compatibility theorem into an importable module",
    "promote W387's source and target point identifications into the same importable namespace",
    "instantiate the W390 transported descended map as sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom",
    "prove only the ordinaryTargetIndex component equation from W390 pointwise conjugacy plus W426 quotient compatibility after the W387 target point identification",
    "then apply w318_conjugatedLegCompatibility_of_concrete_target_component_w458; the ordinarySourceIndex component is forced by WPP-op naturality"]

theorem remainingTargetComponentFrontierInputsW458_count :
    remainingTargetComponentFrontierInputsW458.length = 5 := rfl

/-- Machine-readable state for the W458 support file. -/
structure WppOpW426W390TargetComponentFrontierV370StateW458 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  targetComponentResult : String
  w318LegResult : String
  productSuccessClaimed : Bool

def currentWppOpW426W390TargetComponentFrontierV370StateW458 :
    WppOpW426W390TargetComponentFrontierV370StateW458 where
  seed := supportSeed
  declarations := w458CheckedDeclarationNames
  remainingInputs := remainingTargetComponentFrontierInputsW458
  targetComponentResult :=
    "partial: narrowed W451's concrete leg theorem to the ordinaryTargetIndex equation for the W390-conjugated W426 descended map"
  w318LegResult :=
    "proved conditional reduction: the concrete W318/W451 per-object compatibility follows from that target component"
  productSuccessClaimed := false

theorem currentWppOpW426W390TargetComponentFrontierV370StateW458_productSuccess :
    currentWppOpW426W390TargetComponentFrontierV370StateW458.productSuccessClaimed = false := rfl

section Checks

#check supportSeed
#check ordinarySourceIndex
#check ordinaryTargetIndex
#check ordinaryLeftHom
#check W318ConjugatedLegCompatibilityW458
#check ordinarySourceComponentEquation
#check ordinaryTargetComponentEquation
#check source_component_of_target_component_w458
#check w318_conjugatedLegCompatibility_of_target_component_w458
#check transportedDescendedByPointIsoConjugacyW458
#check transportedDescendedByPointIsoConjugacyW458_pointwise
#check W426W387W390ConcreteTargetComponentInputsW458
#check W426W387W390ConcreteTargetComponentInputsW458.concreteConjugatedDescended
#check concreteConjugatedDescended_pointwise_w458
#check target_component_of_concrete_inputs_w458
#check w318_conjugatedLegCompatibility_of_concrete_target_component_w458
#check TargetComponentFromW390PointwiseAndQuotientInputW458
#check target_component_frontier_from_w390_pointwise_and_quotient_w458
#check w458CheckedDeclarationNames
#check remainingTargetComponentFrontierInputsW458
#check currentWppOpW426W390TargetComponentFrontierV370StateW458
#check currentWppOpW426W390TargetComponentFrontierV370StateW458_productSuccess

end Checks

end WppOpW426W390TargetComponentFrontierV370SupportW458

end LeanLCAExactChallenge
