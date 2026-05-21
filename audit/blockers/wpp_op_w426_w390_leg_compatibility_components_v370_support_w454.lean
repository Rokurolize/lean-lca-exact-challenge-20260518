import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W454: component reduction for W451's concrete WPP-op leg compatibility.

W451 left the remaining concrete W426/W387/W390 frontier as a pointwise
compatibility over every `WalkingParallelPairᵒᵖ` object.  This support file
replaces that field by the two explicit component equations at the ordinary
source and ordinary target indices.  It also checks the categorical reduction
that the ordinary source component follows from the ordinary target component
and WPP-op cocone/naturality equations.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426W390LegCompatibilityComponentsV370SupportW454

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
abbrev W318ConjugatedLegCompatibilityW454
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
Checked replacement for W451's single `∀ j` field: callers supply the two
ordinary WPP-op component equations explicitly.
-/
structure W451ConcreteLegCompatibilityComponents
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop where
  source_component : ordinarySourceComponentEquation X Y α cx cy φ
  target_component : ordinaryTargetComponentEquation X Y α cx cy φ

/-- The target-index component projected from the checked component package. -/
theorem target_component_of_components_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h : W451ConcreteLegCompatibilityComponents X Y α cx cy φ) :
    ordinaryTargetComponentEquation X Y α cx cy φ :=
  h.target_component

/-- The source-index component projected from the checked component package. -/
theorem source_component_of_components_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h : W451ConcreteLegCompatibilityComponents X Y α cx cy φ) :
    ordinarySourceComponentEquation X Y α cx cy φ :=
  h.source_component

/--
The ordinary source equation follows from the ordinary target equation by
composing with the WPP-op left arrow and using cocone naturality on both sides
together with naturality of `α`.
-/
theorem source_component_of_target_component_w454
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

/--
A target-index proof is enough to build the full two-component package, since
the source-index proof is forced by WPP-op cocone/naturality.
-/
def components_of_target_component_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquation X Y α cx cy φ) :
    W451ConcreteLegCompatibilityComponents X Y α cx cy φ where
  source_component := source_component_of_target_component_w454 htarget
  target_component := htarget

/-- The two explicit WPP-op components imply W451's original `∀ j` compatibility. -/
theorem w318_conjugatedLegCompatibility_of_components_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h : W451ConcreteLegCompatibilityComponents X Y α cx cy φ) :
    W318ConjugatedLegCompatibilityW454 X Y α cx cy φ := by
  intro j
  cases j using Opposite.rec
  rename_i j
  cases j
  · simpa [ordinaryTargetIndex] using h.target_component
  · simpa [ordinarySourceIndex] using h.source_component

/-- W451's original compatibility follows from only the target-index component. -/
theorem w318_conjugatedLegCompatibility_of_target_component_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquation X Y α cx cy φ) :
    W318ConjugatedLegCompatibilityW454 X Y α cx cy φ :=
  w318_conjugatedLegCompatibility_of_components_w454
    (components_of_target_component_w454 htarget)

/--
Shape of the still-needed target equation for W426/W387/W390.

W390's pointwise conjugacy identifies the concrete transported map with the
point-isomorphism conjugate of W426's ordinary descended quotient map.  To
finish the target component, the promoted W426 quotient-map compatibility must
be stated after the target point identification and target WPP-op cocone leg
are instantiated.
-/
abbrev TargetComponentFromW390AndQuotientCompatibilityInput
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ordinaryTargetComponentEquation X Y α cx cy φ

/-- Consuming the exact target-index W390/quotient-compatibility equation. -/
theorem target_component_of_w390_quotient_compat_input_w454
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h :
      TargetComponentFromW390AndQuotientCompatibilityInput X Y α cx cy φ) :
    ordinaryTargetComponentEquation X Y α cx cy φ :=
  h

/-- Checked declarations exported by W454. -/
def w454CheckedDeclarationNames : List String :=
  ["ordinarySourceIndex",
    "ordinaryTargetIndex",
    "ordinaryLeftHom",
    "W318ConjugatedLegCompatibilityW454",
    "ordinarySourceComponentEquation",
    "ordinaryTargetComponentEquation",
    "W451ConcreteLegCompatibilityComponents",
    "target_component_of_components_w454",
    "source_component_of_components_w454",
    "source_component_of_target_component_w454",
    "components_of_target_component_w454",
    "w318_conjugatedLegCompatibility_of_components_w454",
    "w318_conjugatedLegCompatibility_of_target_component_w454",
    "TargetComponentFromW390AndQuotientCompatibilityInput",
    "target_component_of_w390_quotient_compat_input_w454"]

theorem w454CheckedDeclarationNames_count :
    w454CheckedDeclarationNames.length = 15 := rfl

/-- Remaining concrete inputs after W454's component reduction. -/
def remainingConcreteLegComponentInputsW454 : List String :=
  ["promote W451/W447/W444 definitions into importable modules or copy the W454 component package into the final module",
    "instantiate phi with W451's transportedDescendedByPointIsoConjugacyW451 concreteConjugatedDescended map",
    "prove the target-index equation cx.ι.app ordinaryTargetIndex ≫ concreteConjugatedDescended = α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex from W390 pointwise conjugacy and W426 quotient-map compatibility after the W387 target point identification",
    "then apply w318_conjugatedLegCompatibility_of_target_component_w454; the ordinary-source equation is no longer a separate mathematical input"]

theorem remainingConcreteLegComponentInputsW454_count :
    remainingConcreteLegComponentInputsW454.length = 4 := rfl

/-- Machine-readable state for the W454 support file. -/
structure WppOpW426W390LegCompatibilityComponentsV370StateW454 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  componentReductionResult : String
  targetComponentResult : String
  sourceComponentResult : String
  productSuccessClaimed : Bool

def currentWppOpW426W390LegCompatibilityComponentsV370StateW454 :
    WppOpW426W390LegCompatibilityComponentsV370StateW454 where
  seed := "a859ad8f6682a2609375b638e131d7fb"
  declarations := w454CheckedDeclarationNames
  remainingInputs := remainingConcreteLegComponentInputsW454
  componentReductionResult :=
    "proved: the two explicit ordinarySourceIndex/ordinaryTargetIndex equations imply W451-style W318ConjugatedLegCompatibility"
  targetComponentResult :=
    "partial: isolated the exact target-index equation to prove from W390 pointwise conjugacy and W426 quotient-map compatibility"
  sourceComponentResult :=
    "proved: source component follows from the target component by WPP-op left-arrow cocone naturality and naturality of alpha"
  productSuccessClaimed := false

theorem currentWppOpW426W390LegCompatibilityComponentsV370StateW454_productSuccess :
    currentWppOpW426W390LegCompatibilityComponentsV370StateW454.productSuccessClaimed = false := rfl

section Checks

#check ordinarySourceIndex
#check ordinaryTargetIndex
#check ordinaryLeftHom
#check W318ConjugatedLegCompatibilityW454
#check ordinarySourceComponentEquation
#check ordinaryTargetComponentEquation
#check W451ConcreteLegCompatibilityComponents
#check target_component_of_components_w454
#check source_component_of_components_w454
#check source_component_of_target_component_w454
#check components_of_target_component_w454
#check w318_conjugatedLegCompatibility_of_components_w454
#check w318_conjugatedLegCompatibility_of_target_component_w454
#check TargetComponentFromW390AndQuotientCompatibilityInput
#check target_component_of_w390_quotient_compat_input_w454
#check w454CheckedDeclarationNames
#check remainingConcreteLegComponentInputsW454
#check currentWppOpW426W390LegCompatibilityComponentsV370StateW454
#check currentWppOpW426W390LegCompatibilityComponentsV370StateW454_productSuccess

end Checks

end WppOpW426W390LegCompatibilityComponentsV370SupportW454

end LeanLCAExactChallenge
