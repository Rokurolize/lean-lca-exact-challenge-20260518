import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W478: standalone bridge from W461-shaped target-leg data to W441-shaped
ordinary-map promotion fields.

The support audit files are not Lake modules, so this file keeps the small
W441/W461 surfaces local.  It records the parent-owned next reduction without
claiming product success: quotient compatibility plus point-identification
target-leg equations give the canonical leg calculation, and the ordinary W426
topology package transports closed-embedding facts to the W318 colimit map.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpW461ToW441PromotionFieldsV370SupportW478

/-- Worker seed recorded for this parent-owned bridge. -/
def supportSeed : String := "parent-w478-w461-to-w441-promotion"

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomainW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW478 X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomainW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW478 X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeftW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW478 X ⟶ wppOpCodomainW478 X :=
  (wppOpOrdinaryDiagramW478 X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRightW478 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW478 X ⟶ wppOpCodomainW478 X :=
  (wppOpOrdinaryDiagramW478 X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the W426 descended quotient map. -/
abbrev wppOpOrdinaryQuotientPointW478
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomainW478 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW478 X - wppOpRightW478 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- Ordinary quotient map used by the W426 quotient-compatibility equation. -/
abbrev wppOpOrdinaryQuotientMapW478
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpCodomainW478 X ⟶ wppOpOrdinaryQuotientPointW478 X :=
  MetrizableLCA.quotientMap (wppOpCodomainW478 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW478 X - wppOpRightW478 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- W318's per-object colimit-map compatibility equation. -/
abbrev W318ColimitMapLegCompatibilityW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- Ordinary W426 descended map package, matching W441's field shape. -/
structure W426OrdinaryDescendedMapPackageW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW478 X ⟶ wppOpOrdinaryDiagramW478 Y) :
    Type 1 where
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW478 X ⟶ wppOpOrdinaryQuotientPointW478 Y
  quotient_compat :
    wppOpOrdinaryQuotientMapW478 X ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫ wppOpOrdinaryQuotientMapW478 Y
  descended_injective :
    Function.Injective (ordinaryDescended :
      wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y)
  descended_inducing :
    IsInducing (ordinaryDescended :
      wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y)
  descended_range_closed :
    IsClosed (Set.range (ordinaryDescended :
      wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y))

/-- W461 target-leg point-identification input shape. -/
structure W426TargetLegPointIdentificationInputsW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinaryMap : wppOpOrdinaryDiagramW478 X ⟶ wppOpOrdinaryDiagramW478 Y
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW478 X ⟶ wppOpOrdinaryQuotientPointW478 Y
  sourcePointIdentification : wppOpOrdinaryQuotientPointW478 X ≅ cx.pt
  targetPointIdentification : wppOpOrdinaryQuotientPointW478 Y ≅ cy.pt
  quotient_compat :
    wppOpOrdinaryQuotientMapW478 X ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫ wppOpOrdinaryQuotientMapW478 Y
  sourcePointIdentification_target_leg :
    cx.ι.app ordinaryTargetIndex ≫ sourcePointIdentification.inv =
      wppOpOrdinaryQuotientMapW478 X
  targetPointIdentification_target_leg :
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex =
      ordinaryMap.app WalkingParallelPair.one ≫
        wppOpOrdinaryQuotientMapW478 Y ≫ targetPointIdentification.hom

/-- Conjugate an ordinary descended map across point identifications. -/
def concreteConjugatedDescendedW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW478 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  inputs.sourcePointIdentification.inv ≫
    inputs.ordinaryDescended ≫ inputs.targetPointIdentification.hom

/-- The ordinary-target component equation of W318's leg compatibility. -/
abbrev ordinaryTargetComponentEquationW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinaryTargetIndex ≫ φ =
    α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex

/-- W426 quotient compatibility plus point-identification legs gives the target component. -/
theorem target_component_of_quotient_compat_and_point_identifications_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426TargetLegPointIdentificationInputsW478 X Y α cx cy) :
    ordinaryTargetComponentEquationW478 X Y α cx cy
      (concreteConjugatedDescendedW478 inputs) := by
  have hcalc :
      ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
          inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
        α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
    have hsource :
        ((cx.ι.app ordinaryTargetIndex ≫ inputs.sourcePointIdentification.inv) ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (wppOpOrdinaryQuotientMapW478 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom :=
      congrArg
        (fun f => (f ≫ inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom)
        inputs.sourcePointIdentification_target_leg
    have hquotient :
        (wppOpOrdinaryQuotientMapW478 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW478 Y) ≫
              inputs.targetPointIdentification.hom :=
      congrArg (fun f => f ≫ inputs.targetPointIdentification.hom) inputs.quotient_compat
    have htarget :
        (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW478 Y) ≫
              inputs.targetPointIdentification.hom =
          α.app ordinaryTargetIndex ≫ cy.ι.app ordinaryTargetIndex := by
      simpa only [Category.assoc] using inputs.targetPointIdentification_target_leg.symm
    exact hsource.trans (hquotient.trans htarget)
  simpa only [concreteConjugatedDescendedW478, Category.assoc] using hcalc

/-- W461-style reduction package from target component to all W318 components. -/
structure W461ToW441PromotionInputs
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  pointIdentificationInputs :
    W426TargetLegPointIdentificationInputsW478 X Y α cx cy
  targetComponentImpliesW318 :
    ordinaryTargetComponentEquationW478 X Y α cx cy
        (concreteConjugatedDescendedW478 pointIdentificationInputs) →
      W318ColimitMapLegCompatibilityW478 X Y α cx cy
        (concreteConjugatedDescendedW478 pointIdentificationInputs)
  ordinaryPackage :
    W426OrdinaryDescendedMapPackageW478 pointIdentificationInputs.ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended =
      pointIdentificationInputs.ordinaryDescended

/-- The concrete conjugated descended map is a closed embedding. -/
theorem concreteConjugatedDescended_closedEmbedding_of_w461_to_w441
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W461ToW441PromotionInputs X Y α cx cy) :
    IsClosedEmbedding (concreteConjugatedDescendedW478
      inputs.pointIdentificationInputs : cx.pt → cy.pt) := by
  let p := inputs.pointIdentificationInputs
  have hordinary :
      IsClosedEmbedding (p.ordinaryDescended :
        wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y) := by
    have hclosed :
        IsClosedEmbedding (inputs.ordinaryPackage.ordinaryDescended :
          wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y) :=
      WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
        (inputs.ordinaryPackage.ordinaryDescended :
          wppOpOrdinaryQuotientPointW478 X → wppOpOrdinaryQuotientPointW478 Y)
        inputs.ordinaryPackage.descended_injective
        inputs.ordinaryPackage.descended_inducing
        inputs.ordinaryPackage.descended_range_closed
    simpa [inputs.ordinaryDescended_eq] using hclosed
  let sourceHomeomorph : cx.pt ≃ₜ+ wppOpOrdinaryQuotientPointW478 X :=
    MetrizableLCA.isoToContinuousAddEquiv p.sourcePointIdentification.symm
  let targetHomeomorph : wppOpOrdinaryQuotientPointW478 Y ≃ₜ+ cy.pt :=
    MetrizableLCA.isoToContinuousAddEquiv p.targetPointIdentification
  have hcomp :
      IsClosedEmbedding
        (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) :=
    targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
      (hordinary.comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
  have hfun :
      (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) =
        (concreteConjugatedDescendedW478 p : cx.pt → cy.pt) := by
    funext x
    rfl
  simpa [hfun] using hcomp

/-- W461's concrete map and any W318-compatible map out of `cx` are equal. -/
theorem eq_concreteConjugatedDescended_of_w461_compat
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (inputs : W461ToW441PromotionInputs X Y α cx cy)
    (hcompat : W318ColimitMapLegCompatibilityW478 X Y α cx cy φ) :
    φ = concreteConjugatedDescendedW478 inputs.pointIdentificationInputs := by
  apply hcx.hom_ext
  intro j
  have hconcrete :
      cx.ι.app j ≫ concreteConjugatedDescendedW478 inputs.pointIdentificationInputs =
        α.app j ≫ cy.ι.app j :=
    inputs.targetComponentImpliesW318
      (target_component_of_quotient_compat_and_point_identifications_w478
        inputs.pointIdentificationInputs) j
  exact (hcompat j).trans hconcrete.symm

/-- W441-shaped promotion fields, kept local to avoid pretending product completion. -/
structure W441PromotionFieldsW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW478 X ⟶ wppOpOrdinaryDiagramW478 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) :
    Type 1 where
  ordinaryPackage : W426OrdinaryDescendedMapPackageW478 ordinaryMap
  ordinaryEqualsCanonicalColimitMap : Prop
  ordinaryEqualsCanonicalImpliesLegCompatibility :
    ordinaryEqualsCanonicalColimitMap →
      W318ColimitMapLegCompatibilityW478 X Y α cx cy φ
  ordinaryTopologyTransportsToColimitMap :
    ordinaryEqualsCanonicalColimitMap →
      Function.Injective (φ : cx.pt → cy.pt) ∧
        IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt))

/-- W461 plus the ordinary package supplies W441-shaped promotion fields. -/
def w441PromotionFields_of_w461_to_w441
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (inputs : W461ToW441PromotionInputs X Y α cx cy)
    (hcompat : W318ColimitMapLegCompatibilityW478 X Y α cx cy φ) :
    W441PromotionFieldsW478 inputs.pointIdentificationInputs.ordinaryMap α cx cy φ where
  ordinaryPackage := inputs.ordinaryPackage
  ordinaryEqualsCanonicalColimitMap := IsColimit.map hcx cy α = φ
  ordinaryEqualsCanonicalImpliesLegCompatibility := by
    intro heq j
    simpa [heq] using IsColimit.ι_map hcx cy α j
  ordinaryTopologyTransportsToColimitMap := by
    intro _heq
    have hclosedConcrete :=
      concreteConjugatedDescended_closedEmbedding_of_w461_to_w441 inputs
    have hφ :
        IsClosedEmbedding (φ : cx.pt → cy.pt) := by
      have hEq := eq_concreteConjugatedDescended_of_w461_compat hcx inputs hcompat
      simpa [hEq] using hclosedConcrete
    exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/-- The equality input required by W441 follows from the same compatibility equation. -/
theorem ordinaryEqualsCanonicalColimitMap_of_w461_to_w441
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (hcompat : W318ColimitMapLegCompatibilityW478 X Y α cx cy φ) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/-- Machine-readable W478 support state. -/
structure WppOpW461ToW441PromotionFieldsV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  promotionFieldsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W478. -/
def currentWppOpW461ToW441PromotionFieldsV370SupportState :
    WppOpW461ToW441PromotionFieldsV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["W426OrdinaryDescendedMapPackageW478",
      "W426TargetLegPointIdentificationInputsW478",
      "target_component_of_quotient_compat_and_point_identifications_w478",
      "W461ToW441PromotionInputs",
      "concreteConjugatedDescended_closedEmbedding_of_w461_to_w441",
      "eq_concreteConjugatedDescended_of_w461_compat",
      "W441PromotionFieldsW478",
      "w441PromotionFields_of_w461_to_w441",
      "ordinaryEqualsCanonicalColimitMap_of_w461_to_w441"]
  promotionFieldsResult :=
    "proved: W461-shaped point-identification target-leg data plus a matching ordinary package construct W441-shaped promotion fields"
  remainingInputs :=
    ["Promote this standalone W478 surface into the importable W441/W461 namespaces or reimplement the bridge there.",
      "Provide concrete W461 target-leg point-identification inputs at every W441 call site.",
      "Provide the matching W426 ordinary descended package and equality to W461's ordinary descended map.",
      "Provide W471 component-colimit comparison inputs for the exact-acyclic endpoint."]
  productSuccessClaimed := false

theorem currentWppOpW461ToW441PromotionFieldsV370SupportState_productSuccess :
    currentWppOpW461ToW441PromotionFieldsV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check W426OrdinaryDescendedMapPackageW478
#check W426TargetLegPointIdentificationInputsW478
#check target_component_of_quotient_compat_and_point_identifications_w478
#check W461ToW441PromotionInputs
#check concreteConjugatedDescended_closedEmbedding_of_w461_to_w441
#check eq_concreteConjugatedDescended_of_w461_compat
#check W441PromotionFieldsW478
#check w441PromotionFields_of_w461_to_w441
#check ordinaryEqualsCanonicalColimitMap_of_w461_to_w441
#check currentWppOpW461ToW441PromotionFieldsV370SupportState_productSuccess

end Checks

end WppOpW461ToW441PromotionFieldsV370SupportW478

end LeanLCAExactChallenge
