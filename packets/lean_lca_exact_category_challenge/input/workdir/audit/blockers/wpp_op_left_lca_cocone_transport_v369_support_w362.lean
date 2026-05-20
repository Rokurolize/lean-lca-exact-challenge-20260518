import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W362: final cocone transport support for the left-LCA concrete quotient route.

This standalone audit file copies the W357 concrete quotient cocone boundary up
to the inverse-equivalence whiskered diagram, then transports that cocone along
the counit diagram isomorphism to an actual `Cocone X`.  It also packages the
W354-ready source/target fields: transported quotient cocones, colimit proofs, a
descended map, and the pointwise cocone leg equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaCoconeTransportV369SupportW362

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

namespace ConcreteMetrizableLCA

open LeanLCAExactChallenge.MetrizableLCA

variable {A B : MetrizableLCA.{0}}

/-- Concrete quotient cofork for a parallel pair, presented as the cokernel of `f - g`. -/
def concreteQuotientCofork (f g : A ⟶ B) : Cofork f g :=
  Preadditive.coforkOfCokernelCofork
    (CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g)))

/-- The concrete quotient cofork is a colimit by the local cokernel construction. -/
def concreteQuotientCoforkIsColimit (f g : A ⟶ B) :
    IsColimit (concreteQuotientCofork f g) :=
  Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsColimit (f - g))

end ConcreteMetrizableLCA

/--
Concrete quotient cocone on the ordinary diagram associated to a WPP-op
diagram.  Its point is the quotient/cokernel object of the two parallel arrows.
-/
def wppOpConcreteQuotientCoconeOnOrdinary
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    Cocone (wppOpOrdinaryDiagram X) :=
  (Cocone.precompose (diagramIsoParallelPair (wppOpOrdinaryDiagram X)).hom).obj
    (ConcreteMetrizableLCA.concreteQuotientCofork (wppOpLeft X) (wppOpRight X))

/-- The ordinary concrete quotient cocone associated to a WPP-op diagram is a colimit. -/
def wppOpConcreteQuotientCoconeOnOrdinaryIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpConcreteQuotientCoconeOnOrdinary X) :=
  (IsColimit.precomposeHomEquiv
    (diagramIsoParallelPair (wppOpOrdinaryDiagram X))
    (ConcreteMetrizableLCA.concreteQuotientCofork (wppOpLeft X) (wppOpRight X))).symm
    (ConcreteMetrizableLCA.concreteQuotientCoforkIsColimit (wppOpLeft X) (wppOpRight X))

/--
Concrete quotient cocone after whiskering through the inverse equivalence.  This
is the W357 cocone immediately before identifying the resulting diagram with the
original WPP-op diagram.
-/
def wppOpWhiskeredConcreteQuotientCocone
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    Cocone (walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X) :=
  Cocone.whisker walkingParallelPairOpEquiv.inverse
    (wppOpConcreteQuotientCoconeOnOrdinary X)

/-- The whiskered concrete quotient cocone is still a colimit. -/
def wppOpWhiskeredConcreteQuotientCoconeIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpWhiskeredConcreteQuotientCocone X) :=
  IsColimit.whiskerEquivalence
    (wppOpConcreteQuotientCoconeOnOrdinaryIsColimit X)
    walkingParallelPairOpEquiv.symm

/-- Counit-based diagram isomorphism from the whiskered W357 diagram back to `X`. -/
def wppOpWhiskeredDiagramIso
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X ≅ X :=
  (Functor.associator walkingParallelPairOpEquiv.inverse walkingParallelPairOpEquiv.functor X).symm ≪≫
    Functor.isoWhiskerRight walkingParallelPairOpEquiv.counitIso X ≪≫
      Functor.leftUnitor X

/-- The concrete quotient cocone transported to an actual cocone over `X`. -/
def wppOpTransportedConcreteQuotientCocone
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : Cocone X :=
  (Cocone.precompose (wppOpWhiskeredDiagramIso X).symm.hom).obj
    (wppOpWhiskeredConcreteQuotientCocone X)

/-- The transported concrete quotient cocone is a colimit. -/
def wppOpTransportedConcreteQuotientCoconeIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpTransportedConcreteQuotientCocone X) :=
  (IsColimit.precomposeHomEquiv
    (wppOpWhiskeredDiagramIso X).symm
    (wppOpWhiskeredConcreteQuotientCocone X)).symm
    (wppOpWhiskeredConcreteQuotientCoconeIsColimit X)

/-- The transported cocone keeps the whiskered quotient point. -/
theorem wppOpTransportedConcreteQuotientCocone_pt
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    (wppOpTransportedConcreteQuotientCocone X).pt =
      (wppOpWhiskeredConcreteQuotientCocone X).pt :=
  rfl

/-- Transport formula for the cocone leg at an object of `WalkingParallelPairᵒᵖ`. -/
theorem wppOpTransportedConcreteQuotientCocone_ι_app
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (j : WalkingParallelPairᵒᵖ) :
    (wppOpTransportedConcreteQuotientCocone X).ι.app j =
      (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        (wppOpWhiskeredConcreteQuotientCocone X).ι.app j :=
  rfl

/-- Topological relation-pullback fields in the same shape consumed by W354. -/
structure RelationPullbackDescendedFieldsInputsW354Shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/--
W354-ready data with the source and target fixed to the transported concrete
quotient cocones built above.
-/
structure TransportedConcreteQuotientW354Inputs
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 2 where
  hcx : IsColimit cx
  hcy : IsColimit cy
  descended :
    (wppOpTransportedConcreteQuotientCocone X).pt ⟶
      (wppOpTransportedConcreteQuotientCocone Y).pt
  descended_leg :
    ∀ j : WalkingParallelPairᵒᵖ,
      (wppOpTransportedConcreteQuotientCocone X).ι.app j ≫ descended =
        α.app j ≫ (wppOpTransportedConcreteQuotientCocone Y).ι.app j
  relation_inputs :
    RelationPullbackDescendedFieldsInputsW354Shape
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      descended

/-- Source cocone field for W354. -/
def TransportedConcreteQuotientW354Inputs.source
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (_h : TransportedConcreteQuotientW354Inputs X Y α cx cy) : Cocone X :=
  wppOpTransportedConcreteQuotientCocone X

/-- Target cocone field for W354. -/
def TransportedConcreteQuotientW354Inputs.target
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (_h : TransportedConcreteQuotientW354Inputs X Y α cx cy) : Cocone Y :=
  wppOpTransportedConcreteQuotientCocone Y

/-- Source colimit proof field for W354. -/
def TransportedConcreteQuotientW354Inputs.hsource
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (_h : TransportedConcreteQuotientW354Inputs X Y α cx cy) :
    IsColimit (wppOpTransportedConcreteQuotientCocone X) :=
  wppOpTransportedConcreteQuotientCoconeIsColimit X

/-- Target colimit proof field for W354. -/
def TransportedConcreteQuotientW354Inputs.htarget
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (_h : TransportedConcreteQuotientW354Inputs X Y α cx cy) :
    IsColimit (wppOpTransportedConcreteQuotientCocone Y) :=
  wppOpTransportedConcreteQuotientCoconeIsColimit Y

/-- Projection lemma exposing the W354 descended leg equation. -/
theorem TransportedConcreteQuotientW354Inputs.descended_leg_app
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (h : TransportedConcreteQuotientW354Inputs X Y α cx cy)
    (j : WalkingParallelPairᵒᵖ) :
    (wppOpTransportedConcreteQuotientCocone X).ι.app j ≫ h.descended =
      α.app j ≫ (wppOpTransportedConcreteQuotientCocone Y).ι.app j :=
  h.descended_leg j

/-- W362 relation fields package the descended map as a closed embedding. -/
theorem RelationPullbackDescendedFieldsInputsW354Shape.closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : RelationPullbackDescendedFieldsInputsW354Shape source target descended) :
    IsClosedEmbedding (descended : source.pt → target.pt) :=
  WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
    (descended : source.pt → target.pt) h.injective h.inducing h.closed_range

/-- The canonical `IsColimit.map` is uniquely determined by cocone compatibility. -/
theorem isColimit_map_eq_of_compat_w362
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx)
    (hcompat : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/-- Transported descended legs identify the descended map with `IsColimit.map`. -/
theorem sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w362
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hsource : IsColimit source) (hcx : IsColimit cx)
    (htarget : IsColimit target) (hcy : IsColimit cy)
    (descended : source.pt ⟶ target.pt)
    (hdescended : ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j) :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫
        IsColimit.map hcx cy α =
      descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom := by
  apply hsource.hom_ext
  intro j
  have hsourceLeg :
      source.ι.app j ≫ (IsColimit.coconePointUniqueUpToIso hsource hcx).hom =
        cx.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hsource hcx j
  have htargetLeg :
      target.ι.app j ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
        cy.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom htarget hcy j
  have hleft :
      source.ι.app j ≫
          ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫
            IsColimit.map hcx cy α) =
        α.app j ≫ cy.ι.app j := by
    have hsourceComp :
        source.ι.app j ≫
            ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫
              IsColimit.map hcx cy α) =
          cx.ι.app j ≫ IsColimit.map hcx cy α := by
      simpa [Category.assoc] using
        congrArg (fun f => f ≫ IsColimit.map hcx cy α) hsourceLeg
    exact hsourceComp.trans (IsColimit.ι_map hcx cy α j)
  have hright :
      source.ι.app j ≫
          (descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom) =
        α.app j ≫ cy.ι.app j := by
    have hdescComp :
        (source.ι.app j ≫ descended) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
          (α.app j ≫ target.ι.app j) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom :=
      congrArg
        (fun f => f ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom)
        (hdescended j)
    have htargetComp :
        (α.app j ≫ target.ι.app j) ≫
            (IsColimit.coconePointUniqueUpToIso htarget hcy).hom =
          α.app j ≫ cy.ι.app j := by
      simpa [Category.assoc] using congrArg (fun f => α.app j ≫ f) htargetLeg
    simpa [Category.assoc] using hdescComp.trans htargetComp
  exact hleft.trans hright.symm

/-- Pointwise formula for the transported `IsColimit.map`. -/
theorem pointwise_isColimitMap_eq_descended_w362
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hcx : IsColimit cx)
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (descended : source.pt ⟶ target.pt)
    (hEq :
      sourceIso.hom ≫ IsColimit.map hcx cy α = descended ≫ targetIso.hom) :
    ∀ x : cx.pt,
      IsColimit.map hcx cy α x = targetIso.hom (descended (sourceIso.inv x)) := by
  intro x
  have hAt :
      (sourceIso.hom ≫ IsColimit.map hcx cy α) (sourceIso.inv x) =
        (descended ≫ targetIso.hom) (sourceIso.inv x) := by
    exact congrArg (fun f : source.pt ⟶ cy.pt => f (sourceIso.inv x)) hEq
  have hsource :
      sourceIso.hom (sourceIso.inv x) = x := by
    exact congrArg (fun f : cx.pt ⟶ cx.pt => f x) sourceIso.inv_hom_id
  simpa [MetrizableLCA.comp_apply, hsource] using hAt

/-- W362 descended fields transport to closed-embedding fields for `IsColimit.map`. -/
theorem isColimitMap_closedEmbedding_of_w362
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (h : TransportedConcreteQuotientW354Inputs X Y α cx cy) :
    IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt) := by
  let source := wppOpTransportedConcreteQuotientCocone X
  let target := wppOpTransportedConcreteQuotientCocone Y
  let hsource := wppOpTransportedConcreteQuotientCoconeIsColimit X
  let htarget := wppOpTransportedConcreteQuotientCoconeIsColimit Y
  let sourceIso := IsColimit.coconePointUniqueUpToIso hsource hcx
  let targetIso := IsColimit.coconePointUniqueUpToIso htarget hcy
  let sourceHomeomorph : cx.pt ≃ₜ+ source.pt :=
    MetrizableLCA.isoToContinuousAddEquiv sourceIso.symm
  let targetHomeomorph : target.pt ≃ₜ+ cy.pt :=
    MetrizableLCA.isoToContinuousAddEquiv targetIso
  have hcomp :
      IsClosedEmbedding
        (fun x : cx.pt => targetHomeomorph (h.descended (sourceHomeomorph x))) :=
    targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
      ((h.relation_inputs.closedEmbedding).comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
  have hEq :
      sourceIso.hom ≫ IsColimit.map hcx cy α =
        h.descended ≫ targetIso.hom :=
    sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w362
      α hsource hcx htarget hcy h.descended h.descended_leg
  have hfun :
      (fun x : cx.pt => targetHomeomorph (h.descended (sourceHomeomorph x))) =
        (IsColimit.map hcx cy α : cx.pt → cy.pt) := by
    funext x
    exact (pointwise_isColimitMap_eq_descended_w362
      hcx sourceIso targetIso h.descended hEq x).symm
  simpa [hfun] using hcomp

/-- W362 inputs provide the W318 left-LCA field tuple for the canonical colimit map. -/
theorem w318_fields_for_isColimitMap_of_w362
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (h : TransportedConcreteQuotientW354Inputs X Y α cx cy) :
    Function.Injective (IsColimit.map hcx cy α : cx.pt → cy.pt) ∧
      IsInducing (IsColimit.map hcx cy α : cx.pt → cy.pt) ∧
        IsClosed (Set.range (IsColimit.map hcx cy α : cx.pt → cy.pt)) := by
  have hclosed : IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt) :=
    isColimitMap_closedEmbedding_of_w362 hcx hcy h
  exact ⟨hclosed.injective, hclosed.isInducing, hclosed.isClosed_range⟩

/--
If every WPP-op colimit map has a W362 transported quotient input, the W318
left-LCA boundary is closed.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w362
    (hcert :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                TransportedConcreteQuotientW354Inputs X Y α cx cy) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let h := hcert X Y α cx cy hcx hcy hclosed
  have hfields := w318_fields_for_isColimitMap_of_w362 hcx hcy h
  have hmapEq : IsColimit.map hcx cy α = φ :=
    isColimit_map_eq_of_compat_w362 α φ hcx hcompat
  have hinj : Function.Injective (φ : cx.pt → cy.pt) := by
    rw [← hmapEq]
    exact hfields.1
  have hind : IsInducing (φ : cx.pt → cy.pt) := by
    rw [← hmapEq]
    exact hfields.2.1
  have hclosedRange : IsClosed (Set.range (φ : cx.pt → cy.pt)) := by
    rw [← hmapEq]
    exact hfields.2.2
  exact ⟨hinj, hind, hclosedRange⟩

/-- Declaration names exported by this support file. -/
def w362SupportDeclarationNames : List String :=
  ["wppOpWhiskeredDiagramIso",
    "wppOpTransportedConcreteQuotientCocone",
    "wppOpTransportedConcreteQuotientCoconeIsColimit",
    "wppOpTransportedConcreteQuotientCocone_pt",
    "wppOpTransportedConcreteQuotientCocone_ι_app",
    "RelationPullbackDescendedFieldsInputsW354Shape",
    "TransportedConcreteQuotientW354Inputs",
    "TransportedConcreteQuotientW354Inputs.source",
    "TransportedConcreteQuotientW354Inputs.target",
    "TransportedConcreteQuotientW354Inputs.hsource",
    "TransportedConcreteQuotientW354Inputs.htarget",
    "TransportedConcreteQuotientW354Inputs.descended_leg_app"]

theorem w362SupportDeclarationNames_count :
    w362SupportDeclarationNames.length = 12 := rfl

/-- Machine-readable state for this checked W362 support file. -/
structure WppOpLeftLcaCoconeTransportV369StateW362 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaCoconeTransportV369StateW362 :
    WppOpLeftLcaCoconeTransportV369StateW362 where
  seed := "2d05508a178eee2dace9d33cafc630b9"
  checkedFacts :=
    ["counit diagram isomorphism identifies the W357 whiskered diagram with the original WPP-op diagram",
      "the W357 whiskered concrete quotient cocone is transported to an actual Cocone X",
      "the transported cocone carries an IsColimit proof",
      "W354-ready source, target, hsource, htarget, descended map, relation fields, and descended leg equation projections are packaged"]
  remainingInputs :=
    ["instantiate the concrete descended map between transported source and target quotient cocones",
      "prove the transported descended leg equations from the ordinary quotient projection equations",
      "supply the relation-pullback closed-map fields for the transported descended map"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaCoconeTransportV369StateW362_productSuccess :
    currentWppOpLeftLcaCoconeTransportV369StateW362.productSuccessClaimed = false := rfl

section Checks

#check wppOpOrdinaryDiagram
#check wppOpConcreteQuotientCoconeOnOrdinary
#check wppOpConcreteQuotientCoconeOnOrdinaryIsColimit
#check wppOpWhiskeredConcreteQuotientCocone
#check wppOpWhiskeredConcreteQuotientCoconeIsColimit
#check wppOpWhiskeredDiagramIso
#check wppOpTransportedConcreteQuotientCocone
#check wppOpTransportedConcreteQuotientCoconeIsColimit
#check wppOpTransportedConcreteQuotientCocone_pt
#check wppOpTransportedConcreteQuotientCocone_ι_app
#check RelationPullbackDescendedFieldsInputsW354Shape
#check TransportedConcreteQuotientW354Inputs
#check TransportedConcreteQuotientW354Inputs.source
#check TransportedConcreteQuotientW354Inputs.target
#check TransportedConcreteQuotientW354Inputs.hsource
#check TransportedConcreteQuotientW354Inputs.htarget
#check TransportedConcreteQuotientW354Inputs.descended_leg_app
#check w362SupportDeclarationNames
#check w362SupportDeclarationNames_count
#check currentWppOpLeftLcaCoconeTransportV369StateW362
#check currentWppOpLeftLcaCoconeTransportV369StateW362_productSuccess

end Checks

end WppOpLeftLcaCoconeTransportV369SupportW362

end LeanLCAExactChallenge
