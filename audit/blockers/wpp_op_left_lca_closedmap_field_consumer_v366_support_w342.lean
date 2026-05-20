import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W342: checked left LCA closed-map field consumer.

This file consumes the W339 transport equation and the W340 descended-map
field boundary at the abstract WPP-op colimit level.  The remaining product
gap is the concrete construction of the quotient/coequalizer cocones and their
leg equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaClosedMapFieldConsumerV366SupportW342

/--
Local copy of the W339 transport equation, because the audit support files are
checked as standalone scripts rather than importable lake modules.
-/
theorem sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hsource : IsColimit source) (hcx : IsColimit cx)
    (htarget : IsColimit target) (hcy : IsColimit cy)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j)
    (hdescended : ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j) :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ =
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
          ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ) =
        α.app j ≫ cy.ι.app j := by
    have hsourceComp :
        source.ι.app j ≫
            ((IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫ φ) =
          cx.ι.app j ≫ φ := by
      simpa [Category.assoc] using congrArg (fun f => f ≫ φ) hsourceLeg
    exact hsourceComp.trans (hφ j)
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

/-- The three topological fields carried by the concrete descended map. -/
structure DescendedClosedMapFields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/--
Turn W340's descended-map fields into a closed embedding.  This is the local
field package needed before transporting along the W339 colimit isomorphisms.
-/
theorem DescendedClosedMapFields.closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : DescendedClosedMapFields source target descended) :
    IsClosedEmbedding (descended : source.pt → target.pt) :=
  WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
    (descended : source.pt → target.pt) h.injective h.inducing h.closed_range

/--
Transport a closed embedding through the source and target colimit-point
isomorphisms.  The pointwise equation is the function-level form of W339's
`sourceIso.hom ≫ φ = descended ≫ targetIso.hom`.
-/
theorem colimitMap_closedEmbedding_of_descended_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hdescended : DescendedClosedMapFields source target descended)
    (htransport :
      ∀ x : cx.pt, φ x = targetIso.hom (descended (sourceIso.inv x))) :
    IsClosedEmbedding (φ : cx.pt → cy.pt) := by
  let sourceHomeomorph :
      cx.pt ≃ₜ+ source.pt :=
    MetrizableLCA.isoToContinuousAddEquiv sourceIso.symm
  let targetHomeomorph :
      target.pt ≃ₜ+ cy.pt :=
    MetrizableLCA.isoToContinuousAddEquiv targetIso
  have hcomp :
      IsClosedEmbedding
        (fun x : cx.pt => targetHomeomorph (descended (sourceHomeomorph x))) :=
    targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
      ((hdescended.closedEmbedding).comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
  have hfun :
      (fun x : cx.pt => targetHomeomorph (descended (sourceHomeomorph x))) =
        (φ : cx.pt → cy.pt) := by
    funext x
    exact (htransport x).symm
  simpa [hfun]
    using hcomp

/--
The W342 consumer theorem: W340 descended fields plus the W339 transport
equation give the W318 three fields for the arbitrary colimit map `φ`.
-/
theorem colimitMap_fields_of_descended_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hdescended : DescendedClosedMapFields source target descended)
    (htransport :
      ∀ x : cx.pt, φ x = targetIso.hom (descended (sourceIso.inv x))) :
    Function.Injective (φ : cx.pt → cy.pt) ∧
      IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt)) := by
  have hclosedEmbedding :
      IsClosedEmbedding (φ : cx.pt → cy.pt) :=
    colimitMap_closedEmbedding_of_descended_fields
      sourceIso targetIso φ descended hdescended htransport
  exact ⟨hclosedEmbedding.injective, hclosedEmbedding.isInducing,
    hclosedEmbedding.isClosed_range⟩

/--
W339's categorical equation gives the pointwise transport equation used by the
field consumer.
-/
theorem pointwise_transport_of_sourceIso_hom_comp_eq
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hEq : sourceIso.hom ≫ φ = descended ≫ targetIso.hom) :
    ∀ x : cx.pt, φ x = targetIso.hom (descended (sourceIso.inv x)) := by
  intro x
  have hAt :
      (sourceIso.hom ≫ φ) (sourceIso.inv x) =
        (descended ≫ targetIso.hom) (sourceIso.inv x) := by
    exact congrArg (fun f : source.pt ⟶ cy.pt => f (sourceIso.inv x)) hEq
  have hsource :
      sourceIso.hom (sourceIso.inv x) = x := by
    exact congrArg (fun f : cx.pt ⟶ cx.pt => f x) sourceIso.inv_hom_id
  simpa [MetrizableLCA.comp_apply, hsource] using hAt

/--
Combined W339/W340 consumer, phrased directly with W339's categorical
transport equation.
-/
theorem colimitMap_fields_of_sourceIso_hom_comp_eq
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (φ : cx.pt ⟶ cy.pt) (descended : source.pt ⟶ target.pt)
    (hdescended : DescendedClosedMapFields source target descended)
    (hEq : sourceIso.hom ≫ φ = descended ≫ targetIso.hom) :
    Function.Injective (φ : cx.pt → cy.pt) ∧
      IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt)) :=
  colimitMap_fields_of_descended_fields sourceIso targetIso φ descended hdescended
    (pointwise_transport_of_sourceIso_hom_comp_eq
      sourceIso targetIso φ descended hEq)

/--
Certificate shape matching the W339/W340 route.  The fields named here are the
remaining concrete quotient/coequalizer inputs needed to instantiate the
consumer for arbitrary WPP-op colimit cocones.
-/
structure WppOpLeftLcaClosedMapTransportCertificate
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  source : Cocone X
  target : Cocone Y
  hsource : IsColimit source
  htarget : IsColimit target
  hcx : IsColimit cx
  hcy : IsColimit cy
  descended : source.pt ⟶ target.pt
  hφ : ∀ j : WalkingParallelPairᵒᵖ,
    cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j
  hdescended : ∀ j : WalkingParallelPairᵒᵖ,
    source.ι.app j ≫ descended = α.app j ≫ target.ι.app j
  descended_fields : DescendedClosedMapFields source target descended

/--
Certificate consumer: if the quotient/coequalizer cocones and descended fields
exist, W339 supplies the transport equation and W342 returns the W318 fields
for `φ`.
-/
theorem colimitMap_fields_of_transport_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (cert : WppOpLeftLcaClosedMapTransportCertificate X Y α cx cy φ) :
    Function.Injective (φ : cx.pt → cy.pt) ∧
      IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt)) := by
  let sourceIso : cert.source.pt ≅ cx.pt :=
    IsColimit.coconePointUniqueUpToIso cert.hsource cert.hcx
  let targetIso : cert.target.pt ≅ cy.pt :=
    IsColimit.coconePointUniqueUpToIso cert.htarget cert.hcy
  have hEq :
      sourceIso.hom ≫ φ = cert.descended ≫ targetIso.hom :=
    sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom
        α cert.hsource cert.hcx cert.htarget cert.hcy
        φ cert.descended cert.hφ cert.hdescended
  exact
    colimitMap_fields_of_sourceIso_hom_comp_eq
      sourceIso targetIso φ cert.descended cert.descended_fields hEq

def w342SupportDeclarationNames : List String :=
  ["DescendedClosedMapFields",
    "sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom",
    "DescendedClosedMapFields.closedEmbedding",
    "colimitMap_closedEmbedding_of_descended_fields",
    "colimitMap_fields_of_descended_fields",
    "pointwise_transport_of_sourceIso_hom_comp_eq",
    "colimitMap_fields_of_sourceIso_hom_comp_eq",
    "WppOpLeftLcaClosedMapTransportCertificate",
    "colimitMap_fields_of_transport_certificate"]

theorem w342SupportDeclarationNames_count :
    w342SupportDeclarationNames.length = 9 := rfl

/-- Machine-readable state for this checked support file. -/
structure WppOpLeftLcaClosedMapFieldConsumerState : Type where
  seed : String
  selectedRoute : String
  checkedFacts : List String
  consumedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpLeftLcaClosedMapFieldConsumerState :
    WppOpLeftLcaClosedMapFieldConsumerState where
  seed := "31841f4eaa48f5dce075657a7075ad34"
  selectedRoute := "transport-three-fields-across-cocone-isos"
  checkedFacts :=
    ["DescendedClosedMapFields.closedEmbedding",
      "sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom",
      "colimitMap_closedEmbedding_of_descended_fields",
      "colimitMap_fields_of_descended_fields",
      "pointwise_transport_of_sourceIso_hom_comp_eq",
      "colimitMap_fields_of_sourceIso_hom_comp_eq",
      "colimitMap_fields_of_transport_certificate"]
  consumedInputs :=
    ["W339 sourceIso.hom ≫ φ = descended ≫ targetIso.hom transport equation",
      "W340 descended Function.Injective field",
      "W340 descended IsInducing field",
      "W340 descended IsClosed range field"]
  remainingInputs :=
    ["instantiate source and target as the concrete quotient/coequalizer WPP-op cocones",
      "prove those concrete cocones are colimits",
      "prove the leg compatibility equations for φ and descended",
      "derive the W340 descended fields from concrete relation-preimage, quotient-compatibility, and closed-map inputs"]
  productSuccessClaimed := false

theorem currentWppOpLeftLcaClosedMapFieldConsumerState_productSuccess :
    currentWppOpLeftLcaClosedMapFieldConsumerState.productSuccessClaimed = false := rfl

section Checks

#check DescendedClosedMapFields
#check sourceIso_hom_comp_colimitMap_eq_descended_comp_targetIso_hom
#check DescendedClosedMapFields.closedEmbedding
#check colimitMap_closedEmbedding_of_descended_fields
#check colimitMap_fields_of_descended_fields
#check pointwise_transport_of_sourceIso_hom_comp_eq
#check colimitMap_fields_of_sourceIso_hom_comp_eq
#check WppOpLeftLcaClosedMapTransportCertificate
#check colimitMap_fields_of_transport_certificate
#check w342SupportDeclarationNames
#check w342SupportDeclarationNames_count
#check currentWppOpLeftLcaClosedMapFieldConsumerState
#check currentWppOpLeftLcaClosedMapFieldConsumerState_productSuccess
#check MetrizableLCA.isoToContinuousAddEquiv

end Checks

end WppOpLeftLcaClosedMapFieldConsumerV366SupportW342

end LeanLCAExactChallenge
