import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W354: left-LCA relation/certificate composer boundary.

This standalone audit file composes the W351 descended-certificate consumer with
a W352-style relation-pullback field provider at the typed boundary needed by
W318.  The concrete quotient-object construction remains an external input:
this file checks that once relation-pullback data supplies the descended
closed-map fields on the quotient-presenting cocones, the W351 certificate and
the W318 left-LCA boundary follow.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaRelationCertificateComposerV369SupportW354

/-- The topological fields supplied by a descended quotient map. -/
structure DescendedClosedMapFieldsW354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- Package the descended fields as a closed embedding. -/
theorem DescendedClosedMapFieldsW354.closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : DescendedClosedMapFieldsW354 source target descended) :
    IsClosedEmbedding (descended : source.pt → target.pt) :=
  WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
    (descended : source.pt → target.pt) h.injective h.inducing h.closed_range

/--
W352-style local relation-pullback input at the W351 typed boundary.

The concrete W352 file proves these three fields from square equations,
relation-pullback equality, quotient compatibility, and closedness of the
descended quotient map.  W354 keeps the same downstream shape while avoiding a
false identification between local quotient objects and arbitrary cocone points.
-/
structure RelationPullbackDescendedFieldsInputsW352Style
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- The W352-style relation input supplies exactly the W351 descended fields. -/
theorem RelationPullbackDescendedFieldsInputsW352Style.descended_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : RelationPullbackDescendedFieldsInputsW352Style source target descended) :
    DescendedClosedMapFieldsW354 source target descended :=
  ⟨h.injective, h.inducing, h.closed_range⟩

/-- The canonical `IsColimit.map` is the unique map compatible with the cocone legs. -/
theorem isColimit_map_eq_of_compat_w354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx)
    (hcompat : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/--
If the quotient-presenting cocones have compatible descended legs, then the
transported descended map agrees with the canonical `IsColimit.map`.
-/
theorem sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w354
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

/--
Pointwise transport formula used to move closed-embedding fields from the
descended quotient map to `IsColimit.map`.
-/
theorem pointwise_isColimitMap_eq_descended_w354
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

/-- Transport a closed embedding through source and target colimit-point isomorphisms. -/
theorem isColimitMap_closedEmbedding_of_descended_fields_w354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hcx : IsColimit cx)
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (descended : source.pt ⟶ target.pt)
    (hdescended : DescendedClosedMapFieldsW354 source target descended)
    (hEq :
      sourceIso.hom ≫ IsColimit.map hcx cy α = descended ≫ targetIso.hom) :
    IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt) := by
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
        (IsColimit.map hcx cy α : cx.pt → cy.pt) := by
    funext x
    exact (pointwise_isColimitMap_eq_descended_w354
      hcx sourceIso targetIso descended hEq x).symm
  simpa [hfun] using hcomp

/-- W351-style certificate for the quotient-presenting route. -/
structure DescendedQuotientIsColimitMapCertificateW354
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 2 where
  source : Cocone X
  target : Cocone Y
  hsource : IsColimit source
  htarget : IsColimit target
  hcx : IsColimit cx
  hcy : IsColimit cy
  descended : source.pt ⟶ target.pt
  descended_leg :
    ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j
  descended_fields : DescendedClosedMapFieldsW354 source target descended
  transported_isColimitMap_eq :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫
        IsColimit.map hcx cy α =
      descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom

/--
W354 composer input: quotient-presenting cocones, colimit proofs, descended
map, leg equations, and the W352-style relation-pullback descended fields.
-/
structure LeftLcaRelationCertificateInputsW354
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 2 where
  source : Cocone X
  target : Cocone Y
  hsource : IsColimit source
  htarget : IsColimit target
  hcx : IsColimit cx
  hcy : IsColimit cy
  descended : source.pt ⟶ target.pt
  descended_leg :
    ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j
  relation_inputs :
    RelationPullbackDescendedFieldsInputsW352Style source target descended

/-- Build the W351-style certificate from the W354 relation/certificate bundle. -/
def LeftLcaRelationCertificateInputsW354.toCertificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (h : LeftLcaRelationCertificateInputsW354 X Y α cx cy) :
    DescendedQuotientIsColimitMapCertificateW354 X Y α cx cy where
  source := h.source
  target := h.target
  hsource := h.hsource
  htarget := h.htarget
  hcx := h.hcx
  hcy := h.hcy
  descended := h.descended
  descended_leg := h.descended_leg
  descended_fields := h.relation_inputs.descended_fields
  transported_isColimitMap_eq :=
    sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w354
      α h.hsource h.hcx h.htarget h.hcy h.descended h.descended_leg

/-- The certificate consumes descended closed-map fields to close `IsColimit.map`. -/
theorem isColimitMap_closedEmbedding_of_certificate_w354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (cert : DescendedQuotientIsColimitMapCertificateW354 X Y α cx cy) :
    IsClosedEmbedding (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) :=
  isColimitMap_closedEmbedding_of_descended_fields_w354
    cert.hcx
    (IsColimit.coconePointUniqueUpToIso cert.hsource cert.hcx)
    (IsColimit.coconePointUniqueUpToIso cert.htarget cert.hcy)
    cert.descended cert.descended_fields cert.transported_isColimitMap_eq

/-- Closed-embedding fields for the canonical `IsColimit.map`. -/
theorem isColimitMap_fields_of_certificate_w354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (cert : DescendedQuotientIsColimitMapCertificateW354 X Y α cx cy) :
    Function.Injective (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
      IsInducing (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
        IsClosed (Set.range (IsColimit.map cert.hcx cy α : cx.pt → cy.pt)) := by
  have hclosed : IsClosedEmbedding (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) :=
    isColimitMap_closedEmbedding_of_certificate_w354 cert
  exact ⟨hclosed.injective, hclosed.isInducing, hclosed.isClosed_range⟩

/-- The W354 bundle gives the three W318 fields for `IsColimit.map`. -/
theorem w318_fields_for_isColimitMap_of_relation_certificate_inputs_w354
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (h : LeftLcaRelationCertificateInputsW354 X Y α cx cy) :
    Function.Injective (IsColimit.map h.hcx cy α : cx.pt → cy.pt) ∧
      IsInducing (IsColimit.map h.hcx cy α : cx.pt → cy.pt) ∧
        IsClosed (Set.range (IsColimit.map h.hcx cy α : cx.pt → cy.pt)) :=
  isColimitMap_fields_of_certificate_w354 h.toCertificate

/--
Supplying W354 relation/certificate bundles for every WPP-op colimit-map
problem closes W318's left-LCA injective/inducing/closed-image boundary.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_relation_certificates_w354
    (hcert :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                LeftLcaRelationCertificateInputsW354 X Y α cx cy) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let h := hcert X Y α cx cy hcx hcy hclosed
  have hfields := w318_fields_for_isColimitMap_of_relation_certificate_inputs_w354 h
  have hmapEq : IsColimit.map h.hcx cy α = φ :=
    isColimit_map_eq_of_compat_w354 α φ h.hcx hcompat
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
def w354SupportDeclarationNames : List String :=
  ["DescendedClosedMapFieldsW354",
    "DescendedClosedMapFieldsW354.closedEmbedding",
    "RelationPullbackDescendedFieldsInputsW352Style",
    "RelationPullbackDescendedFieldsInputsW352Style.descended_fields",
    "isColimit_map_eq_of_compat_w354",
    "sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w354",
    "pointwise_isColimitMap_eq_descended_w354",
    "isColimitMap_closedEmbedding_of_descended_fields_w354",
    "DescendedQuotientIsColimitMapCertificateW354",
    "LeftLcaRelationCertificateInputsW354",
    "LeftLcaRelationCertificateInputsW354.toCertificate",
    "isColimitMap_closedEmbedding_of_certificate_w354",
    "isColimitMap_fields_of_certificate_w354",
    "w318_fields_for_isColimitMap_of_relation_certificate_inputs_w354",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_relation_certificates_w354"]

theorem w354SupportDeclarationNames_count :
    w354SupportDeclarationNames.length = 15 := rfl

/-- Machine-readable state for this checked W354 support file. -/
structure WppOpLeftLcaRelationCertificateComposerV369StateW354 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaRelationCertificateComposerV369StateW354 :
    WppOpLeftLcaRelationCertificateComposerV369StateW354 where
  seed := "86d07543b36ca91f1d0360ef8e1d6ee3"
  checkedFacts :=
    ["W352-style relation-pullback descended fields supply W351 descended closed-map fields",
      "a W354 relation/certificate bundle builds a W351-style descended quotient IsColimit.map certificate",
      "a family of W354 relation/certificate bundles proves W318.wppOp_lca_colimitMap_injective_inducing_closedImage"]
  remainingInputs :=
    ["instantiate source and target as the concrete quotient-presenting cocones",
      "connect the concrete W352 quotient-object package to the cocone-point typed RelationPullbackDescendedFieldsInputsW352Style",
      "prove the concrete descended map leg equations for the WPP-op cocones"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaRelationCertificateComposerV369StateW354_productSuccess :
    currentWppOpLeftLcaRelationCertificateComposerV369StateW354.productSuccessClaimed = false := rfl

section Checks

#check DescendedClosedMapFieldsW354
#check DescendedClosedMapFieldsW354.closedEmbedding
#check RelationPullbackDescendedFieldsInputsW352Style
#check RelationPullbackDescendedFieldsInputsW352Style.descended_fields
#check isColimit_map_eq_of_compat_w354
#check sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom_w354
#check pointwise_isColimitMap_eq_descended_w354
#check isColimitMap_closedEmbedding_of_descended_fields_w354
#check DescendedQuotientIsColimitMapCertificateW354
#check LeftLcaRelationCertificateInputsW354
#check LeftLcaRelationCertificateInputsW354.toCertificate
#check isColimitMap_closedEmbedding_of_certificate_w354
#check isColimitMap_fields_of_certificate_w354
#check w318_fields_for_isColimitMap_of_relation_certificate_inputs_w354
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_relation_certificates_w354
#check w354SupportDeclarationNames
#check w354SupportDeclarationNames_count
#check currentWppOpLeftLcaRelationCertificateComposerV369StateW354
#check currentWppOpLeftLcaRelationCertificateComposerV369StateW354_productSuccess

end Checks

end WppOpLeftLcaRelationCertificateComposerV369SupportW354

end LeanLCAExactChallenge
