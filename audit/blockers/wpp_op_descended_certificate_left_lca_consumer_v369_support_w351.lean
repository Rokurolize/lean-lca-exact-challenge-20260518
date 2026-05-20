import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W351: descended certificate consumer for the W318 left LCA boundary.

This standalone support file copies the checked W348 certificate interface and
packages it at the exact W318
`wppOp_lca_colimitMap_injective_inducing_closedImage` boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpDescendedCertificateLeftLcaConsumerV369SupportW351

/-- The topological fields supplied by the concrete descended quotient map. -/
structure DescendedClosedMapFields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- Package the descended fields as a closed embedding. -/
theorem DescendedClosedMapFields.closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : DescendedClosedMapFields source target descended) :
    IsClosedEmbedding (descended : source.pt → target.pt) :=
  WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
    (descended : source.pt → target.pt) h.injective h.inducing h.closed_range

/-- The canonical `IsColimit.map` is the unique map compatible with the cocone legs. -/
theorem isColimit_map_eq_of_compat
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx)
    (hcompat : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/--
If the concrete quotient-presenting cocones have compatible descended legs,
then the transported descended map agrees with the canonical `IsColimit.map`.
-/
theorem sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom
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
The categorical transport equation implies the pointwise formula used to move
closed-embedding fields from the descended quotient map to `IsColimit.map`.
-/
theorem pointwise_isColimitMap_eq_descended
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
theorem isColimitMap_closedEmbedding_of_descended_fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    {source : Cocone X} {target : Cocone Y}
    (hcx : IsColimit cx)
    (sourceIso : source.pt ≅ cx.pt) (targetIso : target.pt ≅ cy.pt)
    (descended : source.pt ⟶ target.pt)
    (hdescended : DescendedClosedMapFields source target descended)
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
    exact (pointwise_isColimitMap_eq_descended
      hcx sourceIso targetIso descended hEq x).symm
  simpa [hfun] using hcomp

/--
Certificate for the quotient-presenting route.  The final equality field is
the checked identification of `IsColimit.map` with the transported descended
quotient map.
-/
structure DescendedQuotientIsColimitMapCertificate
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
  descended_fields : DescendedClosedMapFields source target descended
  transported_isColimitMap_eq :
    (IsColimit.coconePointUniqueUpToIso hsource hcx).hom ≫
        IsColimit.map hcx cy α =
      descended ≫ (IsColimit.coconePointUniqueUpToIso htarget hcy).hom

/-- Build the certificate once the quotient-presenting cocones and leg equations exist. -/
def mkDescendedQuotientIsColimitMapCertificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    (source : Cocone X) (target : Cocone Y)
    (hsource : IsColimit source) (htarget : IsColimit target)
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (descended : source.pt ⟶ target.pt)
    (hdescended_leg : ∀ j : WalkingParallelPairᵒᵖ,
      source.ι.app j ≫ descended = α.app j ≫ target.ι.app j)
    (hdescended_fields : DescendedClosedMapFields source target descended) :
    DescendedQuotientIsColimitMapCertificate X Y α cx cy where
  source := source
  target := target
  hsource := hsource
  htarget := htarget
  hcx := hcx
  hcy := hcy
  descended := descended
  descended_leg := hdescended_leg
  descended_fields := hdescended_fields
  transported_isColimitMap_eq :=
    sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom
      α hsource hcx htarget hcy descended hdescended_leg

/-- The certificate consumes descended closed-map fields to close the `IsColimit.map` boundary. -/
theorem isColimitMap_closedEmbedding_of_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (cert : DescendedQuotientIsColimitMapCertificate X Y α cx cy) :
    IsClosedEmbedding (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) :=
  isColimitMap_closedEmbedding_of_descended_fields
    cert.hcx
    (IsColimit.coconePointUniqueUpToIso cert.hsource cert.hcx)
    (IsColimit.coconePointUniqueUpToIso cert.htarget cert.hcy)
    cert.descended cert.descended_fields cert.transported_isColimitMap_eq

/-- Closed-embedding fields for the canonical `IsColimit.map`. -/
theorem isColimitMap_fields_of_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (cert : DescendedQuotientIsColimitMapCertificate X Y α cx cy) :
    Function.Injective (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
      IsInducing (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
        IsClosed (Set.range (IsColimit.map cert.hcx cy α : cx.pt → cy.pt)) := by
  have hclosed : IsClosedEmbedding (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) :=
    isColimitMap_closedEmbedding_of_certificate cert
  exact ⟨hclosed.injective, hclosed.isInducing, hclosed.isClosed_range⟩

/-- A single descended quotient certificate gives the three W318 fields for `IsColimit.map`. -/
theorem w318_fields_for_isColimitMap_of_single_certificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (cert : DescendedQuotientIsColimitMapCertificate X Y α cx cy) :
    Function.Injective (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
      IsInducing (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) ∧
        IsClosed (Set.range (IsColimit.map cert.hcx cy α : cx.pt → cy.pt)) :=
  isColimitMap_fields_of_certificate cert

/--
Supplying a descended quotient certificate for each WPP-op colimit-map problem
closes W318's left LCA injective/inducing/closed-image boundary.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_descended_certificates
    (hcert :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                DescendedQuotientIsColimitMapCertificate X Y α cx cy) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let cert := hcert X Y α cx cy hcx hcy hclosed
  have hfields := w318_fields_for_isColimitMap_of_single_certificate cert
  have hmapEq : IsColimit.map cert.hcx cy α = φ :=
    isColimit_map_eq_of_compat α φ cert.hcx hcompat
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
def w351SupportDeclarationNames : List String :=
  ["DescendedClosedMapFields",
    "DescendedClosedMapFields.closedEmbedding",
    "isColimit_map_eq_of_compat",
    "sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom",
    "pointwise_isColimitMap_eq_descended",
    "isColimitMap_closedEmbedding_of_descended_fields",
    "DescendedQuotientIsColimitMapCertificate",
    "mkDescendedQuotientIsColimitMapCertificate",
    "isColimitMap_closedEmbedding_of_certificate",
    "isColimitMap_fields_of_certificate",
    "w318_fields_for_isColimitMap_of_single_certificate",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_descended_certificates"]

theorem w351SupportDeclarationNames_count :
    w351SupportDeclarationNames.length = 12 := rfl

/-- Machine-readable state for this checked W351 support file. -/
structure WppOpDescendedCertificateLeftLcaConsumerV369State : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpDescendedCertificateLeftLcaConsumerV369State :
    WppOpDescendedCertificateLeftLcaConsumerV369State where
  seed := "099a4f4b823a879f07ce9ad60bc5af2e"
  checkedFacts :=
    ["single descended quotient certificate yields the W318 three fields for IsColimit.map",
      "a provider of certificates for all WPP-op colimit-map problems yields W318 left LCA boundary"]
  remainingInputs :=
    ["instantiate source and target as the concrete quotient-presenting cocones",
      "prove those concrete cocones are colimits",
      "prove the descended quotient map satisfies the WPP-op leg equations",
      "derive descended closed-map fields from concrete quotient relation inputs"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpDescendedCertificateLeftLcaConsumerV369State_productSuccess :
    currentWppOpDescendedCertificateLeftLcaConsumerV369State.productSuccessClaimed = false := rfl

section Checks

#check DescendedClosedMapFields
#check DescendedClosedMapFields.closedEmbedding
#check isColimit_map_eq_of_compat
#check sourceIso_hom_comp_isColimitMap_eq_descended_comp_targetIso_hom
#check pointwise_isColimitMap_eq_descended
#check isColimitMap_closedEmbedding_of_descended_fields
#check DescendedQuotientIsColimitMapCertificate
#check mkDescendedQuotientIsColimitMapCertificate
#check isColimitMap_closedEmbedding_of_certificate
#check isColimitMap_fields_of_certificate
#check w318_fields_for_isColimitMap_of_single_certificate
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_descended_certificates
#check w351SupportDeclarationNames
#check w351SupportDeclarationNames_count
#check currentWppOpDescendedCertificateLeftLcaConsumerV369State
#check currentWppOpDescendedCertificateLeftLcaConsumerV369State_productSuccess

end Checks

end WppOpDescendedCertificateLeftLcaConsumerV369SupportW351

end LeanLCAExactChallenge
