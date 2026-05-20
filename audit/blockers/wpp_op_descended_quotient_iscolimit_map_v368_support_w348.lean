import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W348: descended quotient map identification with `IsColimit.map`.

This standalone support file bridges the W339/W342 transported descended-map
route to the canonical categorical map `IsColimit.map hcx cy α`.  It does not
construct the concrete quotient/coequalizer cocones; it records those as the
remaining inputs needed by the larger left LCA frontier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpDescendedQuotientIsColimitMapV368SupportW348

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

/--
The canonical `IsColimit.map` is the unique map compatible with the cocone
legs.  This is the W365 equation specialized for direct reuse below.
-/
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

/--
Global certificate boundary for the left LCA route: for every componentwise
closed-embedding natural transformation, a quotient-presenting descended map
certificate exists.
-/
abbrev wppOp_lca_descendedQuotientCertificate_boundary : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            Nonempty (DescendedQuotientIsColimitMapCertificate X Y α cx cy)

/--
The global descended-quotient certificate boundary is enough to prove W318's
left LCA injective/inducing/closed-image certificate for arbitrary compatible
colimit maps.
-/
theorem wppOp_lca_colimitMap_fields_of_descendedQuotientCertificate_boundary
    (hboundary : wppOp_lca_descendedQuotientCertificate_boundary) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  rcases hboundary X Y α cx cy hcx hcy hclosed with ⟨cert⟩
  rcases isColimitMap_fields_of_certificate cert with
    ⟨hinj, hind, hclosedImage⟩
  have hmapClosed :
      IsClosedEmbedding (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) :=
    WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
      (IsColimit.map cert.hcx cy α : cx.pt → cy.pt) hinj hind hclosedImage
  have hmapEq : IsColimit.map cert.hcx cy α = φ :=
    isColimit_map_eq_of_compat α φ cert.hcx hcompat
  have hφ : IsClosedEmbedding (φ : cx.pt → cy.pt) := by
    change IsClosedEmbedding (MetrizableLCA.Hom.hom φ)
    rw [← hmapEq]
    simpa using hmapClosed
  exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/-- Current checked declaration names for external review scripts. -/
def w348SupportDeclarationNames : List String :=
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
    "wppOp_lca_descendedQuotientCertificate_boundary",
    "wppOp_lca_colimitMap_fields_of_descendedQuotientCertificate_boundary"]

theorem w348SupportDeclarationNames_count :
    w348SupportDeclarationNames.length = 12 := rfl

/-- Machine-readable state for this checked support file. -/
structure WppOpDescendedQuotientIsColimitMapV368State : Type where
  seed : String
  selectedRoute : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpDescendedQuotientIsColimitMapV368State :
    WppOpDescendedQuotientIsColimitMapV368State where
  seed := "23218a68433d531192364e5ff1996aee"
  selectedRoute := "descended-quotient-iscolimit-map-v368"
  checkedFacts :=
    ["transported descended quotient map equals IsColimit.map",
      "certificate bundles quotient cocones, colimit proofs, descended map, leg equation, fields, and equality",
      "certificate yields IsClosedEmbedding and W318-style fields for IsColimit.map",
      "a global certificate boundary yields the W318 left LCA injective/inducing/closed-image certificate"]
  remainingInputs :=
    ["instantiate source and target as the concrete quotient/coequalizer WPP-op cocones",
      "prove those concrete cocones are colimits",
      "prove the descended quotient map satisfies the WPP-op leg equations",
      "derive descended closed-map fields from concrete relation-preimage and quotient-compatibility inputs"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpDescendedQuotientIsColimitMapV368State_productSuccess :
    currentWppOpDescendedQuotientIsColimitMapV368State.productSuccessClaimed = false := rfl

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
#check wppOp_lca_descendedQuotientCertificate_boundary
#check wppOp_lca_colimitMap_fields_of_descendedQuotientCertificate_boundary
#check w348SupportDeclarationNames
#check w348SupportDeclarationNames_count
#check currentWppOpDescendedQuotientIsColimitMapV368State
#check currentWppOpDescendedQuotientIsColimitMapV368State_productSuccess

end Checks

end WppOpDescendedQuotientIsColimitMapV368SupportW348

end LeanLCAExactChallenge
