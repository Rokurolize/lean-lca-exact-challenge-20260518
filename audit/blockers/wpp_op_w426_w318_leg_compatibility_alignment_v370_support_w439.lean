import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W439: W426 ordinary/canonical quotient-map leg compatibility alignment.

W436 isolated the missing equality between W426's ordinary descended quotient
map and W318's canonical WPP-op colimit-point map.  This file tightens that
frontier by giving the W318 leg-compatibility equation its concrete type:

`cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j`.

The W426/W434/W436 source files in `audit/blockers` remain standalone Lean
scripts rather than importable modules, so the ordinary quotient-map side is
recorded by checked declaration-name fields plus a typed implication from the
missing ordinary/canonical equality to the W318 equation.  No product-completion
claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpW426W318LegCompatibilityAlignmentV370SupportW439

/-- The exact per-object compatibility equation consumed by W318. -/
abbrev W318ColimitMapLegCompatibility
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/--
Typed W439 bridge fields for one W318 colimit-map instance.

The string fields name the concrete W426/W436 declarations that still need to
be promoted into an importable namespace.  The proof field records the smallest
missing mathematical API: the ordinary/canonical map equality must imply W318's
per-object colimit-leg equation.
-/
structure W426OrdinaryCanonicalLegCompatibilityFields
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 1 where
  ordinaryDescendedQuotientMapName : String
  canonicalWppOpColimitMapName : String
  sourcePointIdentificationName : String
  targetPointIdentificationName : String
  ordinaryEqualsCanonicalColimitMap : Prop
  ordinaryEqualsCanonicalColimitMapName : String
  ordinaryEqualsCanonicalImpliesLegCompatibility :
    ordinaryEqualsCanonicalColimitMap → W318ColimitMapLegCompatibility X Y α cx cy φ
  colimitMap_injective : Function.Injective (φ : cx.pt → cy.pt)
  colimitMap_inducing : IsInducing (φ : cx.pt → cy.pt)
  colimitMap_range_closed : IsClosed (Set.range (φ : cx.pt → cy.pt))

/--
The missing ordinary/canonical equality is exactly enough to supply the leg
compatibility equation required by W318.
-/
theorem w318_legCompatibility_of_w426_ordinaryEqualsCanonical
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (fields : W426OrdinaryCanonicalLegCompatibilityFields X Y α cx cy φ)
    (heq : fields.ordinaryEqualsCanonicalColimitMap) :
    W318ColimitMapLegCompatibility X Y α cx cy φ :=
  fields.ordinaryEqualsCanonicalImpliesLegCompatibility heq

/--
Checked W439 bridge into W318's left LCA frontier.

After the promoted W426 ordinary/canonical alignment can build the typed fields
for every W318-compatible colimit-map instance, W318's
`wppOp_lca_colimitMap_injective_inducing_closedImage` follows immediately.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryCanonicalFields
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibility X Y α cx cy φ →
                  W426OrdinaryCanonicalLegCompatibilityFields X Y α cx cy φ) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let fields := hfields X Y α cx cy φ hcx hcy hclosed hcompat
  exact ⟨fields.colimitMap_injective, fields.colimitMap_inducing, fields.colimitMap_range_closed⟩

/--
Concrete W318 consumer spelling: the W439 bridge supplies W318's left
closed-embedding preservation boundary once the ordinary/canonical fields are
available uniformly.
-/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryCanonicalFields
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibility X Y α cx cy φ →
                  W426OrdinaryCanonicalLegCompatibilityFields X Y α cx cy φ) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding :=
  WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryCanonicalFields hfields)

/-- Concrete W426-side declarations found in the copied W426 support script. -/
def w426ConcreteOrdinaryDeclarationNamesForW439 : List String :=
  ["WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417",
    "WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMapW418",
    "WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423.ordinaryDescendedOfOrdinaryMapW417_eq_W418",
    "WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "WppOpW399InputsFromCertificatesOnlyV370SupportW426.relationPullbackDescendedFieldsInputsW399_of_w380_w389_w386",
    "WppOpW399InputsFromCertificatesOnlyV370SupportW426.remainingW399CertificatesOnlyInputsW426"]

theorem w426ConcreteOrdinaryDeclarationNamesForW439_count :
    w426ConcreteOrdinaryDeclarationNamesForW439.length = 6 := rfl

/-- W318/W436 declarations that consume the typed compatibility equation. -/
def w318CanonicalDeclarationNamesForW439 : List String :=
  ["WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage",
    "WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage",
    "WppOpW426CanonicalQuotientMapAlignmentV370SupportW436.W426OrdinaryToW318CanonicalMapAlignment.ordinaryEqualsCanonicalColimitMap",
    "W318ColimitMapLegCompatibility"]

theorem w318CanonicalDeclarationNamesForW439_count :
    w318CanonicalDeclarationNamesForW439.length = 4 := rfl

/-- The next exact theorem to port after W439. -/
def nextTheoremToPortW439 : String :=
  "ordinaryEqualsCanonicalColimitMap: after the W387/W390 point identifications, W426's ordinaryDescendedOfOrdinaryMapW417/W418 equals the canonical W318-compatible WPP-op colimit-point map, hence cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j for every WalkingParallelPairᵒᵖ object j"

/-- Remaining non-imported inputs exposed by the checked W439 bridge. -/
def missingAlignmentInputsW439 : List String :=
  ["promote W426's ordinaryDescendedOfOrdinaryMapW417/W418 and quotient-compat declarations from the standalone audit script to an importable module",
    "promote or construct the W318 canonical WPP-op colimit-point map in the same namespace as the ordinary descended quotient map",
    "prove ordinaryEqualsCanonicalColimitMap after the W387/W390 source and target point identifications",
    "derive W318ColimitMapLegCompatibility from that equality for every WalkingParallelPairᵒᵖ object",
    "transport the W426 descended quotient map injective/inducing/closed-image facts to the categorical colimit map φ"]

theorem missingAlignmentInputsW439_count :
    missingAlignmentInputsW439.length = 5 := rfl

def w439SupportDeclarationNames : List String :=
  ["W318ColimitMapLegCompatibility",
    "W426OrdinaryCanonicalLegCompatibilityFields",
    "w318_legCompatibility_of_w426_ordinaryEqualsCanonical",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryCanonicalFields",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryCanonicalFields",
    "w426ConcreteOrdinaryDeclarationNamesForW439",
    "w318CanonicalDeclarationNamesForW439",
    "nextTheoremToPortW439",
    "missingAlignmentInputsW439"]

theorem w439SupportDeclarationNames_count :
    w439SupportDeclarationNames.length = 9 := rfl

structure WppOpW426W318LegCompatibilityAlignmentV370StateW439 : Type where
  seed : String
  declarations : List String
  w426ConcreteOrdinaryDeclarations : List String
  w318CanonicalDeclarations : List String
  missingAlignmentInputs : List String
  nextTheoremToPort : String
  alignmentResult : String
  exactAlignmentProved : Bool
  productSuccessClaimed : Bool

def currentWppOpW426W318LegCompatibilityAlignmentV370StateW439 :
    WppOpW426W318LegCompatibilityAlignmentV370StateW439 where
  seed := "697d89b060bbf669cb10556ed2fe8982"
  declarations := w439SupportDeclarationNames
  w426ConcreteOrdinaryDeclarations := w426ConcreteOrdinaryDeclarationNamesForW439
  w318CanonicalDeclarations := w318CanonicalDeclarationNamesForW439
  missingAlignmentInputs := missingAlignmentInputsW439
  nextTheoremToPort := nextTheoremToPortW439
  alignmentResult :=
    "partial: checked typed W318 leg-compatibility bridge from the W436 ordinary/canonical equality frontier; exact equality remains blocked until W426 ordinary quotient maps and W318 canonical colimit maps are importable together"
  exactAlignmentProved := false
  productSuccessClaimed := false

theorem currentWppOpW426W318LegCompatibilityAlignmentV370StateW439_productSuccess :
    currentWppOpW426W318LegCompatibilityAlignmentV370StateW439.productSuccessClaimed = false := rfl

section Checks

#check W318ColimitMapLegCompatibility
#check W426OrdinaryCanonicalLegCompatibilityFields
#check w318_legCompatibility_of_w426_ordinaryEqualsCanonical
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryCanonicalFields
#check wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryCanonicalFields
#check w426ConcreteOrdinaryDeclarationNamesForW439
#check w318CanonicalDeclarationNamesForW439
#check missingAlignmentInputsW439
#check nextTheoremToPortW439
#check w439SupportDeclarationNames
#check currentWppOpW426W318LegCompatibilityAlignmentV370StateW439
#check currentWppOpW426W318LegCompatibilityAlignmentV370StateW439_productSuccess
#check WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage

end Checks

end WppOpW426W318LegCompatibilityAlignmentV370SupportW439

end LeanLCAExactChallenge
