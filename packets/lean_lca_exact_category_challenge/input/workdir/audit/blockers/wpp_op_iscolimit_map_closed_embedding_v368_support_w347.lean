import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W347: canonical `IsColimit.map` closed-embedding reduction for the v368 left
LCA frontier.

This file does not claim that componentwise closed embeddings alone prove the
canonical colimit map is a closed embedding.  It proves the checked bridge
between the canonical `IsColimit.map` boundary and the concrete W318
injective/inducing/closed-image certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpIscolimitMapClosedEmbeddingV368SupportW347

/-- The v368 canonical `IsColimit.map` closed-embedding boundary. -/
abbrev wppOp_lca_colimitMap_isClosedEmbedding_boundary : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y)
    (hcx : IsColimit cx),
      IsColimit cy →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
          IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt)

/-- The canonical map satisfies the cocone compatibility equations. -/
theorem isColimit_map_compat
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (hcx : IsColimit cx) :
    ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ IsColimit.map hcx cy α = α.app j ≫ cy.ι.app j :=
  fun j => IsColimit.ι_map hcx cy α j

/--
If an arbitrary compatible map out of the source colimit is supplied, it is the
canonical `IsColimit.map`.
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
The concrete W318 quotient/coequalizer fields prove the canonical v368
`IsColimit.map` closed-embedding boundary.
-/
theorem wppOp_lca_colimitMap_isClosedEmbedding_boundary_of_injective_inducing_closedImage
    (hfields :
      WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage) :
    wppOp_lca_colimitMap_isClosedEmbedding_boundary := by
  intro X Y α cx cy hcx hcy hclosed
  rcases hfields X Y α cx cy (IsColimit.map hcx cy α) hcx hcy hclosed
      (isColimit_map_compat α hcx) with
    ⟨hinj, hind, hclosedImage⟩
  exact
    WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
      (IsColimit.map hcx cy α : cx.pt → cy.pt) hinj hind hclosedImage

/--
Conversely, the canonical v368 boundary gives W318's three topological fields
for any compatible colimit map.
-/
theorem injective_inducing_closedImage_of_wppOp_lca_colimitMap_isClosedEmbedding_boundary
    (hboundary : wppOp_lca_colimitMap_isClosedEmbedding_boundary) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  have hmapClosed :
      IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt) :=
    hboundary X Y α cx cy hcx hcy hclosed
  have hmapEq : IsColimit.map hcx cy α = φ :=
    isColimit_map_eq_of_compat α φ hcx hcompat
  have hφ : IsClosedEmbedding (φ : cx.pt → cy.pt) := by
    change IsClosedEmbedding (MetrizableLCA.Hom.hom φ)
    rw [← hmapEq]
    simpa using hmapClosed
  exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/--
The v368 canonical boundary is equivalent to W318's concrete three-field
certificate.  Thus the remaining mathematical input is exactly the
quotient/coequalizer proof of injectivity, induced topology, and closed image.
-/
theorem wppOp_lca_colimitMap_isClosedEmbedding_boundary_iff_injective_inducing_closedImage :
    wppOp_lca_colimitMap_isClosedEmbedding_boundary ↔
      WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage :=
  ⟨injective_inducing_closedImage_of_wppOp_lca_colimitMap_isClosedEmbedding_boundary,
    wppOp_lca_colimitMap_isClosedEmbedding_boundary_of_injective_inducing_closedImage⟩

/-- Machine-readable W347 frontier state. -/
structure IscolimitMapClosedEmbeddingV368SupportState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedReductions : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W347 state for downstream workers. -/
def currentIscolimitMapClosedEmbeddingV368SupportState :
    IscolimitMapClosedEmbeddingV368SupportState where
  seed := "w347-20260520T202941Z-903124cd1a7cf1d1"
  selectedRoute := "canonical-iscolimit-map-to-w318-three-field-certificate"
  checkedBoundary := "wppOp_lca_colimitMap_isClosedEmbedding_boundary"
  provedReductions :=
    ["isColimit_map_compat",
      "isColimit_map_eq_of_compat",
      "wppOp_lca_colimitMap_isClosedEmbedding_boundary_of_injective_inducing_closedImage",
      "injective_inducing_closedImage_of_wppOp_lca_colimitMap_isClosedEmbedding_boundary",
      "wppOp_lca_colimitMap_isClosedEmbedding_boundary_iff_injective_inducing_closedImage"]
  remainingInputs :=
    ["prove W318.wppOp_lca_colimitMap_injective_inducing_closedImage from the concrete WalkingParallelPairᵒᵖ quotient/coequalizer presentation",
      "equivalently, prove injectivity, induced source topology, and closed image for the canonical map between coequalizer quotient presentations",
      "componentwise closed embeddings alone are not used here to prove the quotient/coequalizer relation-pullback and closed-image fields"]
  productSuccessClaimed := false

theorem currentIscolimitMapClosedEmbeddingV368SupportState_productSuccess :
    currentIscolimitMapClosedEmbeddingV368SupportState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def iscolimitMapClosedEmbeddingV368SupportDeclarationNames : List String :=
  ["wppOp_lca_colimitMap_isClosedEmbedding_boundary",
    "isColimit_map_compat",
    "isColimit_map_eq_of_compat",
    "wppOp_lca_colimitMap_isClosedEmbedding_boundary_of_injective_inducing_closedImage",
    "injective_inducing_closedImage_of_wppOp_lca_colimitMap_isClosedEmbedding_boundary",
    "wppOp_lca_colimitMap_isClosedEmbedding_boundary_iff_injective_inducing_closedImage",
    "currentIscolimitMapClosedEmbeddingV368SupportState"]

theorem iscolimitMapClosedEmbeddingV368SupportDeclarationNames_count :
    iscolimitMapClosedEmbeddingV368SupportDeclarationNames.length = 7 := rfl

section Checks

#check wppOp_lca_colimitMap_isClosedEmbedding_boundary
#check isColimit_map_compat
#check isColimit_map_eq_of_compat
#check wppOp_lca_colimitMap_isClosedEmbedding_boundary_of_injective_inducing_closedImage
#check injective_inducing_closedImage_of_wppOp_lca_colimitMap_isClosedEmbedding_boundary
#check wppOp_lca_colimitMap_isClosedEmbedding_boundary_iff_injective_inducing_closedImage
#check currentIscolimitMapClosedEmbeddingV368SupportState
#check currentIscolimitMapClosedEmbeddingV368SupportState_productSuccess
#check iscolimitMapClosedEmbeddingV368SupportDeclarationNames
#check iscolimitMapClosedEmbeddingV368SupportDeclarationNames_count

end Checks

end WppOpIscolimitMapClosedEmbeddingV368SupportW347

end LeanLCAExactChallenge
