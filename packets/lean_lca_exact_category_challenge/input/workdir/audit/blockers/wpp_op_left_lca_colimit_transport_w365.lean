import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W365: categorical transport support for the left LCA map.

This audit file isolates the purely categorical equation used to compare an
arbitrary colimit-induced map `φ : cx.pt ⟶ cy.pt` with the canonical
`colimit.map α`.  It does not prove the remaining relation-preimage or closed
map inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaColimitTransportW365

variable (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
variable (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)

/--
An arbitrary map between colimit points is the `IsColimit.map` induced by `α`
as soon as it satisfies the cocone square equations.
-/
theorem isColimit_map_eq_of_compat
    (hcx : IsColimit cx)
    (hcompat : ∀ j : WalkingParallelPairᵒᵖ,
      cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/--
Intermediate topological boundary for the left LCA route: it is enough to prove
that the canonical `IsColimit.map` induced by `α` is a closed embedding.
-/
abbrev wppOp_lca_colimitMap_isClosedEmbedding_boundary : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y)
    (hcx : IsColimit cx),
      IsColimit cy →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
          IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt)

/--
The `IsColimit.map` closed-embedding boundary supplies the W318
injective/inducing/closed-image certificate for an arbitrary compatible `φ`.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_isColimitMapClosedEmbedding
    (hboundary : wppOp_lca_colimitMap_isClosedEmbedding_boundary) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  have hmapClosed : IsClosedEmbedding (IsColimit.map hcx cy α : cx.pt → cy.pt) :=
    hboundary X Y α cx cy hcx hcy hclosed
  have hmapEq : IsColimit.map hcx cy α = φ :=
    isColimit_map_eq_of_compat X Y α cx cy φ hcx hcompat
  have hφ : IsClosedEmbedding (φ : cx.pt → cy.pt) := by
    change IsClosedEmbedding (MetrizableLCA.Hom.hom φ)
    rw [← hmapEq]
    simpa using hmapClosed
  exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/--
The canonical colimit-cocone isomorphisms available for the next transport
step.  This records the exact pair of APIs needed to turn `IsColimit.map` into
an equation involving `colim.map α`.
-/
def canonicalTransportApiNames : List String :=
  ["IsColimit.comp_coconePointUniqueUpToIso_inv",
    "IsColimit.comp_coconePointUniqueUpToIso_hom",
    "colimit.ι_map",
    "colimMap_eq"]

/-- Declaration names exported by this support file. -/
def w365SupportDeclarationNames : List String :=
  ["isColimit_map_eq_of_compat",
    "wppOp_lca_colimitMap_isClosedEmbedding_boundary",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_isColimitMapClosedEmbedding",
    "canonicalTransportApiNames"]

theorem w365SupportDeclarationNames_count :
    w365SupportDeclarationNames.length = 4 := rfl

section Checks

#check isColimit_map_eq_of_compat
#check wppOp_lca_colimitMap_isClosedEmbedding_boundary
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_isColimitMapClosedEmbedding
#check canonicalTransportApiNames
#check w365SupportDeclarationNames
#check w365SupportDeclarationNames_count

end Checks

end WppOpLeftLcaColimitTransportW365

end LeanLCAExactChallenge
