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
    "canonicalTransportApiNames"]

theorem w365SupportDeclarationNames_count :
    w365SupportDeclarationNames.length = 2 := rfl

section Checks

#check isColimit_map_eq_of_compat
#check canonicalTransportApiNames
#check w365SupportDeclarationNames
#check w365SupportDeclarationNames_count

end Checks

end WppOpLeftLcaColimitTransportW365

end LeanLCAExactChallenge
