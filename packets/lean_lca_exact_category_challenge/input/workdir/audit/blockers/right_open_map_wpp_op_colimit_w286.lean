import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W286: right open-map WPP-op colimit boundary.

This parent-owned audit file reimplements the useful support signal from W286.
It narrows the remaining right-open-map field to an explicit topological LCA
colimit API: the induced map between the `X₂` and `X₃` component colimits of a
WPP-op short-complex diagram is open when all component right maps are open.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace RightOpenMapWppOpColimitW286

/-- Closure of the right open-map field under the chosen WPP-op colimit. -/
abbrev rightOpenMap_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
Explicit topological LCA colimit API boundary for the right map.

The inputs are only the two degreewise colimit facts for the source and target
of the right maps, plus openness of the diagram's component right maps.
-/
abbrev openMap_walkingParallelPairOp_colimitMap_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) →
        IsColimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCocone cs) →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsOpenMap ((S.obj j).g : (S.obj j).X₂ → (S.obj j).X₃)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/--
Pure component-level LCA boundary for WPP-op colimit maps.

This removes the remaining `ShortComplex` structure from W286: the needed
source theorem is that a natural transformation between two WPP-op LCA diagrams
whose components are open maps induces an open map between colimit points.
-/
abbrev wppOp_lca_colimitMap_preserves_openMap : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
              IsOpenMap (φ : cx.pt → cy.pt)

/--
A quotient-presentation-shaped cover sufficient for the pure component open-map
boundary.  This is independent of the chosen concrete WPP-op coequalizer model:
`qX` is a surjective cover of the source colimit point, `qY` is an open cover of
the target colimit point, and `G` is an open aggregate map over the component
maps.
-/
structure WppOpLcaColimitMapOpenCover
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  QX : MetrizableLCA.{0}
  QY : MetrizableLCA.{0}
  qX : QX ⟶ cx.pt
  qY : QY ⟶ cy.pt
  G : QX ⟶ QY
  qX_surjective : Function.Surjective (qX : QX → cx.pt)
  G_open : IsOpenMap (G : QX → QY)
  qY_open : IsOpenMap (qY : QY → cy.pt)
  comm : qX ≫ φ = G ≫ qY

/-- A pure open-map cover proves openness of the induced colimit map. -/
theorem wppOp_lca_colimitMap_openMap_of_cover
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcover : WppOpLcaColimitMapOpenCover X Y α cx cy φ) :
    IsOpenMap (φ : cx.pt → cy.pt) := by
  have hcomp : IsOpenMap ((hcover.qX ≫ φ : hcover.QX ⟶ cy.pt) :
      hcover.QX → cy.pt) := by
    rw [hcover.comm]
    exact hcover.qY_open.comp hcover.G_open
  exact MetrizableLCA.isOpenMap_of_comp_surjective hcover.qX φ
    hcover.qX_surjective hcomp

/-- Pure cover construction is enough for the pure component-level LCA boundary. -/
theorem wppOp_lca_colimitMap_preserves_openMap_of_cover
    (hcover :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPairᵒᵖ,
                  cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
                  Nonempty (WppOpLcaColimitMapOpenCover X Y α cx cy φ)) :
    wppOp_lca_colimitMap_preserves_openMap := by
  intro X Y α cx cy φ hcx hcy hopen hcompat
  rcases hcover X Y α cx cy φ hcx hcy hopen hcompat with ⟨cover⟩
  exact wppOp_lca_colimitMap_openMap_of_cover cover

/-- The pure component-level LCA boundary supplies W286's short-complex boundary. -/
theorem openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap
    (hcomponent : wppOp_lca_colimitMap_preserves_openMap) :
    openMap_walkingParallelPairOp_colimitMap_boundary := by
  intro S cs h₂ h₃ hopen
  let α : S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).g
      naturality := fun _ _ f => (S.map f).comm₂₃ }
  exact hcomponent
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    cs.pt.g
    h₂ h₃ hopen
    (fun j => (cs.ι.app j).comm₂₃)

/--
The explicit topological colimit-open-map boundary supplies the W305/W307
right-open-map field.
-/
theorem rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary
    (hboundary : openMap_walkingParallelPairOp_colimitMap_boundary) :
    rightOpenMap_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hboundary S cs
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- Machine-readable frontier state for W286. -/
structure RightOpenMapWppOpColimitState : Type where
  seed : String
  selectedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W286 boundary state. -/
def currentRightOpenMapWppOpColimitState :
    RightOpenMapWppOpColimitState where
  seed := "w286-20260520T164318Z-75f9e2b44a4e3109"
  selectedBoundary :=
    "openMap_walkingParallelPairOp_colimitMap_boundary"
  provedConsumer :=
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary"
  remainingInputs :=
    ["pure LCA API: wppOp_lca_colimitMap_preserves_openMap",
      "or construct WppOpLcaColimitMapOpenCover for the induced component map",
      "degreewise source and target cocones are supplied by ShortComplex.π₂/π₃ colimit preservation"]
  productSuccessClaimed := false

theorem currentRightOpenMapWppOpColimitState_productSuccess :
    currentRightOpenMapWppOpColimitState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def rightOpenMapWppOpColimitDeclarationNames : List String :=
  ["rightOpenMap_walkingParallelPairOp_colimitClosure",
    "openMap_walkingParallelPairOp_colimitMap_boundary",
    "wppOp_lca_colimitMap_preserves_openMap",
    "WppOpLcaColimitMapOpenCover",
    "wppOp_lca_colimitMap_openMap_of_cover",
    "wppOp_lca_colimitMap_preserves_openMap_of_cover",
    "openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap",
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary",
    "currentRightOpenMapWppOpColimitState"]

theorem rightOpenMapWppOpColimitDeclarationNames_count :
    rightOpenMapWppOpColimitDeclarationNames.length = 9 := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check openMap_walkingParallelPairOp_colimitMap_boundary
#check wppOp_lca_colimitMap_preserves_openMap
#check WppOpLcaColimitMapOpenCover
#check wppOp_lca_colimitMap_openMap_of_cover
#check wppOp_lca_colimitMap_preserves_openMap_of_cover
#check openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary
#check currentRightOpenMapWppOpColimitState
#check currentRightOpenMapWppOpColimitState_productSuccess
#check rightOpenMapWppOpColimitDeclarationNames
#check rightOpenMapWppOpColimitDeclarationNames_count
#check ShortComplex.π₂
#check ShortComplex.π₃
#check isColimitOfPreserves
#check MetrizableLCA.isOpenMap_of_comp_surjective

end Checks

end RightOpenMapWppOpColimitW286

end LeanLCAExactChallenge
