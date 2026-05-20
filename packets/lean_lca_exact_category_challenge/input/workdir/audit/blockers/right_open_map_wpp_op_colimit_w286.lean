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

/--
Quotient/coequalizer data for the pure component open-map boundary.
`qX` and `qY` are quotient-style covers of the source and target colimit
points, and `G` is the aggregate map before descending to the target colimit.
-/
structure WppOpLcaQuotientOpenMapData
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  QX : MetrizableLCA.{0}
  QY : MetrizableLCA.{0}
  qX : QX ⟶ cx.pt
  qY : QY ⟶ cy.pt
  G : QX ⟶ QY
  qX_surjective : Function.Surjective (qX : QX → cx.pt)
  qY_open : IsOpenMap (qY : QY → cy.pt)
  aggregate_open : IsOpenMap (G : QX → QY)
  quotient_comm : qX ≫ φ = G ≫ qY

/-- Quotient/coequalizer open-map data supplies the cover package. -/
def WppOpLcaQuotientOpenMapData.toCover
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (h : WppOpLcaQuotientOpenMapData X Y α cx cy φ) :
    WppOpLcaColimitMapOpenCover X Y α cx cy φ where
  QX := h.QX
  QY := h.QY
  qX := h.qX
  qY := h.qY
  G := h.G
  qX_surjective := h.qX_surjective
  G_open := h.aggregate_open
  qY_open := h.qY_open
  comm := h.quotient_comm

/-- Closed-subgroup quotient-cover data supplying the quotient open-map package. -/
structure WppOpLcaClosedQuotientCoverData
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  AX : MetrizableLCA.{0}
  AY : MetrizableLCA.{0}
  NX : AddSubgroup AX
  NY : AddSubgroup AY
  NX_closed : IsClosed (NX : Set AX)
  NY_closed : IsClosed (NY : Set AY)
  qX : MetrizableLCA.quotientObj AX NX NX_closed ⟶ cx.pt
  qY : MetrizableLCA.quotientObj AY NY NY_closed ⟶ cy.pt
  aggregate : MetrizableLCA.quotientObj AX NX NX_closed ⟶
    MetrizableLCA.quotientObj AY NY NY_closed
  qX_surjective : Function.Surjective
    (qX : MetrizableLCA.quotientObj AX NX NX_closed → cx.pt)
  qY_open : IsOpenMap (qY : MetrizableLCA.quotientObj AY NY NY_closed → cy.pt)
  aggregate_open : IsOpenMap
    (aggregate :
      MetrizableLCA.quotientObj AX NX NX_closed →
        MetrizableLCA.quotientObj AY NY NY_closed)
  quotient_comm : qX ≫ φ = aggregate ≫ qY

namespace WppOpLcaClosedQuotientCoverData

variable {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
variable {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}

/-- The canonical source quotient map attached to closed quotient-cover data. -/
def sourceQuotientMap (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    d.AX ⟶ MetrizableLCA.quotientObj d.AX d.NX d.NX_closed :=
  MetrizableLCA.quotientMap d.AX d.NX d.NX_closed

/-- The canonical target quotient map attached to closed quotient-cover data. -/
def targetQuotientMap (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    d.AY ⟶ MetrizableLCA.quotientObj d.AY d.NY d.NY_closed :=
  MetrizableLCA.quotientMap d.AY d.NY d.NY_closed

theorem sourceQuotientMap_surjective
    (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    Function.Surjective
      (d.sourceQuotientMap :
        d.AX → MetrizableLCA.quotientObj d.AX d.NX d.NX_closed) :=
  MetrizableLCA.quotientMap_surjective d.AX d.NX d.NX_closed

theorem sourceQuotientMap_open
    (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    IsOpenMap
      (d.sourceQuotientMap :
        d.AX → MetrizableLCA.quotientObj d.AX d.NX d.NX_closed) :=
  MetrizableLCA.quotientMap_openMap d.AX d.NX d.NX_closed

theorem targetQuotientMap_surjective
    (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    Function.Surjective
      (d.targetQuotientMap :
        d.AY → MetrizableLCA.quotientObj d.AY d.NY d.NY_closed) :=
  MetrizableLCA.quotientMap_surjective d.AY d.NY d.NY_closed

theorem targetQuotientMap_open
    (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    IsOpenMap
      (d.targetQuotientMap :
        d.AY → MetrizableLCA.quotientObj d.AY d.NY d.NY_closed) :=
  MetrizableLCA.quotientMap_openMap d.AY d.NY d.NY_closed

/-- Closed quotient-cover data constructs quotient open-map data. -/
def toQuotientOpenMapData
    (d : WppOpLcaClosedQuotientCoverData X Y α cx cy φ) :
    WppOpLcaQuotientOpenMapData X Y α cx cy φ where
  QX := MetrizableLCA.quotientObj d.AX d.NX d.NX_closed
  QY := MetrizableLCA.quotientObj d.AY d.NY d.NY_closed
  qX := d.qX
  qY := d.qY
  G := d.aggregate
  qX_surjective := d.qX_surjective
  qY_open := d.qY_open
  aggregate_open := d.aggregate_open
  quotient_comm := d.quotient_comm

end WppOpLcaClosedQuotientCoverData

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

/--
Construct the open-map cover from one component leg.  For a concrete WPP-op
coequalizer presentation, the relevant leg is expected to be the quotient map
from the source object into the colimit point.
-/
def wppOpLcaColimitMapOpenCoverOfLeg
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (j : WalkingParallelPairᵒᵖ)
    (hcompat : cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j)
    (hsource_surjective : Function.Surjective (cx.ι.app j : X.obj j → cx.pt))
    (hα_open : IsOpenMap (α.app j : X.obj j → Y.obj j))
    (htarget_open : IsOpenMap (cy.ι.app j : Y.obj j → cy.pt)) :
    WppOpLcaColimitMapOpenCover X Y α cx cy φ where
  QX := X.obj j
  QY := Y.obj j
  qX := cx.ι.app j
  qY := cy.ι.app j
  G := α.app j
  qX_surjective := hsource_surjective
  G_open := hα_open
  qY_open := htarget_open
  comm := hcompat

/-- The underlying map of an isomorphism in `MetrizableLCA` is surjective. -/
lemma metrizableLCA_iso_hom_surjective {A B : MetrizableLCA.{0}} (e : A ≅ B) :
    Function.Surjective (e.hom : A → B) := by
  intro b
  refine ⟨e.inv b, ?_⟩
  have h := congrArg (fun f : B ⟶ B => f b) e.inv_hom_id
  simpa using h

/-- The underlying map of an isomorphism in `MetrizableLCA` is open. -/
lemma metrizableLCA_iso_hom_openMap {A B : MetrizableLCA.{0}} (e : A ≅ B) :
    IsOpenMap (e.hom : A → B) := by
  intro U hU
  have hpre : e.hom '' U = (e.inv : B → A) ⁻¹' U := by
    ext b
    constructor
    · intro hb
      rcases hb with ⟨a, ha, hb⟩
      subst hb
      have h := congrArg (fun f : A ⟶ A => f a) e.hom_inv_id
      simpa using congrArg (fun x => x ∈ U) h.symm ▸ ha
    · intro hb
      refine ⟨e.inv b, hb, ?_⟩
      have h := congrArg (fun f : B ⟶ B => f b) e.inv_hom_id
      simpa using h
  rw [hpre]
  exact hU.preimage e.inv.hom.continuous

/-- Surjectivity is preserved by composing on the right with an isomorphism. -/
lemma surjective_comp_of_surjective_iso {A B C : MetrizableLCA.{0}} (q : A ⟶ B)
    (e : B ≅ C) (hq : Function.Surjective (q : A → B)) :
    Function.Surjective ((q ≫ e.hom : A ⟶ C) : A → C) := by
  intro c
  rcases hq (e.inv c) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change e.hom (q a) = c
  rw [ha]
  have h := congrArg (fun f : C ⟶ C => f c) e.inv_hom_id
  simpa using h

/-- A leg-level quotient/open certificate supplies the pure component open-map boundary. -/
theorem wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates
    (hleg :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPairᵒᵖ,
                  cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
                  ∃ j : WalkingParallelPairᵒᵖ,
                    Function.Surjective (cx.ι.app j : X.obj j → cx.pt) ∧
                      IsOpenMap (cy.ι.app j : Y.obj j → cy.pt)) :
    wppOp_lca_colimitMap_preserves_openMap := by
  intro X Y α cx cy φ hcx hcy hopen hcompat
  rcases hleg X Y α cx cy φ hcx hcy hopen hcompat with
    ⟨j, hsource_surjective, htarget_open⟩
  exact wppOp_lca_colimitMap_openMap_of_cover
    (wppOpLcaColimitMapOpenCoverOfLeg j (hcompat j)
      hsource_surjective (hopen j) htarget_open)

/--
It is enough to prove the source-surjective and target-open leg certificate for
the canonical colimit cocone at one fixed WPP-op leg.  Any other colimit cocone
is transported from the canonical one by the unique colimit-point isomorphism.
-/
theorem wppOp_lca_colimitMap_preserves_openMap_of_canonical_leg_certificates
    (j₀ : WalkingParallelPairᵒᵖ)
    (hsource : ∀ (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      Function.Surjective
        ((colimit.ι X j₀ : X.obj j₀ ⟶ (colimit X : MetrizableLCA.{0})) :
          (X.obj j₀).carrier → (colimit X : MetrizableLCA.{0})))
    (htarget : ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      IsOpenMap
        ((colimit.ι Y j₀ : Y.obj j₀ ⟶ (colimit Y : MetrizableLCA.{0})) :
          (Y.obj j₀).carrier → (colimit Y : MetrizableLCA.{0}))) :
    wppOp_lca_colimitMap_preserves_openMap := by
  apply wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates
  intro X Y α cx cy φ hcx hcy hopen hcompat
  let ex : colimit X ≅ cx.pt := (colimit.isColimit X).coconePointUniqueUpToIso hcx
  let ey : colimit Y ≅ cy.pt := (colimit.isColimit Y).coconePointUniqueUpToIso hcy
  refine ⟨j₀, ?_, ?_⟩
  · have hcomp : Function.Surjective
        ((colimit.ι X j₀ ≫ ex.hom : X.obj j₀ ⟶ cx.pt) : X.obj j₀ → cx.pt) :=
      surjective_comp_of_surjective_iso (colimit.ι X j₀) ex (hsource X)
    have hfac : colimit.ι X j₀ ≫ ex.hom = cx.ι.app j₀ := by
      simpa [ex] using
        (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X) hcx j₀)
    simpa [hfac] using hcomp
  · have hcomp : IsOpenMap
        ((colimit.ι Y j₀ ≫ ey.hom : Y.obj j₀ ⟶ cy.pt) : Y.obj j₀ → cy.pt) := by
      exact (metrizableLCA_iso_hom_openMap ey).comp (htarget Y)
    have hfac : colimit.ι Y j₀ ≫ ey.hom = cy.ι.app j₀ := by
      simpa [ey] using
        (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Y) hcy j₀)
    simpa [hfac] using hcomp

/--
For an ordinary `WalkingParallelPair`, the canonical colimit leg at `one` is
the coequalizer quotient projection, hence source-surjective and open in
`MetrizableLCA`.
-/
theorem parallelPair_canonical_colimit_leg_surjective_open
    {A B : MetrizableLCA.{0}} (f g : A ⟶ B) :
    Function.Surjective
        ((colimit.ι (parallelPair f g) WalkingParallelPair.one :
          B ⟶ (colimit (parallelPair f g) : MetrizableLCA.{0})) :
          B → (colimit (parallelPair f g) : MetrizableLCA.{0})) ∧
      IsOpenMap
        ((colimit.ι (parallelPair f g) WalkingParallelPair.one :
          B ⟶ (colimit (parallelPair f g) : MetrizableLCA.{0})) :
          B → (colimit (parallelPair f g) : MetrizableLCA.{0})) :=
  ⟨MetrizableLCA.coequalizerπ_surjective f g,
    MetrizableLCA.coequalizerπ_openMap f g⟩

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

/-- Quotient/coequalizer open-map data is enough for the pure component-level LCA boundary. -/
theorem wppOp_lca_colimitMap_preserves_openMap_of_quotientBoundary
    (hboundary :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPairᵒᵖ,
                  cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
                  Nonempty (WppOpLcaQuotientOpenMapData X Y α cx cy φ)) :
    wppOp_lca_colimitMap_preserves_openMap := by
  intro X Y α cx cy φ hcx hcy hopen hcompat
  rcases hboundary X Y α cx cy φ hcx hcy hopen hcompat with ⟨hdata⟩
  exact wppOp_lca_colimitMap_openMap_of_cover hdata.toCover

/-- Closed quotient-cover data is enough for the pure component-level LCA boundary. -/
theorem wppOp_lca_colimitMap_preserves_openMap_of_closedQuotientCoverBoundary
    (hboundary :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPairᵒᵖ,
                  cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
                  Nonempty (WppOpLcaClosedQuotientCoverData X Y α cx cy φ)) :
    wppOp_lca_colimitMap_preserves_openMap :=
  wppOp_lca_colimitMap_preserves_openMap_of_quotientBoundary
    (fun X Y α cx cy φ hcx hcy hopen hcompat => by
      rcases hboundary X Y α cx cy φ hcx hcy hopen hcompat with ⟨d⟩
      exact ⟨d.toQuotientOpenMapData⟩)

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
      "or prove the fixed canonical WPP-op colimit leg is source-surjective/open",
      "ordinary parallelPair coequalizer leg is now source-surjective/open; WPP-op reindexing remains",
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
    "WppOpLcaQuotientOpenMapData",
    "WppOpLcaQuotientOpenMapData.toCover",
    "WppOpLcaClosedQuotientCoverData",
    "WppOpLcaClosedQuotientCoverData.sourceQuotientMap",
    "WppOpLcaClosedQuotientCoverData.targetQuotientMap",
    "WppOpLcaClosedQuotientCoverData.toQuotientOpenMapData",
    "wppOp_lca_colimitMap_openMap_of_cover",
    "wppOpLcaColimitMapOpenCoverOfLeg",
    "metrizableLCA_iso_hom_surjective",
    "metrizableLCA_iso_hom_openMap",
    "surjective_comp_of_surjective_iso",
    "wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates",
    "wppOp_lca_colimitMap_preserves_openMap_of_canonical_leg_certificates",
    "parallelPair_canonical_colimit_leg_surjective_open",
    "wppOp_lca_colimitMap_preserves_openMap_of_cover",
    "wppOp_lca_colimitMap_preserves_openMap_of_quotientBoundary",
    "wppOp_lca_colimitMap_preserves_openMap_of_closedQuotientCoverBoundary",
    "openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap",
    "rightOpenMap_walkingParallelPairOp_colimitClosure_of_colimitMapBoundary",
    "currentRightOpenMapWppOpColimitState"]

theorem rightOpenMapWppOpColimitDeclarationNames_count :
    rightOpenMapWppOpColimitDeclarationNames.length = 24 := rfl

section Checks

#check rightOpenMap_walkingParallelPairOp_colimitClosure
#check openMap_walkingParallelPairOp_colimitMap_boundary
#check wppOp_lca_colimitMap_preserves_openMap
#check WppOpLcaColimitMapOpenCover
#check WppOpLcaQuotientOpenMapData
#check WppOpLcaQuotientOpenMapData.toCover
#check WppOpLcaClosedQuotientCoverData
#check WppOpLcaClosedQuotientCoverData.sourceQuotientMap
#check WppOpLcaClosedQuotientCoverData.targetQuotientMap
#check WppOpLcaClosedQuotientCoverData.toQuotientOpenMapData
#check wppOp_lca_colimitMap_openMap_of_cover
#check wppOpLcaColimitMapOpenCoverOfLeg
#check metrizableLCA_iso_hom_surjective
#check metrizableLCA_iso_hom_openMap
#check surjective_comp_of_surjective_iso
#check wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates
#check wppOp_lca_colimitMap_preserves_openMap_of_canonical_leg_certificates
#check parallelPair_canonical_colimit_leg_surjective_open
#check MetrizableLCA.coequalizerπ_surjective
#check MetrizableLCA.coequalizerπ_openMap
#check wppOp_lca_colimitMap_preserves_openMap_of_cover
#check wppOp_lca_colimitMap_preserves_openMap_of_quotientBoundary
#check wppOp_lca_colimitMap_preserves_openMap_of_closedQuotientCoverBoundary
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
