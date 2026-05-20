import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
W318: consolidated WPP-op exact-acyclic frontier after W286/W287/W289/W317.

W317 showed that W271's exact-acyclic WPP-op colimit-closure input follows from
three direct strict-exact fields: left closed embedding, right open map, and
algebraic exactness.  W286, W287, and W289 each narrowed one of those fields to a
smaller API boundary.  This file combines those consumers into one checked
frontier statement.

Remaining source theorems after this file:

* WPP-op colimits preserve left closed embeddings of the short-complex left maps;
* WPP-op component colimits preserve openness of the induced right map;
* the WPP-op colimit point satisfies the algebraic kernel exactness field.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpExactAcyclicFrontierConsolidatedW318

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/-- W271's exact-acyclic WPP-op colimit closure input, restated locally. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure : Prop :=
  ∀ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cocone K),
      IsColimit ck →
        (∀ j : WalkingParallelPairᵒᵖ, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/-- WPP-op colimits preserve the left closed-embedding field. -/
abbrev wppOp_colimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
Pure component-level LCA certificate for the left closed-embedding field.
For the induced map between WPP-op colimit points it is enough to prove
injectivity, induced source topology, and closed image.
-/
abbrev wppOp_lca_colimitMap_injective_inducing_closedImage : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
              Function.Injective (φ : cx.pt → cy.pt) ∧
                IsInducing (φ : cx.pt → cy.pt) ∧
                  IsClosed (Set.range (φ : cx.pt → cy.pt))

/-- WPP-op component colimits preserve openness of the induced right map. -/
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
Pure component-level LCA boundary for the right-open field: a natural
transformation of WPP-op LCA diagrams with open component maps induces an open
map between colimit points.
-/
abbrev wppOp_lca_colimitMap_preserves_openMap : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
              IsOpenMap (φ : cx.pt → cy.pt)

/-- Direct algebraic exactness at the WPP-op colimit point. -/
abbrev algebraicExact_walkingParallelPairOp_colimitClosure : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Element-level exactness of a short complex after forgetting topology. -/
abbrev AdditiveKernelExact (T : ShortComplex MetrizableLCA.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Element-level middle-kernel exactness for a short complex of abelian groups. -/
abbrev AddCommGrpKernelExact (T : ShortComplex AddCommGrpCat.{0}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂

/-- Right surjectivity for a short complex of abelian groups. -/
abbrev AddCommGrpRightSurjective (T : ShortComplex AddCommGrpCat.{0}) : Prop :=
  Function.Surjective (T.g : T.X₂ → T.X₃)

/-- Left injectivity for a short complex of abelian groups. -/
abbrev AddCommGrpLeftInjective (T : ShortComplex AddCommGrpCat.{0}) : Prop :=
  Function.Injective (T.f : T.X₁ → T.X₂)

/--
Pure additive WPP-op colimit exactness boundary.  This removes all topology from
the algebraic field: componentwise middle-kernel exactness must be preserved by
the WPP-op colimit point.
-/
abbrev additiveKernelExact_wppOp_colimit_boundary : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ, AdditiveKernelExact (S.obj j)) →
          AdditiveKernelExact cs.pt

/--
AddCommGrp-shaped kernel exactness boundary for the WPP-op colimit point.  This
is the topology-free version of `additiveKernelExact_wppOp_colimit_boundary`.
-/
abbrev addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          AddCommGrpKernelExact (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/-- AddCommGrp-shaped algebraic boundary retaining the algebraic strictness fields. -/
abbrev addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          AddCommGrpLeftInjective
              ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
            AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
              AddCommGrpRightSurjective
                ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          AddCommGrpKernelExact (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))

/--
Snake-input certificate that a short complex of abelian groups is the cokernel
row of a morphism between exact short complexes.
-/
structure AddCommGrpStrictSnakeCokernelData (T : ShortComplex AddCommGrpCat.{0}) :
    Type 1 where
  input : ShortComplex.SnakeInput AddCommGrpCat.{0}
  cokernelRowIso : input.L₃ ≅ T

/--
Concrete SnakeInput boundary for the strict AddCommGrp frontier.  It asks for a
cokernel-row presentation of the underlying short complex at the WPP-op colimit.
-/
abbrev addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          AddCommGrpLeftInjective
              ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
            AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
              AddCommGrpRightSurjective
                ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))) →
          Nonempty
            (AddCommGrpStrictSnakeCokernelData
              (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))

/-- Left field consumer from W289's boundary. -/
theorem leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves
    (hpres : wppOp_colimit_preserves_leftClosedEmbedding) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) := by
  intro S cs hcs hS
  exact hpres S cs hcs (fun j => (hS j).closed_inclusion)

/-- The three-part topological certificate is exactly enough for a closed embedding. -/
theorem closedEmbedding_of_injective_inducing_closedImage
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hinj : Function.Injective f) (hind : IsInducing f)
    (hclosed : IsClosed (Set.range f)) :
    IsClosedEmbedding f :=
  { toIsEmbedding := { toIsInducing := hind, injective := hinj }
    isClosed_range := hclosed }

/-- The pure LCA certificate supplies the left closed-embedding preservation boundary. -/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
    (hquot : wppOp_lca_colimitMap_injective_inducing_closedImage) :
    wppOp_colimit_preserves_leftClosedEmbedding := by
  intro S cs hcs hclosed
  let α : S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).f
      naturality := fun _ _ f => (S.map f).comm₁₂ }
  have h₁ : IsColimit
      ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) :=
    isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  have h₂ : IsColimit
      ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) :=
    isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  rcases hquot
    (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    cs.pt.f
    h₁ h₂ hclosed
    (fun j => (cs.ι.app j).comm₁₂) with ⟨hinj, hind, hclosedImage⟩
  exact closedEmbedding_of_injective_inducing_closedImage
    (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) hinj hind hclosedImage

/-- Right-open field consumer from W286's boundary. -/
theorem rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary
    (hboundary : openMap_walkingParallelPairOp_colimitMap_boundary) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) := by
  intro S cs hcs hS
  exact hboundary S cs
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- The pure component-level LCA open-map boundary supplies the W286/W318 boundary. -/
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

/-- Quotient/coequalizer data for the pure component open-map frontier. -/
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

/-- Quotient/coequalizer open-map data proves the pure component open-map input. -/
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
  have hcomp : IsOpenMap ((hdata.qX ≫ φ : hdata.QX ⟶ cy.pt) :
      hdata.QX → cy.pt) := by
    rw [hdata.quotient_comm]
    exact hdata.qY_open.comp hdata.aggregate_open
  exact MetrizableLCA.isOpenMap_of_comp_surjective hdata.qX φ
    hdata.qX_surjective hcomp

/-- Closed quotient-cover data proves the pure component open-map input. -/
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

/--
A leg-level quotient/open certificate supplies the pure component-level LCA
right-open frontier.  For the concrete WPP-op coequalizer presentation, the
expected leg is the quotient map from the coequalizer source object.
-/
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
  have hcomp : IsOpenMap ((cx.ι.app j ≫ φ : X.obj j ⟶ cy.pt) :
      X.obj j → cy.pt) := by
    rw [hcompat j]
    exact htarget_open.comp (hopen j)
  exact MetrizableLCA.isOpenMap_of_comp_surjective (cx.ι.app j) φ
    hsource_surjective hcomp

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

/-- Surjectivity can be recovered after composing on the right with an isomorphism. -/
lemma surjective_of_comp_iso {A B C : MetrizableLCA.{0}} (q : A ⟶ B)
    (e : B ≅ C)
    (hqe : Function.Surjective ((q ≫ e.hom : A ⟶ C) : A → C)) :
    Function.Surjective (q : A → B) := by
  intro b
  rcases hqe (e.hom b) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change q a = b
  have h := congrArg (fun x => e.inv x) ha
  simpa using h

/-- Openness can be recovered after composing on the right with an isomorphism. -/
lemma openMap_of_comp_iso {A B C : MetrizableLCA.{0}} (q : A ⟶ B)
    (e : B ≅ C)
    (hqe : IsOpenMap ((q ≫ e.hom : A ⟶ C) : A → C)) :
    IsOpenMap (q : A → B) := by
  have hcomp : IsOpenMap (((q ≫ e.hom) ≫ e.inv : A ⟶ B) : A → B) :=
    (metrizableLCA_iso_hom_openMap e.symm).comp hqe
  simpa [Category.assoc] using hcomp

/--
For any ordinary walking parallel-pair diagram, the `one` colimit leg is
surjective.  The proof identifies the diagram with its `parallelPair`
presentation and reuses the concrete coequalizer quotient theorem.
-/
theorem walkingParallelPair_colimit_ι_one_surjective
    (F : WalkingParallelPair ⥤ MetrizableLCA.{0}) :
    Function.Surjective
      ((colimit.ι F WalkingParallelPair.one : F.obj WalkingParallelPair.one ⟶
        (colimit F : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → (colimit F : MetrizableLCA.{0})) := by
  let η : F ≅ parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right) :=
    diagramIsoParallelPair F
  let e : colimit F ≅ colimit (parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)) :=
    HasColimit.isoOfNatIso η
  have hbase : Function.Surjective
      ((colimit.ι (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)) WalkingParallelPair.one :
        (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)).obj WalkingParallelPair.one ⟶
          (colimit (parallelPair (F.map WalkingParallelPairHom.left)
            (F.map WalkingParallelPairHom.right)) : MetrizableLCA.{0})) :
        (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)).obj WalkingParallelPair.one → _) :=
    MetrizableLCA.coequalizerπ_surjective
      (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right)
  have hcomp : Function.Surjective
      (((colimit.ι F WalkingParallelPair.one) ≫ e.hom :
        F.obj WalkingParallelPair.one ⟶
          (colimit (parallelPair (F.map WalkingParallelPairHom.left)
            (F.map WalkingParallelPairHom.right)) : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → _) := by
    simpa [e, η] using hbase
  exact surjective_of_comp_iso (colimit.ι F WalkingParallelPair.one) e hcomp

/--
For any ordinary walking parallel-pair diagram, the `one` colimit leg is open.
The proof identifies the diagram with its `parallelPair` presentation and
reuses the concrete coequalizer quotient theorem.
-/
theorem walkingParallelPair_colimit_ι_one_openMap
    (F : WalkingParallelPair ⥤ MetrizableLCA.{0}) :
    IsOpenMap
      ((colimit.ι F WalkingParallelPair.one : F.obj WalkingParallelPair.one ⟶
        (colimit F : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → (colimit F : MetrizableLCA.{0})) := by
  let η : F ≅ parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right) :=
    diagramIsoParallelPair F
  let e : colimit F ≅ colimit (parallelPair (F.map WalkingParallelPairHom.left)
      (F.map WalkingParallelPairHom.right)) :=
    HasColimit.isoOfNatIso η
  have hbase : IsOpenMap
      ((colimit.ι (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)) WalkingParallelPair.one :
        (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)).obj WalkingParallelPair.one ⟶
          (colimit (parallelPair (F.map WalkingParallelPairHom.left)
            (F.map WalkingParallelPairHom.right)) : MetrizableLCA.{0})) :
        (parallelPair (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)).obj WalkingParallelPair.one → _) :=
    MetrizableLCA.coequalizerπ_openMap
      (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right)
  have hcomp : IsOpenMap
      (((colimit.ι F WalkingParallelPair.one) ≫ e.hom :
        F.obj WalkingParallelPair.one ⟶
          (colimit (parallelPair (F.map WalkingParallelPairHom.left)
            (F.map WalkingParallelPairHom.right)) : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → _) := by
    simpa [e, η] using hbase
  exact openMap_of_comp_iso (colimit.ι F WalkingParallelPair.one) e hcomp

/--
The canonical WPP-op colimit leg at `op zero` is surjective.  This transports
the ordinary walking parallel-pair `one` leg across the
`walkingParallelPairOp` final equivalence.
-/
theorem walkingParallelPairOp_colimit_ι_opZero_surjective
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    Function.Surjective
      ((colimit.ι X (Opposite.op WalkingParallelPair.zero) :
        X.obj (Opposite.op WalkingParallelPair.zero) ⟶
          (colimit X : MetrizableLCA.{0})) :
        X.obj (Opposite.op WalkingParallelPair.zero) →
          (colimit X : MetrizableLCA.{0})) := by
  haveI : CategoryTheory.Functor.IsEquivalence walkingParallelPairOp :=
    walkingParallelPairOpEquiv.isEquivalence_functor
  haveI : CategoryTheory.Functor.Final walkingParallelPairOp := by infer_instance
  let F : WalkingParallelPair ⥤ MetrizableLCA.{0} := walkingParallelPairOp ⋙ X
  let e : colimit F ≅ colimit X := asIso (colimit.pre X walkingParallelPairOp)
  have hbase := walkingParallelPair_colimit_ι_one_surjective F
  have hcomp : Function.Surjective
      (((colimit.ι F WalkingParallelPair.one) ≫ e.hom :
        F.obj WalkingParallelPair.one ⟶ (colimit X : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → (colimit X : MetrizableLCA.{0})) :=
    surjective_comp_of_surjective_iso (colimit.ι F WalkingParallelPair.one) e hbase
  have hfac : (colimit.ι F WalkingParallelPair.one) ≫ e.hom =
      (colimit.ι X (Opposite.op WalkingParallelPair.zero) :
        X.obj (Opposite.op WalkingParallelPair.zero) ⟶ _) := by
    simpa [F, e] using colimit.ι_pre X walkingParallelPairOp WalkingParallelPair.one
  exact hfac ▸ hcomp

/--
The canonical WPP-op colimit leg at `op zero` is open.  This transports the
ordinary walking parallel-pair `one` leg across the `walkingParallelPairOp`
final equivalence.
-/
theorem walkingParallelPairOp_colimit_ι_opZero_openMap
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsOpenMap
      ((colimit.ι X (Opposite.op WalkingParallelPair.zero) :
        X.obj (Opposite.op WalkingParallelPair.zero) ⟶
          (colimit X : MetrizableLCA.{0})) :
        X.obj (Opposite.op WalkingParallelPair.zero) →
          (colimit X : MetrizableLCA.{0})) := by
  haveI : CategoryTheory.Functor.IsEquivalence walkingParallelPairOp :=
    walkingParallelPairOpEquiv.isEquivalence_functor
  haveI : CategoryTheory.Functor.Final walkingParallelPairOp := by infer_instance
  let F : WalkingParallelPair ⥤ MetrizableLCA.{0} := walkingParallelPairOp ⋙ X
  let e : colimit F ≅ colimit X := asIso (colimit.pre X walkingParallelPairOp)
  have hbase := walkingParallelPair_colimit_ι_one_openMap F
  have hcomp : IsOpenMap
      (((colimit.ι F WalkingParallelPair.one) ≫ e.hom :
        F.obj WalkingParallelPair.one ⟶ (colimit X : MetrizableLCA.{0})) :
        F.obj WalkingParallelPair.one → (colimit X : MetrizableLCA.{0})) :=
    (metrizableLCA_iso_hom_openMap e).comp hbase
  have hfac : (colimit.ι F WalkingParallelPair.one) ≫ e.hom =
      (colimit.ι X (Opposite.op WalkingParallelPair.zero) :
        X.obj (Opposite.op WalkingParallelPair.zero) ⟶ _) := by
    simpa [F, e] using colimit.ι_pre X walkingParallelPairOp WalkingParallelPair.one
  exact hfac ▸ hcomp

/-- The WPP-op fixed-leg theorem closes the pure right-open LCA input. -/
theorem wppOp_lca_colimitMap_preserves_openMap_of_wppOp_fixed_leg :
    wppOp_lca_colimitMap_preserves_openMap :=
  wppOp_lca_colimitMap_preserves_openMap_of_canonical_leg_certificates
    (Opposite.op WalkingParallelPair.zero)
    walkingParallelPairOp_colimit_ι_opZero_surjective
    walkingParallelPairOp_colimit_ι_opZero_openMap

/-- The colimit right map is categorically epi, by componentwise strict exactness. -/
theorem rightMapEpi_walkingParallelPairOp_colimitClosure_direct
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hcs : IsColimit cs)
    (hS : ∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) :
    Epi cs.pt.g := by
  let φ : (S ⋙ ShortComplex.π₂) ⟶ (S ⋙ ShortComplex.π₃) :=
    { app := fun j => (S.obj j).g
      naturality := fun j j' f => (S.map f).comm₂₃ }
  haveI hφ : ∀ j, Epi (φ.app j) := fun j => by
    dsimp [φ]
    apply (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).epi_of_epi_map
    rw [AddCommGrpCat.epi_iff_surjective]
    exact (hS j).surjective
  exact colim.map_epi' φ (ShortComplex.π₂.mapCocone cs)
    (isColimitOfPreserves ShortComplex.π₃ hcs) cs.pt.g
    (fun j => by
      dsimp [φ]
      simpa using (cs.ι.app j).comm₂₃)

/-- The pure additive boundary supplies W318's algebraic exactness field. -/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary
    (hboundary : additiveKernelExact_wppOp_colimit_boundary) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hboundary S cs hcs (fun j x₂ hx₂ => (hS j).algebraic_exact x₂ hx₂)

/-- The MetrizableLCA and AddCommGrpCat element-level predicates are definitionally aligned. -/
theorem addCommGrpKernelExact_iff_additiveKernelExact
    (T : ShortComplex MetrizableLCA.{0}) :
    AddCommGrpKernelExact (T.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ↔
      AdditiveKernelExact T := by
  rfl

/-- The AddCommGrp-shaped kernel exactness boundary supplies the additive boundary. -/
theorem additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact
    (hboundary : addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable) :
    additiveKernelExact_wppOp_colimit_boundary := by
  intro S cs hcs hS
  exact hboundary S cs hcs (fun j => (addCommGrpKernelExact_iff_additiveKernelExact
    (S.obj j)).mpr (hS j))

/-- A SnakeInput cokernel-row certificate gives element-level kernel exactness. -/
theorem addCommGrpKernelExact_of_strictSnakeCokernelData
    (T : ShortComplex AddCommGrpCat.{0})
    (d : AddCommGrpStrictSnakeCokernelData T) :
    AddCommGrpKernelExact T := by
  have hT : T.Exact := ShortComplex.exact_of_iso d.cokernelRowIso d.input.L₃_exact
  rw [ShortComplex.ab_exact_iff] at hT
  exact hT

/-- The SnakeInput cokernel-row boundary supplies the strict AddCommGrp boundary. -/
theorem addCommGrpStrictKernelExact_wppOp_colimit_boundary_of_snakeCokernel
    (hboundary : addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hS
  rcases hboundary S cs hcs hS with ⟨d⟩
  exact addCommGrpKernelExact_of_strictSnakeCokernelData
    (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) d

/--
The AddCommGrp-shaped strict kernel-exactness boundary supplies W318's
algebraic exactness field while preserving the right-surjectivity hypothesis
available from strict components.
-/
theorem algebraicExact_walkingParallelPairOp_colimitClosure_of_addCommGrpStrictKernelExact
    (hboundary : addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    algebraicExact_walkingParallelPairOp_colimitClosure := by
  intro S cs hcs hS
  exact hboundary S cs hcs (fun j =>
    ⟨(hS j).closed_inclusion.injective,
      (addCommGrpKernelExact_iff_additiveKernelExact (S.obj j)).mpr
        (fun x₂ hx₂ => (hS j).algebraic_exact x₂ hx₂),
      (hS j).surjective⟩)

/--
Consolidated strictness consumer from the W286/W287/W289-style boundaries.
-/
theorem strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
    (hclosed : wppOp_colimit_preserves_leftClosedEmbedding)
    (hopen : openMap_walkingParallelPairOp_colimitMap_boundary)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S),
        IsColimit cs →
          (∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j)) →
            MetrizableLCA.strictShortExact cs.pt := by
  intro S cs hcs hS
  have hopen_cs : IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary hopen S cs hcs hS
  haveI : Epi cs.pt.g :=
    rightMapEpi_walkingParallelPairOp_colimitClosure_direct S cs hcs hS
  have hsurj : Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) :=
    MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap cs.pt.g
      (MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero cs.pt.g
        (MetrizableLCA.cokernelπ_eq_zero_of_epi cs.pt.g))
      hopen_cs
  exact
    { closed_inclusion :=
        leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves hclosed
          S cs hcs hS
      open_map := hopen_cs
      surjective := hsurj
      algebraic_exact := halg S cs hcs hS }

/--
Consolidated exact-acyclic consumer: W271's WPP-op exact-acyclic colimit closure
follows from the three remaining source-level field-preservation inputs.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
    (hclosed : wppOp_colimit_preserves_leftClosedEmbedding)
    (hopen : openMap_walkingParallelPairOp_colimitMap_boundary)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  intro K ck hck hK i
  let S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0} :=
    K ⋙ degreeShortComplexFunctor i
  let cs : Cocone S := (degreeShortComplexFunctor i).mapCocone ck
  have hcs : IsColimit cs := by
    refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).prev i)) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) i) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isColimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).next i)) hck)
  have hS : ∀ j : WalkingParallelPairᵒᵖ, MetrizableLCA.strictShortExact (S.obj j) := by
    intro j
    exact hK j i
  exact strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
    hclosed hopen halg S cs hcs hS

/--
Variant of the consolidated consumer with the right-open input narrowed to the
pure component-level LCA colimit-map theorem.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureOpen_frontier
    (hclosed : wppOp_colimit_preserves_leftClosedEmbedding)
    (hopen : wppOp_lca_colimitMap_preserves_openMap)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
    hclosed
    (openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap hopen)
    halg

/--
Variant with both topological inputs narrowed to pure component-level LCA
frontiers.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureTopological_frontier
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hopen : wppOp_lca_colimitMap_preserves_openMap)
    (halg : algebraicExact_walkingParallelPairOp_colimitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
    (wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage hclosed)
    (openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap hopen)
    halg

/--
Variant with both topological inputs and the algebraic input narrowed to their
pure source-level frontiers.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureField_frontier
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hopen : wppOp_lca_colimitMap_preserves_openMap)
    (halg : additiveKernelExact_wppOp_colimit_boundary) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureTopological_frontier
    hclosed hopen
    (algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary halg)

/--
Variant with the algebraic input stated in the underlying AddCommGrpCat shape.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpField_frontier
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hopen : wppOp_lca_colimitMap_preserves_openMap)
    (halg : addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureField_frontier
    hclosed hopen
    (additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact halg)

/--
Variant with the algebraic input stated in the underlying AddCommGrpCat shape
and retaining the right-surjectivity part of strictness.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpStrictField_frontier
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hopen : wppOp_lca_colimitMap_preserves_openMap)
    (halg : addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureTopological_frontier
    hclosed hopen
    (algebraicExact_walkingParallelPairOp_colimitClosure_of_addCommGrpStrictKernelExact halg)

/--
The right-open input is now supplied internally by the fixed WPP-op colimit leg.
The exact-acyclic closure therefore only needs the left topological certificate
and the AddCommGrpCat kernel-exactness preservation input.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrp
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (halg : addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpField_frontier
    hclosed wppOp_lca_colimitMap_preserves_openMap_of_wppOp_fixed_leg halg

/--
The right-open input is supplied internally, and the algebraic input keeps the
right-surjectivity data from strict components.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (halg : addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpStrictField_frontier
    hclosed wppOp_lca_colimitMap_preserves_openMap_of_wppOp_fixed_leg halg

/--
The remaining algebraic input can be supplied by a SnakeInput cokernel-row
presentation of the underlying AddCommGrp short complex at the WPP-op colimit.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hsnake : addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
    hclosed
    (addCommGrpStrictKernelExact_wppOp_colimit_boundary_of_snakeCokernel hsnake)

/-- Machine-readable W318 frontier state. -/
structure WppOpExactAcyclicFrontierConsolidatedState : Type where
  seed : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W318 state for downstream workers. -/
def currentWppOpExactAcyclicFrontierConsolidatedState :
    WppOpExactAcyclicFrontierConsolidatedState where
  seed := "w318-parent-20260521T0310Z"
  provedConsumer :=
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel"
  remainingInputs :=
    ["wppOp_lca_colimitMap_injective_inducing_closedImage",
      "addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable"]
  productSuccessClaimed := false

theorem currentWppOpExactAcyclicFrontierConsolidatedState_productSuccess :
    currentWppOpExactAcyclicFrontierConsolidatedState.productSuccessClaimed = false := rfl

section Checks

#check degreeShortComplexFunctor
#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure
#check wppOp_colimit_preserves_leftClosedEmbedding
#check wppOp_lca_colimitMap_injective_inducing_closedImage
#check openMap_walkingParallelPairOp_colimitMap_boundary
#check wppOp_lca_colimitMap_preserves_openMap
#check algebraicExact_walkingParallelPairOp_colimitClosure
#check AdditiveKernelExact
#check AddCommGrpKernelExact
#check AddCommGrpRightSurjective
#check AddCommGrpLeftInjective
#check additiveKernelExact_wppOp_colimit_boundary
#check addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable
#check addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable
#check AddCommGrpStrictSnakeCokernelData
#check addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves
#check closedEmbedding_of_injective_inducing_closedImage
#check wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary
#check openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap
#check WppOpLcaQuotientOpenMapData
#check wppOp_lca_colimitMap_preserves_openMap_of_quotientBoundary
#check WppOpLcaClosedQuotientCoverData
#check WppOpLcaClosedQuotientCoverData.sourceQuotientMap
#check WppOpLcaClosedQuotientCoverData.targetQuotientMap
#check WppOpLcaClosedQuotientCoverData.toQuotientOpenMapData
#check wppOp_lca_colimitMap_preserves_openMap_of_closedQuotientCoverBoundary
#check metrizableLCA_iso_hom_surjective
#check metrizableLCA_iso_hom_openMap
#check surjective_comp_of_surjective_iso
#check wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates
#check wppOp_lca_colimitMap_preserves_openMap_of_canonical_leg_certificates
#check walkingParallelPair_colimit_ι_one_surjective
#check walkingParallelPair_colimit_ι_one_openMap
#check walkingParallelPairOp_colimit_ι_opZero_surjective
#check walkingParallelPairOp_colimit_ι_opZero_openMap
#check wppOp_lca_colimitMap_preserves_openMap_of_wppOp_fixed_leg
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary
#check addCommGrpKernelExact_iff_additiveKernelExact
#check additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact
#check addCommGrpKernelExact_of_strictSnakeCokernelData
#check addCommGrpStrictKernelExact_wppOp_colimit_boundary_of_snakeCokernel
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_addCommGrpStrictKernelExact
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureOpen_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureTopological_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureField_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpField_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpStrictField_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrp
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel
#check currentWppOpExactAcyclicFrontierConsolidatedState
#check currentWppOpExactAcyclicFrontierConsolidatedState_productSuccess
#check ShortComplex.π₂
#check ShortComplex.π₃
#check ShortComplex.isColimitOfIsColimitπ
#check colim.map_epi'

end Checks

end WppOpExactAcyclicFrontierConsolidatedW318

end LeanLCAExactChallenge
