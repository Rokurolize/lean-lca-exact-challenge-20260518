import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.Limits

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
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier"
  remainingInputs :=
    ["wppOp_lca_colimitMap_injective_inducing_closedImage",
      "wppOp_lca_colimitMap_preserves_openMap",
      "addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable"]
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
#check additiveKernelExact_wppOp_colimit_boundary
#check addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable
#check leftClosedEmbedding_walkingParallelPairOp_colimitClosure_of_preserves
#check closedEmbedding_of_injective_inducing_closedImage
#check wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
#check rightOpenMap_walkingParallelPairOp_colimitClosure_of_boundary
#check openMap_walkingParallelPairOp_colimitMap_boundary_of_lca_colimitMap
#check wppOp_lca_colimitMap_preserves_openMap_of_leg_certificates
#check rightMapEpi_walkingParallelPairOp_colimitClosure_direct
#check algebraicExact_walkingParallelPairOp_colimitClosure_of_additiveBoundary
#check addCommGrpKernelExact_iff_additiveKernelExact
#check additiveKernelExact_wppOp_colimit_boundary_of_addCommGrpKernelExact
#check strictShortExact_walkingParallelPairOp_colimitClosure_of_consolidated_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_consolidated_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureOpen_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureTopological_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_pureField_frontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_addCommGrpField_frontier
#check currentWppOpExactAcyclicFrontierConsolidatedState
#check currentWppOpExactAcyclicFrontierConsolidatedState_productSuccess
#check ShortComplex.π₂
#check ShortComplex.π₃
#check ShortComplex.isColimitOfIsColimitπ
#check colim.map_epi'

end Checks

end WppOpExactAcyclicFrontierConsolidatedW318

end LeanLCAExactChallenge
