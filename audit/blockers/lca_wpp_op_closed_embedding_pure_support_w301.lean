import LeanLCAExactChallenge.LCA.ExactCategory
import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.Pushout
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W301: pure LCA closed-embedding boundary for WPP-op colimit maps.

W297 reduced the left closed-embedding branch to a pure theorem about a natural
transformation between two `WalkingParallelPairᵒᵖ` diagrams in `MetrizableLCA`.
This file does not prove that theorem from the current quotient API.  It proves
the checked consumer from an explicit topological certificate for the induced
coequalizer/colimit map: injectivity, induced subspace topology, and closed
image.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace LcaWppOpClosedEmbeddingPureSupportW301

/-- W289/W318's left closed-embedding preservation boundary, restated locally. -/
abbrev wppOp_colimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit cs →
        (∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
W297's component-level input, restated locally.  It still mentions short
complexes only to obtain the two component cocones and the candidate map.
-/
abbrev wppOp_component_colimitMap_preserves_closedEmbedding : Prop :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S),
      IsColimit ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCocone cs) →
        IsColimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCocone cs) →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
            (∀ j : WalkingParallelPairᵒᵖ,
              ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
                MetrizableLCA.{0}).mapCocone cs).ι.app j ≫ cs.pt.f =
                (S.obj j).f ≫
                  ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
                    MetrizableLCA.{0}).mapCocone cs).ι.app j) →
              IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
The pure W297 boundary: a natural transformation between two WPP-op LCA
diagrams whose components are closed embeddings should induce a closed
embedding between colimit points.
-/
abbrev wppOp_lca_colimitMap_preserves_closedEmbedding : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
              IsClosedEmbedding (φ : cx.pt → cy.pt)

/--
Concrete quotient/coequalizer-map input isolated by W301.  For the induced map
`φ` between WPP-op colimit points, it is enough to prove:

* injectivity of the induced map;
* that the source topology is induced from the target through `φ`;
* closedness of the image of `φ`.

This is the exact topological content of closed embedding, separated from the
categorical construction of `φ`.
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

/-- The explicit three-part topological certificate is exactly enough. -/
theorem closedEmbedding_of_injective_inducing_closedImage
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hinj : Function.Injective f) (hind : IsInducing f)
    (hclosed : IsClosed (Set.range f)) :
    IsClosedEmbedding f :=
  { toIsEmbedding := { toIsInducing := hind, injective := hinj }
    isClosed_range := hclosed }

/--
Checked reduction of the pure W297 boundary to the concrete quotient/coequalizer
closed-image plus subspace-topology theorem.
-/
theorem wppOp_lca_colimitMap_preserves_closedEmbedding_of_injective_inducing_closedImage
    (hquot : wppOp_lca_colimitMap_injective_inducing_closedImage) :
    wppOp_lca_colimitMap_preserves_closedEmbedding := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  rcases hquot X Y α cx cy φ hcx hcy hclosed hcompat with
    ⟨hinj, hind, hclosedImage⟩
  exact closedEmbedding_of_injective_inducing_closedImage
    (φ : cx.pt → cy.pt) hinj hind hclosedImage

/-- The pure component/coequalizer boundary implies W297's component boundary. -/
theorem wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap
    (hcomponent : wppOp_lca_colimitMap_preserves_closedEmbedding) :
    wppOp_component_colimitMap_preserves_closedEmbedding := by
  intro S cs h₁ h₂ hclosed hcompat
  let α : S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).f
      naturality := fun _ _ f => (S.map f).comm₁₂ }
  exact hcomponent
    (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCocone cs)
    cs.pt.f
    h₁ h₂ hclosed hcompat

/--
The W297 component boundary implies the W289/W318 left closed-embedding
preservation boundary.
-/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap
    (hcomponent : wppOp_component_colimitMap_preserves_closedEmbedding) :
    wppOp_colimit_preserves_leftClosedEmbedding := by
  intro S cs hcs hclosed
  exact hcomponent S cs
    (isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    hclosed
    (fun j => (cs.ι.app j).comm₁₂)

/--
Direct checked consumer from the concrete quotient/coequalizer topological
certificate to the W289/W318 left closed-embedding preservation boundary.
-/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
    (hquot : wppOp_lca_colimitMap_injective_inducing_closedImage) :
    wppOp_colimit_preserves_leftClosedEmbedding :=
  wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap
    (wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap
      (wppOp_lca_colimitMap_preserves_closedEmbedding_of_injective_inducing_closedImage hquot))

/-- Machine-readable W301 boundary state. -/
structure LcaWppOpClosedEmbeddingPureSupportState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumers : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W301 state for downstream workers. -/
def currentLcaWppOpClosedEmbeddingPureSupportState :
    LcaWppOpClosedEmbeddingPureSupportState where
  seed := "w301-20260520T174325Z-7f826ed6cdf0c2eb"
  selectedRoute := "pure-colimit-map-injective-inducing-closed-image-certificate"
  checkedBoundary := "wppOp_lca_colimitMap_injective_inducing_closedImage"
  provedConsumers :=
    ["closedEmbedding_of_injective_inducing_closedImage",
      "wppOp_lca_colimitMap_preserves_closedEmbedding_of_injective_inducing_closedImage",
      "wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap",
      "wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap",
      "wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage"]
  remainingInputs :=
    ["prove injectivity of the WPP-op coequalizer/colimit-induced map from the component closed embeddings and cocone compatibility",
      "prove the source quotient topology is induced from the target quotient through the induced map",
      "prove the induced map has closed image in the target quotient",
      "the current local Quotient/Cokernel/Pushout APIs provide closed-subgroup quotients and pushout closed embeddings, but not these three facts for the WPP-op coequalizer map"]
  productSuccessClaimed := false

theorem currentLcaWppOpClosedEmbeddingPureSupportState_productSuccess :
    currentLcaWppOpClosedEmbeddingPureSupportState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def lcaWppOpClosedEmbeddingPureSupportDeclarationNames : List String :=
  ["wppOp_colimit_preserves_leftClosedEmbedding",
    "wppOp_component_colimitMap_preserves_closedEmbedding",
    "wppOp_lca_colimitMap_preserves_closedEmbedding",
    "wppOp_lca_colimitMap_injective_inducing_closedImage",
    "closedEmbedding_of_injective_inducing_closedImage",
    "wppOp_lca_colimitMap_preserves_closedEmbedding_of_injective_inducing_closedImage",
    "wppOp_component_colimitMap_preserves_closedEmbedding_of_lca_colimitMap",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_component_colimitMap",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage",
    "currentLcaWppOpClosedEmbeddingPureSupportState"]

theorem lcaWppOpClosedEmbeddingPureSupportDeclarationNames_count :
    lcaWppOpClosedEmbeddingPureSupportDeclarationNames.length = 10 := rfl

section Checks

#check wppOp_colimit_preserves_leftClosedEmbedding
#check wppOp_component_colimitMap_preserves_closedEmbedding
#check wppOp_lca_colimitMap_preserves_closedEmbedding
#check wppOp_lca_colimitMap_injective_inducing_closedImage
#check closedEmbedding_of_injective_inducing_closedImage
#check wppOp_lca_colimitMap_preserves_closedEmbedding_of_injective_inducing_closedImage
#check wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
#check currentLcaWppOpClosedEmbeddingPureSupportState
#check currentLcaWppOpClosedEmbeddingPureSupportState_productSuccess
#check lcaWppOpClosedEmbeddingPureSupportDeclarationNames
#check lcaWppOpClosedEmbeddingPureSupportDeclarationNames_count
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientMap_openMap
#check MetrizableLCA.cokernelObj
#check MetrizableLCA.pushoutInr_closedEmbedding
#check MetrizableLCA.strictShortExact
#check HasCoequalizers

end Checks

end LcaWppOpClosedEmbeddingPureSupportW301

end LeanLCAExactChallenge
