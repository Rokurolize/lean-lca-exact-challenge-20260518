import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.Pushout
import LeanLCAExactChallenge.LCA.Pullback

/-!
W337: v360 left LCA relation/closed-map support.

This file records the checked v360-facing boundary for the W333
relation-preimage plus descended-closed-map route.  The W333 audit file is not
an importable Lean module in this worktree, so this file keeps the bridge in
terms of exact declaration names and typed fields at the categorical
`wppOp_lca_colimitMap_injective_inducing_closedImage` boundary.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaRelationClosedMapV360SupportW337

/--
The v360-side fields that must be obtained after transporting W333's
quotient-presentation theorem across the concrete coequalizer/colimit
identification.
-/
structure WppOpLeftLcaRelationClosedMapFields
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type where
  relation_preimage_exact_decl : String
  descended_closedMap_decl : String
  quotient_compat_decl : String
  colimit_descended_identification : String
  colimitMap_injective : Function.Injective (φ : cx.pt → cy.pt)
  colimitMap_inducing : IsInducing (φ : cx.pt → cy.pt)
  colimitMap_range_closed : IsClosed (Set.range (φ : cx.pt → cy.pt))

/--
Once the W333 relation/closed-map package has been transported to the
categorical colimit-induced map `φ`, it is exactly the v360 left LCA
certificate boundary.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_relationClosedMapFields
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPairᵒᵖ,
                  cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j) →
                    WppOpLeftLcaRelationClosedMapFields X Y α cx cy φ) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  exact
    let d := hfields X Y α cx cy φ hcx hcy hclosed hcompat
    ⟨d.colimitMap_injective, d.colimitMap_inducing, d.colimitMap_range_closed⟩

/--
The W333 quotient-presentation inputs, named so downstream work can line them
up with the copied support file without relying on comments.
-/
def w333RelationClosedMapInputDeclarationNames : List String :=
  ["MetrizableLCA.coequalizerMap_descended_injective_of_relation_preimage_exact",
    "MetrizableLCA.coequalizerMap_isClosedEmbedding_of_descended_closedMap",
    "MetrizableLCA.coequalizerMap_descended_range_closed_of_descended_closedMap",
    "MetrizableLCA.coequalizerMap_isClosedEmbedding_of_relation_preimage_exact_and_descended_closedMap",
    "CoequalizerClosedEmbeddingQuotientInputs.of_relation_preimage_exact_and_descended_closedMap"]

/-- Exact declarations available from the v360 boundary file for this route. -/
def v360LeftLcaBoundaryDeclarationNames : List String :=
  ["WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage",
    "WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage",
    "WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage"]

/--
Smallest missing equation found by this route: the W333 descended quotient map
must be identified with the categorical colimit-induced map `φ` after choosing
the coequalizer/cokernel quotient presentations of `cx.pt` and `cy.pt`.
-/
def smallestMissingEquation : List String :=
  ["sourceIso.hom ≫ φ = descended ≫ targetIso.hom",
    "equivalently: the categorical WPP-op colimit map is the transported W333 descended quotient map"]

/-- Machine-readable state for the W337 v360 relation/closed-map route. -/
structure WppOpLeftLcaRelationClosedMapFrontierState : Type where
  seed : String
  checkedBridge : String
  w333InputDeclarations : List String
  v360BoundaryDeclarations : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpLeftLcaRelationClosedMapFrontierState :
    WppOpLeftLcaRelationClosedMapFrontierState where
  seed := "ace0cace5b24d858629ddf165381558e"
  checkedBridge :=
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_relationClosedMapFields"
  w333InputDeclarations := w333RelationClosedMapInputDeclarationNames
  v360BoundaryDeclarations := v360LeftLcaBoundaryDeclarationNames
  remainingInputs :=
    ["derive relation_preimage_exact from component closed embedding plus the square equations",
      "derive IsClosedMap for the W333 descended quotient map, or an equivalent closed-range-plus-inducing route",
      "prove the transport equation sourceIso.hom ≫ φ = descended ≫ targetIso.hom for the concrete WPP-op coequalizer presentation"]
  productSuccessClaimed := false

theorem currentWppOpLeftLcaRelationClosedMapFrontierState_productSuccess :
    currentWppOpLeftLcaRelationClosedMapFrontierState.productSuccessClaimed = false := rfl

def w337SupportDeclarationNames : List String :=
  ["WppOpLeftLcaRelationClosedMapFields",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_relationClosedMapFields",
    "w333RelationClosedMapInputDeclarationNames",
    "v360LeftLcaBoundaryDeclarationNames",
    "smallestMissingEquation",
    "WppOpLeftLcaRelationClosedMapFrontierState",
    "currentWppOpLeftLcaRelationClosedMapFrontierState",
    "currentWppOpLeftLcaRelationClosedMapFrontierState_productSuccess"]

theorem w337SupportDeclarationNames_count :
    w337SupportDeclarationNames.length = 8 := rfl

section Checks

#check WppOpLeftLcaRelationClosedMapFields
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_relationClosedMapFields
#check w333RelationClosedMapInputDeclarationNames
#check v360LeftLcaBoundaryDeclarationNames
#check smallestMissingEquation
#check WppOpLeftLcaRelationClosedMapFrontierState
#check currentWppOpLeftLcaRelationClosedMapFrontierState
#check currentWppOpLeftLcaRelationClosedMapFrontierState_productSuccess
#check w337SupportDeclarationNames
#check w337SupportDeclarationNames_count
#check WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage
#check WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
#check WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientMap
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.cokernelπ
#check MetrizableLCA.cokernelIsColimit

end Checks

end WppOpLeftLcaRelationClosedMapV360SupportW337

end LeanLCAExactChallenge
