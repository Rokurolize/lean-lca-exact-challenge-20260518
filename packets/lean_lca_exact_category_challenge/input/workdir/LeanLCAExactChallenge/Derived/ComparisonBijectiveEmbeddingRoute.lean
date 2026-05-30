import LeanLCAExactChallenge.Derived.ComparisonProjectionTopologyRoute

/-!
W816: reduce the W814 bijective-open comparison target to a bijective-embedding
comparison target.

W815 supplies the projection-topology facts that should feed an embedding proof
for the canonical left-right homology comparison.  This helper records the
standard topological bridge: once the comparison is bijective and an embedding,
its surjectivity makes it an open embedding, hence an open map.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

/-- A surjective embedding is an open map. -/
theorem isOpenMap_of_surjective_isEmbeddingW816
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hsurj : Function.Surjective f) (hemb : IsEmbedding f) :
    IsOpenMap f :=
  (hemb.isOpenEmbedding_of_surjective hsurj).isOpenMap

/--
W816 comparison target: the W814 comparison map is bijective and an embedding.
The open-map field then follows formally from surjectivity.
-/
def comparisonBijectiveEmbeddingTargetW816
    (S : ShortComplex MetrizableLCA.{0}) : Prop :=
  Function.Bijective S.leftRightHomologyComparison ∧
    IsEmbedding (S.leftRightHomologyComparison :
      S.leftHomology → S.rightHomology)

/-- W816 converts the bijective-embedding target into the W814 bijective-open target. -/
theorem comparisonBijectiveOpenTarget_of_bijectiveEmbeddingW816
    (S : ShortComplex MetrizableLCA.{0})
    (h : comparisonBijectiveEmbeddingTargetW816 S) :
    comparisonBijectiveOpenTargetW814 S :=
  ⟨h.1,
    isOpenMap_of_surjective_isEmbeddingW816
      (f := (S.leftRightHomologyComparison :
        S.leftHomology → S.rightHomology))
      h.1.2 h.2⟩

/--
W816: a universal bijective-embedding theorem for the canonical comparison maps
supplies `CategoryWithHomology MetrizableLCA`.
-/
theorem categoryWithHomology_of_comparisonBijectiveEmbeddingW816
    (h :
      ∀ S : ShortComplex MetrizableLCA.{0},
        comparisonBijectiveEmbeddingTargetW816 S) :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonBijectiveOpenW814
    (fun S => comparisonBijectiveOpenTarget_of_bijectiveEmbeddingW816 S (h S))

/-- Input names for the W816 comparison embedding route. -/
def comparisonBijectiveEmbeddingInputNamesW816 :
    List String :=
  ["algebraic bijectivity of the canonical left-right homology comparison",
    "embedding of the canonical left-right homology comparison"]

theorem comparisonBijectiveEmbeddingInputNamesW816_count :
    comparisonBijectiveEmbeddingInputNamesW816.length = 2 :=
  rfl

/-- Current checked W816 state for the bijective-embedding bridge. -/
structure ComparisonBijectiveEmbeddingRouteStateW816 :
    Type where
  seed : String
  declarations : List String
  bridgeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W816 state. -/
def currentComparisonBijectiveEmbeddingRouteSupportStateW816 :
    ComparisonBijectiveEmbeddingRouteStateW816
    where
  seed := "w816-comparison-bijective-embedding-route"
  declarations :=
    ["isOpenMap_of_surjective_isEmbeddingW816",
      "comparisonBijectiveEmbeddingTargetW816",
      "comparisonBijectiveOpenTarget_of_bijectiveEmbeddingW816",
      "categoryWithHomology_of_comparisonBijectiveEmbeddingW816",
      "comparisonBijectiveEmbeddingInputNamesW816",
      "comparisonBijectiveEmbeddingInputNamesW816_count"]
  bridgeResult :=
    "proved: bijective embedding of the canonical comparison implies the W814 " ++
      "bijective-open target and hence CategoryWithHomology MetrizableLCA"
  remainingInputs :=
    comparisonBijectiveEmbeddingInputNamesW816
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentComparisonBijectiveEmbeddingRouteStateW816 :
    ComparisonBijectiveEmbeddingRouteStateW816 :=
  currentComparisonBijectiveEmbeddingRouteSupportStateW816

theorem currentComparisonBijectiveEmbeddingRouteStateW816_productSuccess :
    currentComparisonBijectiveEmbeddingRouteStateW816.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
