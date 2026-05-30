import LeanLCAExactChallenge.Derived.ComparisonBijectiveEmbeddingRoute
import LeanLCAExactChallenge.Derived.LeftRightComparisonRoute

/-!
W817: connect the existing canonical comparison `IsIso` surface to the W816
bijective-embedding target.

W816 reduced the W814 target to bijectivity plus embedding of the canonical
left-right homology comparison.  This helper proves those concrete topological
fields follow from a categorical isomorphism of the same comparison morphism,
and records that the older W736 universal comparison-isomorphism input feeds
the W816 target without an extra open-map obligation.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

/-- A categorical isomorphism in `MetrizableLCA` has a bijective underlying map. -/
theorem bijective_of_isIsoW817
    {A B : MetrizableLCA.{0}} (f : A ⟶ B) [IsIso f] :
    Function.Bijective (f : A → B) := by
  let e := isoToContinuousAddEquiv (asIso f)
  exact e.bijective

/-- A categorical isomorphism in `MetrizableLCA` has an embedded underlying map. -/
theorem isEmbedding_of_isIsoW817
    {A B : MetrizableLCA.{0}} (f : A ⟶ B) [IsIso f] :
    IsEmbedding (f : A → B) := by
  let e := isoToContinuousAddEquiv (asIso f)
  exact e.toHomeomorph.isEmbedding

/--
W817: an isomorphism of the canonical comparison supplies the W816 concrete
bijective-embedding comparison target.
-/
theorem comparisonBijectiveEmbeddingTarget_of_isIsoW817
    (S : ShortComplex MetrizableLCA.{0})
    [IsIso S.leftRightHomologyComparison] :
    comparisonBijectiveEmbeddingTargetW816 S :=
  ⟨bijective_of_isIsoW817 S.leftRightHomologyComparison,
    isEmbedding_of_isIsoW817 S.leftRightHomologyComparison⟩

/--
W817: the W736 universal comparison-isomorphism input feeds the W816 universal
bijective-embedding target.
-/
theorem universalComparisonBijectiveEmbeddingTarget_of_w736ComparisonIsoW817
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso
          (Dbounded.leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)) :
    ∀ S : ShortComplex MetrizableLCA.{0},
      comparisonBijectiveEmbeddingTargetW816 S := by
  intro S
  haveI : IsIso S.leftRightHomologyComparison := by
    simpa [Dbounded.leftRightHomologyComparison_of_metrizableKernelCokernelW736]
      using comparisonIso S
  exact comparisonBijectiveEmbeddingTarget_of_isIsoW817 S

/--
W817: the W736 universal comparison-isomorphism input constructs
`CategoryWithHomology MetrizableLCA` through the explicit W816 target.
-/
theorem categoryWithHomology_of_w736ComparisonIsoViaEmbeddingW817
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso
          (Dbounded.leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)) :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonBijectiveEmbeddingW816
    (universalComparisonBijectiveEmbeddingTarget_of_w736ComparisonIsoW817
      comparisonIso)

/-- Input names for the W817 comparison-isomorphism to embedding route. -/
def comparisonIsomorphismEmbeddingInputNamesW817 :
    List String :=
  ["universal IsIso for the canonical left-right homology comparison"]

theorem comparisonIsomorphismEmbeddingInputNamesW817_count :
    comparisonIsomorphismEmbeddingInputNamesW817.length = 1 :=
  rfl

/-- Current checked W817 state for the comparison-isomorphism bridge. -/
structure ComparisonIsomorphismEmbeddingRouteStateW817 :
    Type where
  seed : String
  declarations : List String
  bridgeResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W817 state. -/
def currentComparisonIsomorphismEmbeddingRouteSupportStateW817 :
    ComparisonIsomorphismEmbeddingRouteStateW817
    where
  seed := "w817-comparison-isomorphism-embedding-route"
  declarations :=
    ["bijective_of_isIsoW817",
      "isEmbedding_of_isIsoW817",
      "comparisonBijectiveEmbeddingTarget_of_isIsoW817",
      "universalComparisonBijectiveEmbeddingTarget_of_w736ComparisonIsoW817",
      "categoryWithHomology_of_w736ComparisonIsoViaEmbeddingW817",
      "comparisonIsomorphismEmbeddingInputNamesW817",
      "comparisonIsomorphismEmbeddingInputNamesW817_count"]
  bridgeResult :=
    "proved: a categorical isomorphism of the canonical comparison supplies " ++
      "the W816 concrete bijective-embedding target"
  removedInputs :=
    ["separate topological embedding/open-map obligation after a W736-style " ++
      "canonical comparison isomorphism is proved"]
  remainingInputs :=
    comparisonIsomorphismEmbeddingInputNamesW817
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentComparisonIsomorphismEmbeddingRouteStateW817 :
    ComparisonIsomorphismEmbeddingRouteStateW817 :=
  currentComparisonIsomorphismEmbeddingRouteSupportStateW817

theorem currentComparisonIsomorphismEmbeddingRouteStateW817_productSuccess :
    currentComparisonIsomorphismEmbeddingRouteStateW817.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
