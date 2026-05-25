import LeanLCAExactChallenge.Derived.ComparisonIsomorphismEmbeddingRoute
import Mathlib.Topology.Maps.OpenQuotient

/-!
W818: port the `TopModuleCat` comparison-embedding criterion to
`MetrizableLCA` homology data.

W815 supplied the open quotient projections and closed embedded inclusions for
arbitrary left/right homology data.  This helper uses the same
open-quotient/inducing square as mathlib's `TopModuleCat` homology proof to
show that the canonical comparison is an embedding once its algebraic
injectivity and the concrete fiber-saturation condition are available.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

universe u

/-- A continuous additive morphism that is surjective and open is an open quotient map. -/
theorem isOpenQuotientMap_of_surjective_openMapW818
    {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hsurj : Function.Surjective (f : A → B))
    (hopen : IsOpenMap (f : A → B)) :
    IsOpenQuotientMap (f : A → B) :=
  ⟨hsurj, f.hom.continuous, hopen⟩

/-- The left homology projection in any left homology data is an open quotient map. -/
theorem leftHomologyData_π_openQuotientMapW818
    {S : ShortComplex MetrizableLCA.{u}} (h : S.LeftHomologyData) :
    IsOpenQuotientMap (h.π : h.K → h.H) :=
  isOpenQuotientMap_of_surjective_openMapW818 h.π
    (leftHomologyData_π_surjectiveW815 h)
    (leftHomologyData_π_openMapW815 h)

/-- The cokernel projection in any right homology data is an open quotient map. -/
theorem rightHomologyData_p_openQuotientMapW818
    {S : ShortComplex MetrizableLCA.{u}} (h : S.RightHomologyData) :
    IsOpenQuotientMap (h.p : S.X₂ → h.Q) :=
  isOpenQuotientMap_of_surjective_openMapW818 h.p
    (rightHomologyData_p_surjectiveW815 h)
    (rightHomologyData_p_openMapW815 h)

/--
The fiber-saturation condition used by the open-quotient/inducing comparison
criterion.  It says that points of `X₂` whose image in the right cokernel lies
over the image of the left cycles already lie in the left-cycle range.
-/
def leftRightComparisonFiberSaturationW818
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) : Prop :=
  (h₂.p : S.X₂ → h₂.Q) ⁻¹'
      ((h₂.p : S.X₂ → h₂.Q) ''
        Set.range (h₁.i : h₁.K → S.X₂)) ⊆
    Set.range (h₁.i : h₁.K → S.X₂)

/-- The underlying square for the canonical left-right homology comparison. -/
theorem leftRightHomologyComparison'_squareW818
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    ((ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι :
        h₁.H ⟶ h₂.Q) : h₁.H → h₂.Q) ∘
      (h₁.π : h₁.K → h₁.H) =
    (h₂.p : S.X₂ → h₂.Q) ∘
      (h₁.i : h₁.K → S.X₂) := by
  funext x
  change h₂.ι ((ShortComplex.leftRightHomologyComparison' h₁ h₂) (h₁.π x)) =
    h₂.p (h₁.i x)
  have hsq :
      h₁.π ≫ ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι =
        h₁.i ≫ h₂.p :=
    ShortComplex.π_leftRightHomologyComparison'_ι h₁ h₂
  exact congrArg (fun f : h₁.K ⟶ h₂.Q => (f : h₁.K → h₂.Q) x) hsq

/--
W818: the TopModuleCat-style open-quotient/inducing criterion proves that the
canonical comparison composite into right cycles is an embedding.
-/
theorem leftRightHomologyComparison'_comp_ι_embedding_of_bijective_saturatedW818
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    (hbij :
      Function.Bijective
        (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H))
    (hsat : leftRightComparisonFiberSaturationW818 h₁ h₂) :
    IsEmbedding
      ((ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι :
        h₁.H ⟶ h₂.Q) : h₁.H → h₂.Q) := by
  refine isEmbedding_of_isOpenQuotientMap_of_isInducing
    (f := (h₁.i : h₁.K → S.X₂))
    (g := ((ShortComplex.leftRightHomologyComparison' h₁ h₂ ≫ h₂.ι :
      h₁.H ⟶ h₂.Q) : h₁.H → h₂.Q))
    (p := (h₁.π : h₁.K → h₁.H))
    (q := (h₂.p : S.X₂ → h₂.Q))
    (leftRightHomologyComparison'_squareW818 h₁ h₂)
    (leftHomologyData_i_closedEmbeddingW815 h₁).isInducing
    (leftHomologyData_π_openQuotientMapW818 h₁).isQuotientMap
    (rightHomologyData_p_openQuotientMapW818 h₂) ?_ hsat
  intro x y hxy
  exact hbij.1 ((rightHomologyData_ι_closedEmbeddingW815 h₂).isEmbedding.injective hxy)

/--
W818: the fiber-saturation criterion proves the embedding field of the
canonical left-right homology comparison.
-/
theorem leftRightHomologyComparison'_embedding_of_bijective_saturatedW818
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
    (hbij :
      Function.Bijective
        (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H))
    (hsat : leftRightComparisonFiberSaturationW818 h₁ h₂) :
    IsEmbedding
      (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H) :=
  IsEmbedding.of_comp
    (ShortComplex.leftRightHomologyComparison' h₁ h₂).hom.continuous
    h₂.ι.hom.continuous
    (leftRightHomologyComparison'_comp_ι_embedding_of_bijective_saturatedW818
      h₁ h₂ hbij hsat)

/--
W818 target: algebraic bijectivity plus the concrete fiber-saturation condition
for the canonical comparison map.
-/
def comparisonFiberSaturationTargetW818
    (S : ShortComplex MetrizableLCA.{0}) : Prop :=
  Function.Bijective (S.leftRightHomologyComparison :
      S.leftHomology → S.rightHomology) ∧
    leftRightComparisonFiberSaturationW818
      S.leftHomologyData S.rightHomologyData

/-- W818 converts the fiber-saturation target into the W816 bijective-embedding target. -/
theorem comparisonBijectiveEmbeddingTarget_of_fiberSaturationW818
    (S : ShortComplex MetrizableLCA.{0})
    (h : comparisonFiberSaturationTargetW818 S) :
    comparisonBijectiveEmbeddingTargetW816 S :=
  ⟨h.1,
    leftRightHomologyComparison'_embedding_of_bijective_saturatedW818
      S.leftHomologyData S.rightHomologyData
      (by
        simpa [ShortComplex.leftRightHomologyComparison] using h.1)
      h.2⟩

/--
W818: a universal algebraic-bijectivity plus fiber-saturation theorem supplies
`CategoryWithHomology MetrizableLCA` through the W816 route.
-/
theorem categoryWithHomology_of_comparisonFiberSaturationW818
    (h :
      ∀ S : ShortComplex MetrizableLCA.{0},
        comparisonFiberSaturationTargetW818 S) :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonBijectiveEmbeddingW816
    (fun S => comparisonBijectiveEmbeddingTarget_of_fiberSaturationW818 S (h S))

/-- Input names for the W818 comparison embedding criterion route. -/
def comparisonEmbeddingCriterionInputNamesW818 :
    List String :=
  ["algebraic bijectivity of the canonical left-right homology comparison",
    "fiber-saturation of the left-cycle range under the right cokernel projection"]

theorem comparisonEmbeddingCriterionInputNamesW818_count :
    comparisonEmbeddingCriterionInputNamesW818.length = 2 :=
  rfl

/-- Current checked W818 state for the comparison embedding criterion. -/
structure ComparisonEmbeddingCriterionRouteStateW818 :
    Type where
  seed : String
  declarations : List String
  topologyResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W818 state. -/
def currentComparisonEmbeddingCriterionRouteSupportStateW818 :
    ComparisonEmbeddingCriterionRouteStateW818
    where
  seed := "w818-comparison-embedding-criterion-route"
  declarations :=
    ["isOpenQuotientMap_of_surjective_openMapW818",
      "leftHomologyData_π_openQuotientMapW818",
      "rightHomologyData_p_openQuotientMapW818",
      "leftRightComparisonFiberSaturationW818",
      "leftRightHomologyComparison'_squareW818",
      "leftRightHomologyComparison'_comp_ι_embedding_of_bijective_saturatedW818",
      "leftRightHomologyComparison'_embedding_of_bijective_saturatedW818",
      "comparisonFiberSaturationTargetW818",
      "comparisonBijectiveEmbeddingTarget_of_fiberSaturationW818",
      "categoryWithHomology_of_comparisonFiberSaturationW818",
      "comparisonEmbeddingCriterionInputNamesW818",
      "comparisonEmbeddingCriterionInputNamesW818_count"]
  topologyResult :=
    "proved: W815 projection topology plus algebraic injectivity and fiber saturation " ++
      "give the embedding field of the canonical comparison"
  removedInputs :=
    ["separate topological embedding proof after algebraic bijectivity and " ++
      "right-cokernel fiber saturation are available"]
  remainingInputs :=
    comparisonEmbeddingCriterionInputNamesW818
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentComparisonEmbeddingCriterionRouteStateW818 :
    ComparisonEmbeddingCriterionRouteStateW818 :=
  currentComparisonEmbeddingCriterionRouteSupportStateW818

theorem currentComparisonEmbeddingCriterionRouteStateW818_productSuccess :
    currentComparisonEmbeddingCriterionRouteStateW818.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
