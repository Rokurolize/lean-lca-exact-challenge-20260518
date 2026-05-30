import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
W814: reduce the `CategoryWithHomology MetrizableLCA` input to a concrete
topological statement about the canonical left-right homology comparison.

This does not prove the comparison is bijective and open.  It records the
smallest non-circular target found by the W814 scout: once that comparison map
is known to be a bijective open map for every MetrizableLCA short complex, the
existing `MetrizableLCA.isIso_of_bijective_openMap` helper and mathlib's
`ShortComplex.hasHomology_of_isIsoLeftRightHomologyComparison` construct the
category-level homology instance.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory

namespace MetrizableLCA

/--
W814 comparison target: every canonical left-right homology comparison in
`MetrizableLCA` is bijective and open as a continuous additive morphism.
-/
def comparisonBijectiveOpenTargetW814
    (S : ShortComplex MetrizableLCA.{0}) : Prop :=
  Function.Bijective S.leftRightHomologyComparison ∧
    IsOpenMap (S.leftRightHomologyComparison :
      S.leftHomology → S.rightHomology)

/--
W814: the concrete bijective-open comparison target supplies
`CategoryWithHomology MetrizableLCA`.
-/
theorem categoryWithHomology_of_comparisonBijectiveOpenW814
    (h :
      ∀ S : ShortComplex MetrizableLCA.{0},
        comparisonBijectiveOpenTargetW814 S) :
    CategoryWithHomology MetrizableLCA.{0} := by
  constructor
  intro S
  haveI : IsIso S.leftRightHomologyComparison :=
    MetrizableLCA.isIso_of_bijective_openMap S.leftRightHomologyComparison
      (h S).1 (h S).2
  exact ShortComplex.hasHomology_of_isIsoLeftRightHomologyComparison (S := S)

/-- Input names for the W814 category-homology comparison route. -/
def categoryHomologyComparisonBijectiveOpenInputNamesW814 :
    List String :=
  ["for every MetrizableLCA short complex, the left-right homology comparison is bijective",
    "for every MetrizableLCA short complex, the left-right homology comparison is open"]

theorem categoryHomologyComparisonBijectiveOpenInputNamesW814_count :
    categoryHomologyComparisonBijectiveOpenInputNamesW814.length =
      2 :=
  rfl

/-- Current checked W814 state for the category-homology comparison route. -/
structure CategoryHomologyComparisonBijectiveOpenRouteStateW814 :
    Type where
  seed : String
  declarations : List String
  categoryHomologyResult : String
  reducedInput : String
  rejectedRoutes : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W814 state. -/
def currentCategoryHomologyComparisonBijectiveOpenRouteSupportStateW814 :
    CategoryHomologyComparisonBijectiveOpenRouteStateW814
    where
  seed := "w814-category-homology-comparison-bijective-open-route"
  declarations :=
    ["comparisonBijectiveOpenTargetW814",
      "categoryWithHomology_of_comparisonBijectiveOpenW814",
      "categoryHomologyComparisonBijectiveOpenInputNamesW814",
      "categoryHomologyComparisonBijectiveOpenInputNamesW814_count"]
  categoryHomologyResult :=
    "proved: a universal bijective-open left-right homology comparison supplies " ++
      "CategoryWithHomology MetrizableLCA"
  reducedInput :=
    "construct the bijective-open comparison theorem for arbitrary MetrizableLCA short complexes"
  rejectedRoutes :=
    ["direct instance search for CategoryWithHomology MetrizableLCA",
      "direct instance search for the W736 comparison isomorphism",
      "unavailable direct transfer from TopModuleCat homology to MetrizableLCA"]
  remainingInputs :=
    categoryHomologyComparisonBijectiveOpenInputNamesW814
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentCategoryHomologyComparisonBijectiveOpenRouteStateW814 :
    CategoryHomologyComparisonBijectiveOpenRouteStateW814 :=
  currentCategoryHomologyComparisonBijectiveOpenRouteSupportStateW814

theorem currentW814CategoryHomologyComparisonBijectiveOpen_productSuccess :
    currentCategoryHomologyComparisonBijectiveOpenRouteStateW814.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
