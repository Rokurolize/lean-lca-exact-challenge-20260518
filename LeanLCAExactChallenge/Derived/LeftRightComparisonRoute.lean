import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W765 closes the local W736 comparison-isomorphism frontier under the existing
`CategoryWithHomology MetrizableLCA` premise.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W765: a `CategoryWithHomology MetrizableLCA` instance makes the canonical W736
left-right homology comparison an isomorphism for any MetrizableLCA short complex.
-/
theorem leftRightComparisonIso_of_categoryWithHomologyInstanceW765
    [CategoryWithHomology MetrizableLCA.{0}]
    (S : ShortComplex MetrizableLCA.{0}) :
    IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S) := by
  infer_instance

/--
W765 packages the previous theorem in the universal function shape consumed by
the W736-to-W764 route.
-/
theorem universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765
    [CategoryWithHomology MetrizableLCA.{0}] :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S) := by
  intro S
  exact leftRightComparisonIso_of_categoryWithHomologyInstanceW765 S

/--
W765 closed-map branch: a category-homology instance supplies the W736
comparison-isomorphism input required by the W764 route-data provider.
-/
def boundaryRelationTargetClosednessNormalizedDataProvider_of_closedMapCategoryHomologyInstanceRouteDataW765
    [CategoryWithHomology MetrizableLCA.{0}]
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  boundaryRelationTargetClosednessNormalizedDataProvider_of_closedMapLeftRightComparisonW764
    universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765
    inputs

/--
W765 closed-embedding branch: a category-homology instance supplies the W736
comparison-isomorphism input required by the W764 route-data provider.
-/
def boundaryRelationTargetClosednessNormalizedDataProvider_of_closedEmbeddingCategoryHomologyInstanceRouteDataW765
    [CategoryWithHomology MetrizableLCA.{0}]
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  boundaryRelationTargetClosednessNormalizedDataProvider_of_closedEmbeddingLeftRightComparisonW764
    universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765
    inputs

/-- W765 closed-map exact/stable evidence through the W764 route-data bridge. -/
noncomputable def exactStableEvidence_of_closedMapCategoryHomologyInstanceRouteDataW765
    [CategoryWithHomology MetrizableLCA.{0}]
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidence_of_closedMapLeftRightComparisonRouteDataW764
    universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765
    inputs

/-- W765 closed-embedding exact/stable evidence through the W764 route-data bridge. -/
noncomputable def exactStableEvidence_of_closedEmbeddingCategoryHomologyInstanceRouteDataW765
    [CategoryWithHomology MetrizableLCA.{0}]
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppExactStableEvidenceW758 :=
  exactStableEvidence_of_closedEmbeddingLeftRightComparisonRouteDataW764
    universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765
    inputs

/-- Input names for the W765 category-homology-instance route-data bridge. -/
def exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765 :
    List String :=
  exactStableWppOpCategoryHomologyInstanceConcreteLeafInputNamesW761

theorem exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765_count :
    exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765.length =
      10 := by
  simpa [exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765] using
    exactStableWppOpCategoryHomologyInstanceConcreteLeafInputNamesW761_count

/-- Current checked W765 state for the category-homology comparison route. -/
structure MetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765 :
    Type where
  seed : String
  declarations : List String
  comparisonIsoResult : String
  routeDataResult : String
  exactStableResult : String
  removedInputs : List String
  exposedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W765 state. -/
def currentMetrizableWppCategoryHomologyInstanceRouteDataExactStableSupportStateW765 :
    MetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765
    where
  seed := "w765-category-homology-left-right-comparison-route-data"
  declarations :=
    ["leftRightComparisonIso_of_categoryWithHomologyInstanceW765",
      "universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765",
      "boundaryRelationTargetClosednessNormalizedDataProvider_of_closedMapCategoryHomologyInstanceRouteDataW765",
      "boundaryRelationTargetClosednessNormalizedDataProvider_of_closedEmbeddingCategoryHomologyInstanceRouteDataW765",
      "exactStableEvidence_of_closedMapCategoryHomologyInstanceRouteDataW765",
      "exactStableEvidence_of_closedEmbeddingCategoryHomologyInstanceRouteDataW765",
      "exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765",
      "exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765_count"]
  comparisonIsoResult :=
    "proved: CategoryWithHomology MetrizableLCA supplies HasHomology for every short complex, so mathlib's left-right homology comparison isomorphism instance applies"
  routeDataResult :=
    "proved: W765 removes the explicit W736 comparison-isomorphism argument from the W764 route-data bridge under the CategoryWithHomology premise"
  exactStableResult :=
    "proved: the category-homology route feeds W764 W732 route-data evidence into W763 exactness plus accepted stable evidence"
  removedInputs :=
    ["explicit universal W736 left-right comparison-isomorphism argument after CategoryWithHomology is available"]
  exposedInputs :=
    exactStableWppOpCategoryHomologyInstanceRouteDataInputNamesW765
  remainingInputs :=
    ["construct CategoryWithHomology MetrizableLCA",
      "construct concrete values for the W735 branch data inputs",
      "construct Dbounded finite-limit, finite-colimit, suspension-loop, and pushout-pullback stable-infinity inputs"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentMetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765 :
    MetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765 :=
  currentMetrizableWppCategoryHomologyInstanceRouteDataExactStableSupportStateW765

theorem
    currentMetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765_productSuccess :
    currentMetrizableWppCategoryHomologyInstanceRouteDataExactStableStateW765.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
