import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.ExactInputsComparisonSelectedCochainStableRoute

/-!
W1614 feeds W1613 after deriving its selected-cochain data from the W851
comparison selected-cochain route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-!
W1614 closed-map exact inputs converted to the W1613 selected-cochain
comparison surface.
-/
noncomputable def
    closedMapSelectedCochainComparisonDataOfExactInputsW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedMapSelectedCochainDirectSourceDataOfComparisonW851 exactInputs

/-!
W1614 closed-embedding exact inputs converted to the W1613 selected-cochain
comparison surface.
-/
noncomputable def
    closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851 exactInputs

/-!
W1614 closed-map product evidence after W851 derives W847 data from one W735
exact-input branch.
-/
noncomputable def
    productEvidenceOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapSelectedCochainComparisonW1613
    (closedMapSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-embedding product evidence after W851 derives W847 data from one
W735 exact-input branch.
-/
noncomputable def
    productEvidenceOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingSelectedCochainComparisonW1613
    (closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-map direct finite-shape stable data through W1613.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapSelectedCochainComparisonW1613
    (closedMapSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-embedding direct finite-shape stable data through W1613.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingSelectedCochainComparisonW1613
    (closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-map stable-boundary inputs through W1613.
-/
noncomputable def
    stableBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapSelectedCochainComparisonW1613
    (closedMapSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-embedding stable-boundary inputs through W1613.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingSelectedCochainComparisonW1613
    (closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-map exact inputs as canonical direct-localization stable-instance
boundary inputs.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedMapStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
    exactInputs

/-!
W1614 closed-embedding exact inputs as canonical direct-localization
stable-instance boundary inputs.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
    exactInputs

/-!
W1614 closed-map accepted stable evidence through W1613.
-/
noncomputable def
    acceptedStableOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapSelectedCochainComparisonW1613
    (closedMapSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-embedding accepted stable evidence through W1613.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingSelectedCochainComparisonW1613
    (closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-map accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs)

/-!
W1614 closed-embedding accepted stable evidence through the canonical
direct-localization boundary.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs)

/-!
W1614 closed-map bounded derived package through W1613.
-/
noncomputable def
    boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapSelectedCochainComparisonW1613
    (closedMapSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-embedding bounded derived package through W1613.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingSelectedCochainComparisonW1613
    (closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614 exactInputs)

/-!
W1614 closed-map bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs)

/-!
W1614 closed-embedding bounded derived package through the canonical
direct-localization boundary.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs)

/-!
Top-level input names for the W1614 exact-input selected-cochain comparison
route.
-/
def boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614 :
    List String :=
  ["W735 closed-map or closed-embedding exact-input branch, including W716\
      boundary data, W519 mapped-cokernel closedness, and W720 endpoint\
      topology data"]

theorem
    boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614_count :
    boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614.length =
      1 :=
  rfl

/-!
Current checked W1614 exact-input selected-cochain comparison route state.
-/
structure
    MetrizableBoundarySourcePiZeroExactInputsSelectedCochainComparisonRouteStateW1614 :
    Type where
  seed : String
  declarations : List String
  selectedCochainResult : String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-!
Current checked W1614 state: W851 supplies the W847 data consumed by W1613.
-/
def
    currentMetrizableBoundarySourcePiZeroExactInputsSelectedCochainComparisonRouteStateW1614 :
    MetrizableBoundarySourcePiZeroExactInputsSelectedCochainComparisonRouteStateW1614
    where
  seed :=
    "w1614-boundary-source-pi-zero-exact-inputs-selected-cochain-comparison-route"
  declarations :=
    ["closedMapSelectedCochainComparisonDataOfExactInputsW1614",
      "closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614",
      "productEvidenceOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "productEvidenceOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "directFiniteShapeStableDataOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "directFiniteShapeStableDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "stableBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "stableBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "acceptedStableOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "acceptedStableOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "acceptedStableOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614",
      "acceptedStableOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614",
      "boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614",
      "boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614",
      "boundedDerivedOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614",
      "boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614",
      "boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614",
      "boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614_count"]
  selectedCochainResult :=
    "proved: W851 comparison selected-cochain data supplies the W1613 W847\
      selected-cochain branch data"
  closedMapResult :=
    "proved: one closed-map W735 exact-input branch feeds W1613 without a\
      separate W847 selected-cochain strictification field and also supplies\
      the canonical direct-localization stable-instance boundary"
  closedEmbeddingResult :=
    "proved: one closed-embedding W735 exact-input branch feeds W1613 without\
      a separate W847 selected-cochain strictification field and also supplies\
      the canonical direct-localization stable-instance boundary"
  replacedInputs :=
    ["separate W847 exact-acyclic selected-cochain strictification theorem"]
  remainingInputs :=
    ["construct concrete values for one W735 branch, including W716 boundary\
        data, W519 mapped-cokernel closedness, and W720 endpoint topology data",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem
    currentW1614BoundarySourcePiZeroExactInputsSelectedCochainComparisonRoute_productSuccess :
    (have state :=
      currentMetrizableBoundarySourcePiZeroExactInputsSelectedCochainComparisonRouteStateW1614;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
