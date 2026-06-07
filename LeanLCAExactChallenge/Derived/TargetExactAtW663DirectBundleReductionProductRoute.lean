import LeanLCAExactChallenge.Derived.TargetExactAtW663BundleReductionProductRoute

/-!
W807 lifts the W806 target-ExactAt W663 payload reduction to the full W663
direct finite-shape bundles, proving that the direct source carried by those
bundles is not needed for the current terminal product-evidence route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W807 extracts the W663 endpoint target-ExactAt payload from a direct bundle. -/
def endpointPayloadOfDirectEndpointBundleW807
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663) :
    MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663 :=
  bundle.endpointPayload

/-- W807 extracts the W663 ShortExact target-ExactAt payload from a direct bundle. -/
def shortExactPayloadOfDirectShortExactBundleW807
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663) :
    MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663 :=
  bundle.shortExactPayload

/-- W807 closed-map endpoint direct bundle reduced to W803 terminal data. -/
noncomputable def closedMapTargetExactAtW803DataOfDirectEndpointBundleW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803 :=
  closedMapTargetExactAtW803DataOfEndpointBundleW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding endpoint direct bundle reduced to W803 terminal data.
-/
noncomputable def
    closedEmbeddingTargetExactAtW803DataOfDirectEndpointBundleW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803 :=
  closedEmbeddingTargetExactAtW803DataOfEndpointBundleW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-- W807 closed-map ShortExact direct bundle reduced to W803 terminal data. -/
noncomputable def closedMapTargetExactAtW803DataOfDirectShortExactBundleW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803 :=
  closedMapTargetExactAtW803DataOfShortExactBundleW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding ShortExact direct bundle reduced to W803 terminal data.
-/
noncomputable def
    closedEmbeddingTargetExactAtW803DataOfDirectShortExactBundleW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803 :=
  closedEmbeddingTargetExactAtW803DataOfShortExactBundleW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-map endpoint direct bundle product evidence through the W803 route.
-/
noncomputable def productEvidence_of_closedMapDirectEndpointBundleReducedRouteW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapEndpointBundleReducedRouteW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding endpoint direct bundle product evidence through the W803
route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingDirectEndpointBundleReducedRouteW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingEndpointBundleReducedRouteW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-map ShortExact direct bundle product evidence through the W803 route.
-/
noncomputable def productEvidence_of_closedMapDirectShortExactBundleReducedRouteW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapShortExactBundleReducedRouteW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding ShortExact direct bundle product evidence through the W803
route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingDirectShortExactBundleReducedRouteW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingShortExactBundleReducedRouteW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-map direct endpoint bundle evidence as W806/W803 direct stable data.
-/
noncomputable def directFiniteShapeStableDataOfClosedMapDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct endpoint bundle evidence as W806/W803 direct stable
data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-map direct ShortExact bundle evidence as W806/W803 direct stable
data.
-/
noncomputable def directFiniteShapeStableDataOfClosedMapDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct ShortExact bundle evidence as W806/W803 direct
stable data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-! W807 closed-map direct endpoint bundle evidence as stable-boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct endpoint bundle evidence as stable-boundary inputs.
-/
noncomputable def stableBoundaryInputsOfClosedEmbeddingDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-map direct ShortExact bundle evidence as stable-boundary inputs.
-/
noncomputable def stableBoundaryInputsOfClosedMapDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct ShortExact bundle evidence as stable-boundary
inputs.
-/
noncomputable def stableBoundaryInputsOfClosedEmbeddingDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-! W807 closed-map direct endpoint bundle evidence passes the stable boundary. -/
noncomputable def acceptedStableOfClosedMapDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct endpoint bundle evidence passes the stable boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingDirectEndpointBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingEndpointBundleReducedW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-! W807 closed-map direct ShortExact bundle evidence passes the stable boundary. -/
noncomputable def acceptedStableOfClosedMapDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct ShortExact bundle evidence passes the stable
boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingDirectShortExactBundleReducedW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingShortExactBundleReducedW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-map direct endpoint bundle evidence produces the stable-boundary
package.
-/
noncomputable def boundedDerivedOfClosedMapDirectEndpointBundleReducedStableBoundaryW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapEndpointBundleReducedStableBoundaryW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct endpoint bundle evidence produces the
stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingDirectEndpointBundleReducedStableBoundaryW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeEndpointDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingEndpointBundleReducedStableBoundaryW806
    comparisonIso (endpointPayloadOfDirectEndpointBundleW807 bundle) exactInputs

/-!
W807 closed-map direct ShortExact bundle evidence produces the stable-boundary
package.
-/
noncomputable def
    boundedDerivedOfClosedMapDirectShortExactBundleReducedStableBoundaryW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapShortExactBundleReducedStableBoundaryW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-!
W807 closed-embedding direct ShortExact bundle evidence produces the
stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingDirectShortExactBundleReducedStableBoundaryW807
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (bundle :
      MetrizableWppDirectFiniteShapeShortExactDirectLocalizationTargetExactAtBundleW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingShortExactBundleReducedStableBoundaryW806
    comparisonIso (shortExactPayloadOfDirectShortExactBundleW807 bundle) exactInputs

/-- W807 input names for full W663 direct-bundle reduction to W803 terminal route. -/
def targetExactAtW663DirectBundleReductionInputNamesW807 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "full W663 direct finite-shape endpoint or ShortExact target-ExactAt bundle"]

theorem targetExactAtW663DirectBundleReductionInputNamesW807_count :
    targetExactAtW663DirectBundleReductionInputNamesW807.length = 3 :=
  rfl

structure MetrizableTargetExactAtW663DirectBundleReductionStateW807 :
    Type where
  seed : String
  declarations : List String
  endpointReductionResult : String
  shortExactReductionResult : String
  stableBoundaryResult : String
  droppedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtW663DirectBundleReductionStateW807 :
    MetrizableTargetExactAtW663DirectBundleReductionStateW807
    where
  seed := "w807-target-exactat-w663-direct-bundle-reduction-route"
  declarations :=
    ["endpointPayloadOfDirectEndpointBundleW807",
      "shortExactPayloadOfDirectShortExactBundleW807",
      "closedMapTargetExactAtW803DataOfDirectEndpointBundleW807",
      "closedEmbeddingTargetExactAtW803DataOfDirectEndpointBundleW807",
      "closedMapTargetExactAtW803DataOfDirectShortExactBundleW807",
      "closedEmbeddingTargetExactAtW803DataOfDirectShortExactBundleW807",
      "productEvidence_of_closedMapDirectEndpointBundleReducedRouteW807",
      "productEvidence_of_closedEmbeddingDirectEndpointBundleReducedRouteW807",
      "productEvidence_of_closedMapDirectShortExactBundleReducedRouteW807",
      "productEvidence_of_closedEmbeddingDirectShortExactBundleReducedRouteW807",
      "directFiniteShapeStableDataOfClosedMapDirectEndpointBundleReducedW807",
      "directFiniteShapeStableDataOfClosedEmbeddingDirectEndpointBundleReducedW807",
      "directFiniteShapeStableDataOfClosedMapDirectShortExactBundleReducedW807",
      "directFiniteShapeStableDataOfClosedEmbeddingDirectShortExactBundleReducedW807",
      "stableBoundaryInputsOfClosedMapDirectEndpointBundleReducedW807",
      "stableBoundaryInputsOfClosedEmbeddingDirectEndpointBundleReducedW807",
      "stableBoundaryInputsOfClosedMapDirectShortExactBundleReducedW807",
      "stableBoundaryInputsOfClosedEmbeddingDirectShortExactBundleReducedW807",
      "acceptedStableOfClosedMapDirectEndpointBundleReducedW807",
      "acceptedStableOfClosedEmbeddingDirectEndpointBundleReducedW807",
      "acceptedStableOfClosedMapDirectShortExactBundleReducedW807",
      "acceptedStableOfClosedEmbeddingDirectShortExactBundleReducedW807",
      "boundedDerivedOfClosedMapDirectEndpointBundleReducedStableBoundaryW807",
      "boundedDerivedOfClosedEmbeddingDirectEndpointBundleReducedStableBoundaryW807",
      "boundedDerivedOfClosedMapDirectShortExactBundleReducedStableBoundaryW807",
      "boundedDerivedOfClosedEmbeddingDirectShortExactBundleReducedStableBoundaryW807",
      "targetExactAtW663DirectBundleReductionInputNamesW807",
      "targetExactAtW663DirectBundleReductionInputNamesW807_count"]
  endpointReductionResult :=
    "proved: full W663 endpoint direct bundles feed the W803 terminal route"
  shortExactReductionResult :=
    "proved: full W663 ShortExact direct bundles feed the W803 terminal route"
  stableBoundaryResult :=
    "proved: full W663 endpoint and ShortExact direct bundles expose the W806\
      stable-boundary gate"
  droppedInputs :=
    ["direct finite-shape WPP source field",
      "endpoint or ShortExact topology fields",
      "global homology field carried by the W663 payload",
      "bounded homotopy localized right adjoint and direct localization fields"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target ExactAt realization data for exact-acyclic homotopy\
        objects"]
  productSuccessClaimed := false

theorem currentW807TargetExactAtW663DirectBundleReduction_productSuccess :
    (have state :=
      currentMetrizableTargetExactAtW663DirectBundleReductionStateW807;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
