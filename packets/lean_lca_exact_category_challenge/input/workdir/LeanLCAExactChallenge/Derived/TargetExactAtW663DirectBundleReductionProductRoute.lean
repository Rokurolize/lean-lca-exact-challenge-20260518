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
      "targetExactAtW663DirectBundleReductionInputNamesW807",
      "targetExactAtW663DirectBundleReductionInputNamesW807_count"]
  endpointReductionResult :=
    "proved: full W663 endpoint direct bundles feed the W803 terminal route"
  shortExactReductionResult :=
    "proved: full W663 ShortExact direct bundles feed the W803 terminal route"
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
