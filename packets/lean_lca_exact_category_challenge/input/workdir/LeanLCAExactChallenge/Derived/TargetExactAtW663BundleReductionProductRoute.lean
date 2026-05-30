import LeanLCAExactChallenge.Derived.TargetExactAtEndpointReductionProductRoute

/-!
W806 lets W663 endpoint and ShortExact target-ExactAt payload bundles feed the
current W803 terminal route, ignoring the extra localization/topology fields
that are not needed for terminal evidence.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W806 extracts W785 target-ExactAt data from a W663 endpoint payload bundle. -/
def targetExactAtPayloadOfEndpointBundleW806
    (payload :
      MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  payload.targetExactAtPayload

/-- W806 extracts W785 target-ExactAt data from a W663 ShortExact payload bundle. -/
def targetExactAtPayloadOfShortExactBundleW806
    (payload :
      MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  payload.targetExactAtPayload

/-- W806 closed-map endpoint W663 bundle reduced to W803 terminal data. -/
noncomputable def closedMapTargetExactAtW803DataOfEndpointBundleW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := comparisonIso
  targetExactAtPayload := targetExactAtPayloadOfEndpointBundleW806 payload
  exactInputs := exactInputs

/-- W806 closed-embedding endpoint W663 bundle reduced to W803 terminal data. -/
noncomputable def closedEmbeddingTargetExactAtW803DataOfEndpointBundleW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := comparisonIso
  targetExactAtPayload := targetExactAtPayloadOfEndpointBundleW806 payload
  exactInputs := exactInputs

/-- W806 closed-map ShortExact W663 bundle reduced to W803 terminal data. -/
noncomputable def closedMapTargetExactAtW803DataOfShortExactBundleW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := comparisonIso
  targetExactAtPayload := targetExactAtPayloadOfShortExactBundleW806 payload
  exactInputs := exactInputs

/-- W806 closed-embedding ShortExact W663 bundle reduced to W803 terminal data. -/
noncomputable def closedEmbeddingTargetExactAtW803DataOfShortExactBundleW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := comparisonIso
  targetExactAtPayload := targetExactAtPayloadOfShortExactBundleW806 payload
  exactInputs := exactInputs

/-- W806 closed-map endpoint bundle product evidence through the W803 route. -/
noncomputable def productEvidence_of_closedMapEndpointBundleReducedRouteW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    (closedMapTargetExactAtW803DataOfEndpointBundleW806
      comparisonIso payload exactInputs)

/-!
W806 closed-embedding endpoint bundle product evidence through the W803 route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingEndpointBundleReducedRouteW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableEndpointDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointBundleW806
      comparisonIso payload exactInputs)

/-- W806 closed-map ShortExact bundle product evidence through the W803 route. -/
noncomputable def productEvidence_of_closedMapShortExactBundleReducedRouteW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    (closedMapTargetExactAtW803DataOfShortExactBundleW806
      comparisonIso payload exactInputs)

/-!
W806 closed-embedding ShortExact bundle product evidence through the W803 route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingShortExactBundleReducedRouteW806
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (payload :
      MetrizableShortExactDirectLocalizationTriangulatedTargetExactAtPayloadW663)
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    (closedEmbeddingTargetExactAtW803DataOfShortExactBundleW806
      comparisonIso payload exactInputs)

/-- W806 input names for W663 bundle reduction to the W803 terminal route. -/
def targetExactAtW663BundleReductionInputNamesW806 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "W663 endpoint or ShortExact target-ExactAt payload bundle"]

theorem targetExactAtW663BundleReductionInputNamesW806_count :
    targetExactAtW663BundleReductionInputNamesW806.length = 3 :=
  rfl

structure MetrizableTargetExactAtW663BundleReductionStateW806 : Type where
  seed : String
  declarations : List String
  endpointReductionResult : String
  shortExactReductionResult : String
  droppedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtW663BundleReductionStateW806 :
    MetrizableTargetExactAtW663BundleReductionStateW806
    where
  seed := "w806-target-exactat-w663-bundle-reduction-route"
  declarations :=
    ["targetExactAtPayloadOfEndpointBundleW806",
      "targetExactAtPayloadOfShortExactBundleW806",
      "closedMapTargetExactAtW803DataOfEndpointBundleW806",
      "closedEmbeddingTargetExactAtW803DataOfEndpointBundleW806",
      "closedMapTargetExactAtW803DataOfShortExactBundleW806",
      "closedEmbeddingTargetExactAtW803DataOfShortExactBundleW806",
      "productEvidence_of_closedMapEndpointBundleReducedRouteW806",
      "productEvidence_of_closedEmbeddingEndpointBundleReducedRouteW806",
      "productEvidence_of_closedMapShortExactBundleReducedRouteW806",
      "productEvidence_of_closedEmbeddingShortExactBundleReducedRouteW806",
      "targetExactAtW663BundleReductionInputNamesW806",
      "targetExactAtW663BundleReductionInputNamesW806_count"]
  endpointReductionResult :=
    "proved: W663 endpoint target-ExactAt bundles feed the W803 terminal route"
  shortExactReductionResult :=
    "proved: W663 ShortExact target-ExactAt bundles feed the W803 terminal route"
  droppedInputs :=
    ["endpoint or ShortExact topology fields",
      "global homology field carried by the W663 bundle",
      "bounded homotopy localized right adjoint and direct localization fields"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target ExactAt realization data for exact-acyclic homotopy\
        objects"]
  productSuccessClaimed := false

theorem currentW806TargetExactAtW663BundleReduction_productSuccess :
    (have state := currentMetrizableTargetExactAtW663BundleReductionStateW806;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
