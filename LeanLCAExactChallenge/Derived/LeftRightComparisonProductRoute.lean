import LeanLCAExactChallenge.Derived.KernelCokernelProductRoute

/-!
W768 feeds the W736 left-right comparison isomorphism route into the W767
kernel-cokernel product route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W768 turns the W736 universal left-right comparison isomorphism into cochain
homology for every MetrizableLCA complex and degree.
-/
theorem cochainHasHomology_of_leftRightComparisonIsoW768
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i := by
  intro K i
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    categoryWithHomology_of_metrizableLeftRightComparisonIsoW736
      comparisonIso
  infer_instance

/--
W768 kernel/cokernel-conditioned left-calculus fields with the W736 comparison
isomorphism as the homology input.
-/
noncomputable def metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (I : MetrizableExactAtKernelCokernelConditionedTopologyInputs)
    (R : BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}) :
    Dbounded.MetrizableLeftCalculusSemanticFields :=
  Dbounded.metrizableLeftCalculusFieldsOfKernelCokernelConditionedTopology_w669
    (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso) I R

/--
W768 data surface for W767 after replacing the direct `CategoryWithHomology`
input by W736 comparison-isomorphism data.
-/
structure MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂] :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721
  transferStableInputs :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768
        comparisonIso
        kernelCokernelTopologyData
        (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
          localizedRightAdjointData))

/-- W768 converts the comparison-isomorphism data surface to ordinary stable input. -/
noncomputable def
    metrizableOrdinaryStableSemanticInputOfKernelCokernelLeftRightComparisonProductRoute_w768
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (data : MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  Dbounded.metrizableOrdinaryStableSemanticInputOfKernelCokernelConditionedWppTransfer_w669
    (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
    data.kernelCokernelTopologyData
    (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.localizedRightAdjointData)
    data.transferStableInputs

/-- W768 comparison-isomorphism product route produces a ready stable certificate. -/
theorem stableCertificateOfKernelCokernelLeftRightComparisonProductRoute_w768_ready
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (data : MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelLeftRightComparisonProductRoute_w768
        data)).ready := by
  exact
    Dbounded.stableCertificateOfKernelCokernelConditionedWppTransfer_w669_ready
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      data.kernelCokernelTopologyData
      (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
        data.localizedRightAdjointData)
      data.transferStableInputs

/-- W768 closed-map branch: W762 exact/WPP evidence plus W768 stable evidence. -/
noncomputable def
    productEvidence_of_closedMapLeftRightComparisonKernelCokernelRouteW768
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (exactInputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData : MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedMapLeftRightComparisonConcreteLeavesW762
      stableData.comparisonIso exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelLeftRightComparisonProductRoute_w768
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfKernelCokernelLeftRightComparisonProductRoute_w768_ready
      stableData
  kernelCokernelStableAccepted := rfl

/-- W768 closed-embedding branch: W762 exact/WPP evidence plus W768 stable evidence. -/
noncomputable def
    productEvidence_of_closedEmbeddingLeftRightComparisonKernelCokernelRouteW768
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData : MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedEmbeddingLeftRightComparisonConcreteLeavesW762
      stableData.comparisonIso exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelLeftRightComparisonProductRoute_w768
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfKernelCokernelLeftRightComparisonProductRoute_w768_ready
      stableData
  kernelCokernelStableAccepted := rfl

/-- W768 input names after replacing `CategoryWithHomology` by W736 comparison data. -/
def kernelCokernelLeftRightComparisonProductRouteInputNamesW768 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding exact/WPP branch data",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "W721 localized-right-adjoint data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "MetrizableWalkingParallelPairTransferStableSemanticInputs"]

theorem kernelCokernelLeftRightComparisonProductRouteInputNamesW768_count :
    kernelCokernelLeftRightComparisonProductRouteInputNamesW768.length =
      6 :=
  rfl

/-- Current checked W768 state. -/
structure MetrizableKernelCokernelLeftRightComparisonProductRouteStateW768 :
    Type where
  seed : String
  declarations : List String
  comparisonHomologyResult : String
  exactWppResult : String
  stableCertificateResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W768 state for the comparison-isomorphism product route. -/
def currentMetrizableKernelCokernelLeftRightComparisonProductRouteSupportStateW768 :
    MetrizableKernelCokernelLeftRightComparisonProductRouteStateW768
    where
  seed := "w768-left-right-comparison-kernel-cokernel-product-route"
  declarations :=
    ["cochainHasHomology_of_leftRightComparisonIsoW768",
      "metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768",
      "MetrizableKernelCokernelLeftRightComparisonWppTransferDataW768",
      "metrizableOrdinaryStableSemanticInputOfKernelCokernelLeftRightComparisonProductRoute_w768",
      "stableCertificateOfKernelCokernelLeftRightComparisonProductRoute_w768_ready",
      "productEvidence_of_closedMapLeftRightComparisonKernelCokernelRouteW768",
      "productEvidence_of_closedEmbeddingLeftRightComparisonKernelCokernelRouteW768",
      "kernelCokernelLeftRightComparisonProductRouteInputNamesW768",
      "kernelCokernelLeftRightComparisonProductRouteInputNamesW768_count"]
  comparisonHomologyResult :=
    "proved: W736 comparison-isomorphism data supplies CategoryWithHomology-derived cochain homology"
  exactWppResult :=
    "proved: W762 route data supplies WPP exact/stable evidence"
  stableCertificateResult :=
    "proved: W768 feeds W736 comparison data into the W669 kernel-cokernel stable certificate"
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP transfer stable semantic inputs"]
  productSuccessClaimed := false

theorem
    currentMetrizableKernelCokernelLeftRightComparisonProductRouteStateW768_productSuccess :
    currentMetrizableKernelCokernelLeftRightComparisonProductRouteSupportStateW768.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
