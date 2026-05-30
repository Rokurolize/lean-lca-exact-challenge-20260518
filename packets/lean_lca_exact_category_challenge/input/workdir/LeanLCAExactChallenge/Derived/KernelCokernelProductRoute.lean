import LeanLCAExactChallenge.Derived.CategoryHomologyStableRoute

/-!
W767 combines the W765 exact/WPP route with the W766 kernel-cokernel stable route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W767 projects the W721 localized-right-adjoint bundle into the W766 input shape. -/
def boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
    (data : MetrizableWppLocalizedRightAdjointDataProviderW721) :
    BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}
    where
  rightAdjoint := data.boundedHomotopyLocalizedRightAdjoint
  adjunction := data.boundedHomotopyLocalizedAdjunction
  unit_mem := data.boundedHomotopyLocalizedUnitMem

/--
W767 data surface for W766 after reusing the existing W721 localized-right-adjoint
provider and making the WPP-transfer stable input explicit.
-/
structure MetrizableKernelCokernelCategoryHomologyWppTransferDataW767
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂] :
    Type 2 where
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721
  transferStableInputs :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766
        kernelCokernelTopologyData
        (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
          localizedRightAdjointData))

/-- W767 converts the data surface to the W766 ordinary stable input. -/
noncomputable def
    metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyProductRoute_w767
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (data : MetrizableKernelCokernelCategoryHomologyWppTransferDataW767) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyWppTransfer_w766
    data.kernelCokernelTopologyData
    (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.localizedRightAdjointData)
    data.transferStableInputs

/-- W767 kernel-cokernel category-homology product route produces a ready certificate. -/
theorem stableCertificateOfKernelCokernelCategoryHomologyProductRoute_w767_ready
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (data : MetrizableKernelCokernelCategoryHomologyWppTransferDataW767) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyProductRoute_w767
        data)).ready := by
  exact
    stableCertificateOfKernelCokernelCategoryHomologyWppTransfer_w766_ready
      data.kernelCokernelTopologyData
      (boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
        data.localizedRightAdjointData)
      data.transferStableInputs

/-- W767 packages WPP exactness together with the W766-style stable certificate. -/
structure MetrizableWppKernelCokernelProductEvidenceW767 : Type 2 where
  exactStableEvidence : MetrizableWppExactStableEvidenceW758
  kernelCokernelStableCertificate :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0}
  kernelCokernelStableReady : kernelCokernelStableCertificate.ready
  kernelCokernelStableAccepted :
    Dbounded.StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate kernelCokernelStableCertificate) =
        true

/-- W767 closed-map branch: W765 exact/WPP evidence plus W766 stable evidence. -/
noncomputable def
    productEvidence_of_closedMapCategoryHomologyKernelCokernelRouteW767
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (exactInputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData : MetrizableKernelCokernelCategoryHomologyWppTransferDataW767) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedMapCategoryHomologyInstanceRouteDataW765 exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyProductRoute_w767
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfKernelCokernelCategoryHomologyProductRoute_w767_ready stableData
  kernelCokernelStableAccepted := rfl

/-- W767 closed-embedding branch: W765 exact/WPP evidence plus W766 stable evidence. -/
noncomputable def
    productEvidence_of_closedEmbeddingCategoryHomologyKernelCokernelRouteW767
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData : MetrizableKernelCokernelCategoryHomologyWppTransferDataW767) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedEmbeddingCategoryHomologyInstanceRouteDataW765
      exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyProductRoute_w767
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfKernelCokernelCategoryHomologyProductRoute_w767_ready stableData
  kernelCokernelStableAccepted := rfl

/-- W767 input names after W721 and W766 integration. -/
def kernelCokernelCategoryHomologyProductRouteInputNamesW767 : List String :=
  ["CategoryWithHomology MetrizableLCA",
    "W735 closed-map or closed-embedding exact/WPP branch data",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "W721 localized-right-adjoint data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "MetrizableWalkingParallelPairTransferStableSemanticInputs"]

theorem kernelCokernelCategoryHomologyProductRouteInputNamesW767_count :
    kernelCokernelCategoryHomologyProductRouteInputNamesW767.length =
      6 :=
  rfl

/-- Current checked W767 state. -/
structure MetrizableKernelCokernelCategoryHomologyProductRouteStateW767 :
    Type where
  seed : String
  declarations : List String
  exactWppResult : String
  stableCertificateResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W767 state for the product-route integration. -/
def currentMetrizableKernelCokernelCategoryHomologyProductRouteSupportStateW767 :
    MetrizableKernelCokernelCategoryHomologyProductRouteStateW767
    where
  seed := "w767-kernel-cokernel-category-homology-product-route"
  declarations :=
    ["boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767",
      "MetrizableKernelCokernelCategoryHomologyWppTransferDataW767",
      "metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyProductRoute_w767",
      "stableCertificateOfKernelCokernelCategoryHomologyProductRoute_w767_ready",
      "MetrizableWppKernelCokernelProductEvidenceW767",
      "productEvidence_of_closedMapCategoryHomologyKernelCokernelRouteW767",
      "productEvidence_of_closedEmbeddingCategoryHomologyKernelCokernelRouteW767",
      "kernelCokernelCategoryHomologyProductRouteInputNamesW767",
      "kernelCokernelCategoryHomologyProductRouteInputNamesW767_count"]
  exactWppResult :=
    "proved: W765 route data supplies WPP exact/stable evidence"
  stableCertificateResult :=
    "proved: W721 data feeds the W766 kernel-cokernel stable certificate"
  remainingInputs :=
    ["construct CategoryWithHomology MetrizableLCA",
      "construct concrete values for one W735 branch",
      "construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct WPP transfer stable semantic inputs"]
  productSuccessClaimed := false

theorem currentMetrizableKernelCokernelCategoryHomologyProductRouteStateW767_productSuccess :
    (let state :=
      currentMetrizableKernelCokernelCategoryHomologyProductRouteSupportStateW767;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
