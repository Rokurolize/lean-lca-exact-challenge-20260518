import LeanLCAExactChallenge.Derived.LeftRightComparisonProductRoute
import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundary

/-!
W769 feeds the W670 direct finite-shape transfer-stable construction into the
W768 left-right comparison product route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W769 data surface replacing W768's explicit WPP transfer-stable semantic input
by the direct finite-shape data already consumed by W670.
-/
structure
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  directSource :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  localizedRightAdjoint :
    BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W769 repackages its comparison data in the W670 bundle shape. -/
noncomputable def
    directFiniteShapeKernelCokernelBundleOfLeftRightComparisonW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    MetrizableWppDirectFiniteShapeKernelCokernelConditionedDirectLocalizationBundleW670
    where
  exactClosed2 := data.exactClosed2
  directSource := data.directSource
  hasHomology := cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso
  kernelCokernelTopology := data.kernelCokernelTopologyData
  localizedRightAdjoint := data.localizedRightAdjoint
  directLocalization := data.directLocalization

/--
W769 obtains the WPP transfer-stable semantic inputs from W670 instead of
taking them as a primitive route input.
-/
noncomputable def transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    letI :
        (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
      data.exactClosed2
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768
        data.comparisonIso
        data.kernelCokernelTopologyData
        data.localizedRightAdjoint) := by
  simpa [directFiniteShapeKernelCokernelBundleOfLeftRightComparisonW769,
    metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768] using
    metrizableWppTransferStableSemanticInputs_of_directFiniteShapeKernelCokernelConditionedBundleW670
      (directFiniteShapeKernelCokernelBundleOfLeftRightComparisonW769 data)

/-- W769 ordinary stable semantic input for the direct finite-shape product route. -/
noncomputable def
    metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    Dbounded.MetrizableOrdinaryStableSemanticInput := by
  letI :
      (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    data.exactClosed2
  exact
    Dbounded.metrizableOrdinaryStableSemanticInputOfKernelCokernelConditionedWppTransfer_w669
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      data.kernelCokernelTopologyData
      data.localizedRightAdjoint
      (transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769 data)

/-- W769 direct finite-shape product route produces a ready stable certificate. -/
theorem stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
        data)).ready := by
  letI :
      (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    data.exactClosed2
  simpa
    [metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769] using
    Dbounded.stableCertificateOfKernelCokernelConditionedWppTransfer_w669_ready
      (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
      data.kernelCokernelTopologyData
      data.localizedRightAdjoint
      (transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769 data)

/--
W769 derives direct bounded left calculus from the left-right comparison route and the
kernel/cokernel-conditioned topology data.
-/
@[reducible] noncomputable def directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions := by
  letI :
      (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    data.exactClosed2
  exact Dbounded.leftCalculus_of_kernelCokernelConditionedTopology_w668
    (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
    data.kernelCokernelTopologyData
    data.localizedRightAdjoint

/-- W769 data as the explicit canonical stable-instance boundary input bundle. -/
noncomputable def stableBoundaryInputsOfLeftRightComparisonDirectFiniteShapeW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    Dbounded.MetrizableStableInstanceBoundaryInputs where
  directLeftCalculus :=
    Dbounded.directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769 data
  transferStableInputs := by
    letI :
        (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      Dbounded.directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769 data
    letI :
        (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
      data.exactClosed2
    simpa [Dbounded.directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769,
      transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769,
      metrizableLeftCalculusFieldsOfKernelCokernelLeftRightComparison_w768,
      Dbounded.metrizableLeftCalculusFieldsOfKernelCokernelConditionedTopology_w669] using
      Dbounded.transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769 data

/-- W769 direct finite-shape data passes the canonical accepted stable boundary gate. -/
noncomputable def
    acceptedStableBoundedDerivedInfinityCategoryOfLeftRightComparisonDirectFiniteShapeW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.MetrizableStableInstanceBoundaryInputs.acceptedStable
    (Dbounded.stableBoundaryInputsOfLeftRightComparisonDirectFiniteShapeW769 data)

/-- W769 direct finite-shape data produces the canonical stable-boundary package. -/
noncomputable def
    boundedDerivedInfinityCategoryOfLeftRightComparisonDirectFiniteShapeStableBoundaryW769
    (data :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
    (Dbounded.stableBoundaryInputsOfLeftRightComparisonDirectFiniteShapeW769 data)

/-- W769 closed-map branch: W762 exact/WPP evidence plus W670-derived stable evidence. -/
noncomputable def
    productEvidence_of_closedMapLeftRightComparisonDirectFiniteShapeRouteW769
    (exactInputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedMapLeftRightComparisonConcreteLeavesW762
      stableData.comparisonIso exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready
      stableData
  kernelCokernelStableAccepted := rfl

/--
W769 closed-embedding branch: W762 exact/WPP evidence plus W670-derived stable
evidence.
-/
noncomputable def
    productEvidence_of_closedEmbeddingLeftRightComparisonDirectFiniteShapeRouteW769
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (stableData :
      MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769) :
    MetrizableWppKernelCokernelProductEvidenceW767
    where
  exactStableEvidence :=
    exactStableEvidence_of_closedEmbeddingLeftRightComparisonConcreteLeavesW762
      stableData.comparisonIso exactInputs
  kernelCokernelStableCertificate :=
    Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfLeftRightComparisonDirectFiniteShapeProductRoute_w769
        stableData)
  kernelCokernelStableReady :=
    stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready
      stableData
  kernelCokernelStableAccepted := rfl

/-- W769 input names after W670 supplies transfer-stable semantic inputs. -/
def leftRightComparisonDirectFiniteShapeProductRouteInputNamesW769 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding exact/WPP branch data",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "bounded homotopy localized right adjoint plus unit membership",
    "direct localization triangulated source data"]

theorem leftRightComparisonDirectFiniteShapeProductRouteInputNamesW769_count :
    leftRightComparisonDirectFiniteShapeProductRouteInputNamesW769.length =
      7 :=
  rfl

/--
W769 source inputs needed only for the canonical stable boundary, excluding the separate
closed-map or closed-embedding exact/WPP branch consumed by the product-evidence route.
-/
def leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "direct finite-shape WPP source data",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "bounded homotopy localized right adjoint plus unit membership",
    "direct localization triangulated source data"]

theorem leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769_count :
    leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769.length =
      6 :=
  rfl

/-- Current checked W769 state. -/
structure MetrizableLeftRightComparisonDirectFiniteShapeProductRouteStateW769 :
    Type where
  seed : String
  declarations : List String
  transferStableInputResult : String
  stableCertificateResult : String
  exactWppResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W769 state for the direct finite-shape product route. -/
def currentMetrizableLeftRightComparisonDirectFiniteShapeProductRouteSupportStateW769 :
    MetrizableLeftRightComparisonDirectFiniteShapeProductRouteStateW769
    where
  seed := "w769-left-right-comparison-direct-finite-shape-product-route"
  declarations :=
    ["MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769",
      "directFiniteShapeKernelCokernelBundleOfLeftRightComparisonW769",
      "transferStableInputsOfLeftRightComparisonDirectFiniteShapeW769",
      "metrizableOrdinaryStableSemanticInputOfLeftRightComparison\
        DirectFiniteShapeProductRoute_w769",
      "stableCertificateOfLeftRightComparisonDirectFiniteShapeProductRoute_w769_ready",
      "directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769",
      "stableBoundaryInputsOfLeftRightComparisonDirectFiniteShapeW769",
      "acceptedStableBoundedDerivedInfinityCategoryOfLeftRightComparison\
        DirectFiniteShapeW769",
      "boundedDerivedInfinityCategoryOfLeftRightComparisonDirectFiniteShape\
        StableBoundaryW769",
      "productEvidence_of_closedMapLeftRightComparisonDirectFiniteShapeRouteW769",
      "productEvidence_of_closedEmbeddingLeftRightComparisonDirectFiniteShapeRouteW769",
      "leftRightComparisonDirectFiniteShapeProductRouteInputNamesW769",
      "leftRightComparisonDirectFiniteShapeProductRouteInputNamesW769_count",
      "leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769",
      "leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769_count"]
  transferStableInputResult :=
    "proved: W670 direct finite-shape data supplies the W669/W768 transfer-stable semantic inputs"
  stableCertificateResult :=
    "proved: the W769 route produces a ready W528 stable certificate and \
      accepted stable boundary gate"
  exactWppResult :=
    "proved: W762 exact/WPP evidence still combines with the W769 stable certificate"
  replacedInputs :=
    ["primitive MetrizableWalkingParallelPairTransferStableSemanticInputs argument"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct direct finite-shape WPP source data",
      "construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "construct bounded homotopy localized right adjoint plus unit membership",
      "construct direct localization triangulated source data"]
  productSuccessClaimed := false

theorem currentMetrizableLeftRightComparisonDirectFiniteShapeProductRouteStateW769_productSuccess :
    (let state :=
      currentMetrizableLeftRightComparisonDirectFiniteShapeProductRouteSupportStateW769;
    state.productSuccessClaimed) = false :=
  rfl

section Checks

#check Dbounded.directLeftCalculusOfLeftRightComparisonDirectFiniteShapeW769
#check Dbounded.stableBoundaryInputsOfLeftRightComparisonDirectFiniteShapeW769
#check
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfLeftRightComparisonDirectFiniteShapeW769
#check
  Dbounded.boundedDerivedInfinityCategoryOfLeftRightComparisonDirectFiniteShapeStableBoundaryW769
#check Dbounded.leftRightComparisonDirectFiniteShapeStableBoundaryInputNamesW769_count
#check
  Dbounded.currentMetrizableLeftRightComparisonDirectFiniteShapeProductRouteStateW769_productSuccess

end Checks

end Dbounded

end LeanLCAExactChallenge
