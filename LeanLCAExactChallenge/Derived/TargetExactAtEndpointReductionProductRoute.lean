import LeanLCAExactChallenge.Derived.TargetExactAtRouteConsistencyProductRoute
import LeanLCAExactChallenge.Derived.TargetExactAtEndpointTargetIsoSelectedW461RowsProductRoute

/-!
W805 projects the older W785 target-ExactAt endpoint branch data into the W803
minimal terminal route, dropping endpoint, W461-row, and boundary fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W805 closed-map W785 endpoint data reduced to W803 terminal data. -/
noncomputable def closedMapTargetExactAtW803DataOfEndpointW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W805 closed-embedding W785 endpoint data reduced to W803 terminal data. -/
noncomputable def closedEmbeddingTargetExactAtW803DataOfEndpointW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := data.comparisonIso
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W805 closed-map product evidence through the reduced W803 endpoint route. -/
noncomputable def productEvidence_of_closedMapTargetExactAtEndpointReducedRouteW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapTargetExactAtW664TerminalRouteW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding product evidence through the reduced W803 endpoint route.
-/
noncomputable def
    productEvidence_of_closedEmbeddingTargetExactAtEndpointReducedRouteW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingTargetExactAtW664TerminalRouteW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-- W805 closed-map exact/stable evidence after endpoint-data reduction. -/
noncomputable def closedMapExactStableEvidenceOfTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedMapTargetExactAtEndpointReducedRouteW805
    data).exactStableEvidence

/-- W805 closed-embedding exact/stable evidence after endpoint-data reduction. -/
noncomputable def
    closedEmbeddingExactStableEvidenceOfTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableWppExactStableEvidenceW758 :=
  (productEvidence_of_closedEmbeddingTargetExactAtEndpointReducedRouteW805
    data).exactStableEvidence

/-- W805 closed-map stable certificate after endpoint-data reduction. -/
noncomputable def closedMapStableCertificateOfTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  (productEvidence_of_closedMapTargetExactAtEndpointReducedRouteW805
    data).kernelCokernelStableCertificate

/-- W805 closed-embedding stable certificate after endpoint-data reduction. -/
noncomputable def
    closedEmbeddingStableCertificateOfTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.StableFourProjectionCertificate MetrizableLCA.{0} :=
  (productEvidence_of_closedEmbeddingTargetExactAtEndpointReducedRouteW805
    data).kernelCokernelStableCertificate

/-- W805 closed-map stable certificate readiness after endpoint-data reduction. -/
theorem closedMapStableCertificateReadyOfTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    (closedMapStableCertificateOfTargetExactAtEndpointReducedW805 data).ready :=
  closedMapStableCertificateReadyOfTargetExactAtW664TerminalW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding stable certificate readiness after endpoint-data reduction.
-/
theorem closedEmbeddingStableCertificateReadyOfTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    (closedEmbeddingStableCertificateOfTargetExactAtEndpointReducedW805
      data).ready :=
  closedEmbeddingStableCertificateReadyOfTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-- W805 closed-map stable certificate acceptance after endpoint-data reduction. -/
theorem closedMapStableCertificateAcceptedOfTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedMapStableCertificateOfTargetExactAtEndpointReducedW805 data)) =
        true :=
  closedMapStableCertificateAcceptedOfTargetExactAtW664TerminalW804
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding stable certificate acceptance after endpoint-data
reduction.
-/
theorem closedEmbeddingStableCertificateAcceptedOfTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedEmbeddingStableCertificateOfTargetExactAtEndpointReducedW805
          data)) =
        true :=
  closedEmbeddingStableCertificateAcceptedOfTargetExactAtW664TerminalW804
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-map endpoint-reduced evidence as W803/W769 direct stable data.
-/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding endpoint-reduced evidence as W803/W769 direct stable data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-map endpoint-reduced evidence as stable-boundary inputs.
-/
noncomputable def stableBoundaryInputsOfClosedMapTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding endpoint-reduced evidence as stable-boundary inputs.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-map endpoint-reduced evidence passes the stable boundary.
-/
noncomputable def acceptedStableOfClosedMapTargetExactAtEndpointReducedW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetExactAtW664TerminalW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding endpoint-reduced evidence passes the stable boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetExactAtEndpointReducedW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetExactAtW664TerminalW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-map endpoint-reduced evidence produces the stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedMapTargetExactAtEndpointReducedStableBoundaryW805
    (data : MetrizableClosedMapTargetExactAtEndpointTargetIsoBranchDataW785) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetExactAtW664TerminalStableBoundaryW803
    (closedMapTargetExactAtW803DataOfEndpointW805 data)

/-!
W805 closed-embedding endpoint-reduced evidence produces the stable-boundary
package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetExactAtEndpointReducedStableBoundaryW805
    (data :
      MetrizableClosedEmbeddingTargetExactAtEndpointTargetIsoBranchDataW785) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetExactAtW664TerminalStableBoundaryW803
    (closedEmbeddingTargetExactAtW803DataOfEndpointW805 data)

/-- W805 input names after W785 endpoint data is reduced to the W803 route. -/
def targetExactAtEndpointReductionProductRouteInputNamesW805 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "target ExactAt realization data for exact-acyclic homotopy objects"]

theorem targetExactAtEndpointReductionProductRouteInputNamesW805_count :
    targetExactAtEndpointReductionProductRouteInputNamesW805.length = 3 :=
  rfl

structure MetrizableTargetExactAtEndpointReductionRouteStateW805 : Type where
  seed : String
  declarations : List String
  reductionResult : String
  terminalEvidenceResult : String
  stableBoundaryResult : String
  droppedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtEndpointReductionRouteStateW805 :
    MetrizableTargetExactAtEndpointReductionRouteStateW805
    where
  seed := "w805-target-exactat-endpoint-reduction-route"
  declarations :=
    ["closedMapTargetExactAtW803DataOfEndpointW805",
      "closedEmbeddingTargetExactAtW803DataOfEndpointW805",
      "productEvidence_of_closedMapTargetExactAtEndpointReducedRouteW805",
      "productEvidence_of_closedEmbeddingTargetExactAtEndpointReducedRouteW805",
      "closedMapExactStableEvidenceOfTargetExactAtEndpointReducedW805",
      "closedEmbeddingExactStableEvidenceOfTargetExactAtEndpointReducedW805",
      "closedMapStableCertificateOfTargetExactAtEndpointReducedW805",
      "closedEmbeddingStableCertificateOfTargetExactAtEndpointReducedW805",
      "closedMapStableCertificateReadyOfTargetExactAtEndpointReducedW805",
      "closedEmbeddingStableCertificateReadyOfTargetExactAtEndpointReducedW805",
      "closedMapStableCertificateAcceptedOfTargetExactAtEndpointReducedW805",
      "closedEmbeddingStableCertificateAcceptedOfTargetExactAtEndpointReducedW805",
      "directFiniteShapeStableDataOfClosedMapTargetExactAtEndpointReducedW805",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetExactAtEndpointReducedW805",
      "stableBoundaryInputsOfClosedMapTargetExactAtEndpointReducedW805",
      "stableBoundaryInputsOfClosedEmbeddingTargetExactAtEndpointReducedW805",
      "acceptedStableOfClosedMapTargetExactAtEndpointReducedW805",
      "acceptedStableOfClosedEmbeddingTargetExactAtEndpointReducedW805",
      "boundedDerivedOfClosedMapTargetExactAtEndpointReducedStableBoundaryW805",
      "boundedDerivedOfClosedEmbeddingTargetExactAtEndpointReducedStableBoundaryW805",
      "targetExactAtEndpointReductionProductRouteInputNamesW805",
      "targetExactAtEndpointReductionProductRouteInputNamesW805_count"]
  reductionResult :=
    "proved: W785 endpoint branch data projects to the W803 terminal route"
  terminalEvidenceResult :=
    "proved: reduced endpoint data exposes exact/stable evidence and certificates"
  stableBoundaryResult :=
    "proved: reduced endpoint data exposes the W803 stable-boundary gate"
  droppedInputs :=
    ["endpoint-strict topology data",
      "closed quotient-cover and Epi boundary data",
      "selected W461 and row-aware provider data",
      "W696 closed-range endpoint topology data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct target ExactAt realization data for exact-acyclic homotopy\
        objects"]
  productSuccessClaimed := false

theorem currentW805TargetExactAtEndpointReduction_productSuccess :
    (have state :=
      currentMetrizableTargetExactAtEndpointReductionRouteStateW805;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
