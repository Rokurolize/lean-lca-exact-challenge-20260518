import LeanLCAExactChallenge.Derived.TargetHomologyZeroTerminalEvidenceProductRoute

/-!
W799 makes the W798 target homology-zero terminal route depend directly on the
underlying W664 target homology-zero payload.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W799 closed-map branch data with the W664 payload made explicit. -/
structure MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13TargetHomologyZeroPayloadW664
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/-- W799 closed-embedding branch data with the W664 payload made explicit. -/
structure MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799 :
    Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13TargetHomologyZeroPayloadW664
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

noncomputable def closedMapComparisonHomologyDataOfW664PayloadW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableClosedMapTargetHomologyZeroComparisonHomologyBranchDataW794
    where
  comparisonIso := data.comparisonIso
  targetHomologyZeroPayload := data.targetHomologyZeroPayload
  exactInputs := data.exactInputs

noncomputable def closedEmbeddingComparisonHomologyDataOfW664PayloadW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableClosedEmbeddingTargetHomologyZeroComparisonHomologyBranchDataW794
    where
  comparisonIso := data.comparisonIso
  targetHomologyZeroPayload := data.targetHomologyZeroPayload
  exactInputs := data.exactInputs

noncomputable def productEvidence_of_closedMapW664TerminalRouteW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapComparisonHomologyRouteW794
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

noncomputable def productEvidence_of_closedEmbeddingW664TerminalRouteW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingComparisonHomologyRouteW794
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

noncomputable def closedMapExactStableEvidenceOfW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableWppExactStableEvidenceW758 :=
  closedMapExactStableEvidenceOfTargetHomologyZeroTerminalW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

noncomputable def closedEmbeddingExactStableEvidenceOfW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableWppExactStableEvidenceW758 :=
  closedEmbeddingExactStableEvidenceOfTargetHomologyZeroTerminalW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

theorem closedMapStableCertificateReadyOfW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    (closedMapStableCertificateOfTargetHomologyZeroTerminalW798
      (closedMapComparisonHomologyDataOfW664PayloadW799 data)).ready :=
  closedMapStableCertificateReadyOfTargetHomologyZeroTerminalW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

theorem closedEmbeddingStableCertificateReadyOfW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    (closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798
      (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)).ready :=
  closedEmbeddingStableCertificateReadyOfTargetHomologyZeroTerminalW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

theorem closedMapStableCertificateAcceptedOfW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedMapStableCertificateOfTargetHomologyZeroTerminalW798
          (closedMapComparisonHomologyDataOfW664PayloadW799 data))) =
        true :=
  closedMapStableCertificateAcceptedOfTargetHomologyZeroTerminalW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

theorem closedEmbeddingStableCertificateAcceptedOfW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    StableRouteAttempt.accepted (C := MetrizableLCA.{0})
      (.fullCertificate
        (closedEmbeddingStableCertificateOfTargetHomologyZeroTerminalW798
          (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data))) =
        true :=
  closedEmbeddingStableCertificateAcceptedOfTargetHomologyZeroTerminalW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

/-- W799 closed-map W664-explicit terminal evidence as W769 stable data. -/
noncomputable def directFiniteShapeStableDataOfClosedMapTargetHomologyZeroW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

/-- W799 closed-embedding W664-explicit terminal evidence as W769 stable data. -/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

/-- W799 closed-map W664-explicit terminal evidence as stable-boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapTargetHomologyZeroW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

/--
W799 closed-embedding W664-explicit terminal evidence as stable-boundary
inputs.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

/-- W799 closed-map W664-explicit terminal evidence passes the stable boundary. -/
noncomputable def acceptedStableOfClosedMapTargetHomologyZeroW664TerminalW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapTargetHomologyZeroTerminalEvidenceW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

/--
W799 closed-embedding W664-explicit terminal evidence passes the stable
boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingTargetHomologyZeroW664TerminalW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

/-- W799 closed-map W664-explicit terminal evidence produces the stable-boundary package. -/
noncomputable def
    boundedDerivedOfClosedMapTargetHomologyZeroW664TerminalStableBoundaryW799
    (data : MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetHomologyZeroTerminalEvidenceStableBoundaryW798
    (closedMapComparisonHomologyDataOfW664PayloadW799 data)

/--
W799 closed-embedding W664-explicit terminal evidence produces the
stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingTargetHomologyZeroW664TerminalStableBoundaryW799
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetHomologyZeroTerminalEvidenceStableBoundaryW798
    (closedEmbeddingComparisonHomologyDataOfW664PayloadW799 data)

def targetHomologyZeroW664TerminalProductRouteInputNamesW799 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "W664 target homology-zero payload indexed by W768-derived homology\
      existence"]

theorem targetHomologyZeroW664TerminalProductRouteInputNamesW799_count :
    targetHomologyZeroW664TerminalProductRouteInputNamesW799.length = 3 :=
  rfl

structure MetrizableTargetHomologyZeroW664TerminalRouteStateW799 : Type where
  seed : String
  declarations : List String
  branchDataResult : String
  terminalEvidenceResult : String
  stableBoundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetHomologyZeroW664TerminalRouteStateW799 :
    MetrizableTargetHomologyZeroW664TerminalRouteStateW799
    where
  seed := "w799-target-homology-zero-w664-terminal-route"
  declarations :=
    ["MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799",
      "MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799",
      "closedMapComparisonHomologyDataOfW664PayloadW799",
      "closedEmbeddingComparisonHomologyDataOfW664PayloadW799",
      "productEvidence_of_closedMapW664TerminalRouteW799",
      "productEvidence_of_closedEmbeddingW664TerminalRouteW799",
      "closedMapExactStableEvidenceOfW664TerminalW799",
      "closedEmbeddingExactStableEvidenceOfW664TerminalW799",
      "closedMapStableCertificateReadyOfW664TerminalW799",
      "closedEmbeddingStableCertificateReadyOfW664TerminalW799",
      "closedMapStableCertificateAcceptedOfW664TerminalW799",
      "closedEmbeddingStableCertificateAcceptedOfW664TerminalW799",
      "directFiniteShapeStableDataOfClosedMapTargetHomologyZeroW664TerminalW799",
      "directFiniteShapeStableDataOfClosedEmbeddingTargetHomologyZeroW664TerminalW799",
      "stableBoundaryInputsOfClosedMapTargetHomologyZeroW664TerminalW799",
      "stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroW664TerminalW799",
      "acceptedStableOfClosedMapTargetHomologyZeroW664TerminalW799",
      "acceptedStableOfClosedEmbeddingTargetHomologyZeroW664TerminalW799",
      "boundedDerivedOfClosedMapTargetHomologyZeroW664TerminalStableBoundaryW799",
      "boundedDerivedOfClosedEmbeddingTargetHomologyZeroW664TerminalStableBoundaryW799",
      "targetHomologyZeroW664TerminalProductRouteInputNamesW799",
      "targetHomologyZeroW664TerminalProductRouteInputNamesW799_count"]
  branchDataResult :=
    "proved: W664 target homology-zero payload data converts to W794 data"
  terminalEvidenceResult :=
    "proved: W664-explicit data feed W798 terminal exact/stable evidence"
  stableBoundaryResult :=
    "proved: W799 W664 terminal branches expose the W798/W794/W774/W773/W769\
      canonical stable-boundary gate"
  replacedInputs :=
    ["target homology-zero realization data alias stack from W798",
      "separate W798 terminal-evidence stable-boundary branch input"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct the W664 target homology-zero payload indexed by the\
        comparison-derived homology existence"]
  productSuccessClaimed := false

theorem currentW799TargetHomologyZeroW664TerminalRoute_productSuccess :
    (have state :=
      currentMetrizableTargetHomologyZeroW664TerminalRouteStateW799;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
