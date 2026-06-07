import LeanLCAExactChallenge.Derived.IsoClosureStrictRealizationTerminalProductRoute

/-!
W812 supplies the homology-detection evidence needed to collapse W651
iso-closure endpoints back to exact-acyclic homotopy objects. The homology
detection is derived from the W768 universal-comparison homology existence and
the W735 exact-input fields through W790/W696/W668.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W812 derives homology detection from closed-map W735 exact inputs. -/
def homologyDetectionOfClosedMapExactInputsW812
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
  Dbounded.homologyDetection_of_kernelCokernelConditionedTopology_w668
    (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
    (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
      (closedRangeEndpointTopologyOfClosedMapExactInputsW790 exactInputs))

/-- W812 derives homology detection from closed-embedding W735 exact inputs. -/
def homologyDetectionOfClosedEmbeddingExactInputsW812
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    ExactAcyclicHomologyDetectionInput MetrizableLCA.{0} :=
  Dbounded.homologyDetection_of_kernelCokernelConditionedTopology_w668
    (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
    (metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
      (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790 exactInputs))

/--
Homology detection collapses W651 iso-closure endpoints back to exact-acyclic
homotopy objects.
-/
theorem exactAcyclicHomotopyObjectOfIsoClosureHomologyDetectionW812
    (H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0})
    {K : HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)}
    (hK : exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} K) :
    exactAcyclicHomotopyObject MetrizableLCA.{0} K := by
  letI : (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms :=
    exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
      MetrizableLCA.{0}
      (exactAcyclicHomotopyEquivInvarianceInput_of_homologyDetection
        MetrizableLCA.{0} H)
  rcases hK with ⟨L, hL, e⟩
  exact (exactAcyclicHomotopyObject MetrizableLCA.{0}).prop_of_iso
    e.some.symm hL

/--
W812 derives W651 iso-closure realization from W809 strict realization under
homology detection.
-/
theorem isoClosureRealizationOfStrictRealizationHomologyDetectionW812
    (H : ExactAcyclicHomologyDetectionInput MetrizableLCA.{0})
    (realize :
      MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783) :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651 := by
  intro T hT h₁ h₃
  exact realize hT
    (exactAcyclicHomotopyObjectOfIsoClosureHomologyDetectionW812 H h₁)
    (exactAcyclicHomotopyObjectOfIsoClosureHomologyDetectionW812 H h₃)

/-- W812 closed-map data converted to W810 data through W735/W768 detection. -/
noncomputable def closedMapIsoClosureDataOfStrictRealizationW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedMapIsoClosureRealizationTerminalBranchDataW810
    where
  comparisonIso := data.comparisonIso
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedMapExactInputsW812 data.comparisonIso
        data.exactInputs)
      data.trianglehRealization
  exactInputs := data.exactInputs

/--
W812 closed-embedding data converted to W810 data through W735/W768 detection.
-/
noncomputable def closedEmbeddingIsoClosureDataOfStrictRealizationW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedEmbeddingIsoClosureRealizationTerminalBranchDataW810
    where
  comparisonIso := data.comparisonIso
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedEmbeddingExactInputsW812 data.comparisonIso
        data.exactInputs)
      data.trianglehRealization
  exactInputs := data.exactInputs

/-- W812 closed-map product evidence through detected W651 realization. -/
noncomputable def productEvidence_of_closedMapHomologyDetectedIsoClosureRouteW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedMapIsoClosureRealizationTerminalRouteW810
    (closedMapIsoClosureDataOfStrictRealizationW812 data)

/-- W812 closed-embedding product evidence through detected W651 realization. -/
noncomputable def
    productEvidence_of_closedEmbeddingHomologyDetectedIsoClosureRouteW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidence_of_closedEmbeddingIsoClosureRealizationTerminalRouteW810
    (closedEmbeddingIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-map homology-detected iso-closure data as W810/W809 stable data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedMapHomologyDetectedIsoClosureW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedMapIsoClosureRealizationTerminalW810
    (closedMapIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-embedding homology-detected iso-closure data as W810/W809 stable
data.
-/
noncomputable def
    directFiniteShapeStableDataOfClosedEmbeddingHomologyDetectedIsoClosureW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableKernelCokernelLeftRightComparisonDirectFiniteShapeStableDataW769 :=
  directFiniteShapeStableDataOfClosedEmbeddingIsoClosureRealizationTerminalW810
    (closedEmbeddingIsoClosureDataOfStrictRealizationW812 data)

/-! W812 closed-map homology-detected iso-closure data as boundary inputs. -/
noncomputable def stableBoundaryInputsOfClosedMapHomologyDetectedIsoClosureW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedMapIsoClosureRealizationTerminalW810
    (closedMapIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-embedding homology-detected iso-closure data as boundary inputs.
-/
noncomputable def
    stableBoundaryInputsOfClosedEmbeddingHomologyDetectedIsoClosureW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    Dbounded.MetrizableStableInstanceBoundaryInputs :=
  stableBoundaryInputsOfClosedEmbeddingIsoClosureRealizationTerminalW810
    (closedEmbeddingIsoClosureDataOfStrictRealizationW812 data)

/-! W812 closed-map homology-detected iso-closure data passes the boundary. -/
noncomputable def acceptedStableOfClosedMapHomologyDetectedIsoClosureW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapIsoClosureRealizationTerminalW810
    (closedMapIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-embedding homology-detected iso-closure data passes the boundary.
-/
noncomputable def acceptedStableOfClosedEmbeddingHomologyDetectedIsoClosureW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingIsoClosureRealizationTerminalW810
    (closedEmbeddingIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-map homology-detected iso-closure data produces the stable-boundary
package.
-/
noncomputable def
    boundedDerivedOfClosedMapHomologyDetectedIsoClosureStableBoundaryW812
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapIsoClosureRealizationTerminalStableBoundaryW810
    (closedMapIsoClosureDataOfStrictRealizationW812 data)

/-!
W812 closed-embedding homology-detected iso-closure data produces the
stable-boundary package.
-/
noncomputable def
    boundedDerivedOfClosedEmbeddingHomologyDetectedIsoClosureStableBoundaryW812
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingIsoClosureRealizationTerminalStableBoundaryW810
    (closedEmbeddingIsoClosureDataOfStrictRealizationW812 data)

def homologyDetectedIsoClosureTerminalProductRouteInputNamesW812 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding branch data",
    "exact-acyclic homotopy-object strict triangleh realization data"]

theorem homologyDetectedIsoClosureTerminalProductRouteInputNamesW812_count :
    homologyDetectedIsoClosureTerminalProductRouteInputNamesW812.length = 3 :=
  rfl

structure MetrizableHomologyDetectedIsoClosureTerminalRouteStateW812 :
    Type where
  seed : String
  declarations : List String
  homologyDetectionResult : String
  isoClosureReductionResult : String
  stableBoundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableHomologyDetectedIsoClosureTerminalRouteStateW812 :
    MetrizableHomologyDetectedIsoClosureTerminalRouteStateW812
    where
  seed := "w812-homology-detected-iso-closure-terminal-route"
  declarations :=
    ["homologyDetectionOfClosedMapExactInputsW812",
      "homologyDetectionOfClosedEmbeddingExactInputsW812",
      "exactAcyclicHomotopyObjectOfIsoClosureHomologyDetectionW812",
      "isoClosureRealizationOfStrictRealizationHomologyDetectionW812",
      "closedMapIsoClosureDataOfStrictRealizationW812",
      "closedEmbeddingIsoClosureDataOfStrictRealizationW812",
      "productEvidence_of_closedMapHomologyDetectedIsoClosureRouteW812",
      "productEvidence_of_closedEmbeddingHomologyDetectedIsoClosureRouteW812",
      "directFiniteShapeStableDataOfClosedMapHomologyDetectedIsoClosureW812",
      "directFiniteShapeStableDataOfClosedEmbeddingHomologyDetectedIsoClosureW812",
      "stableBoundaryInputsOfClosedMapHomologyDetectedIsoClosureW812",
      "stableBoundaryInputsOfClosedEmbeddingHomologyDetectedIsoClosureW812",
      "acceptedStableOfClosedMapHomologyDetectedIsoClosureW812",
      "acceptedStableOfClosedEmbeddingHomologyDetectedIsoClosureW812",
      "boundedDerivedOfClosedMapHomologyDetectedIsoClosureStableBoundaryW812",
      "boundedDerivedOfClosedEmbeddingHomologyDetectedIsoClosureStableBoundaryW812",
      "homologyDetectedIsoClosureTerminalProductRouteInputNamesW812",
      "homologyDetectedIsoClosureTerminalProductRouteInputNamesW812_count"]
  homologyDetectionResult :=
    "proved: W735 exact inputs plus W768 comparison homology existence supply\
      W668 homology detection for both branches"
  isoClosureReductionResult :=
    "proved: homology detection collapses W651 iso-closure endpoints, so W809\
      strict realization supplies W651 realization"
  stableBoundaryResult :=
    "proved: homology-detected W810 iso-closure data expose the\
      stable-boundary gate"
  replacedInputs :=
    ["W651 exact-acyclic homotopy-object iso-closure strict realization data"]
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 branch",
      "construct exact-acyclic homotopy-object strict triangleh realization\
        data"]
  productSuccessClaimed := false

theorem currentW812HomologyDetectedIsoClosureTerminalRoute_productSuccess :
    (have state :=
      currentMetrizableHomologyDetectedIsoClosureTerminalRouteStateW812;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
