import LeanLCAExactChallenge.Derived.W735DirectLocalizationBoundaryRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroBoundarySourcePiZeroProductRoute

/-!
W879 feeds W735 boundary source-pi-zero limit stability and selected-row
WPP-op colimit stability into the W877 direct-localization boundary.

This avoids the closed-range product route: direct-localization only needs W735
branch data and WPP limit/colimit stability, so the W792 limit and selected-row
colimit adapters can supply those fields directly.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W879 closed-map branch data for direct localization through W735 boundary
source-pi-zero limit stability and selected-row WPP-op colimit stability.
-/
structure MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  selectedW461 : WppOpSelectedW461ProviderW781
  closedMapRows : WppOpClosedMapRowsProviderW781

/--
W879 closed-embedding branch data for direct localization through W735 boundary
source-pi-zero limit stability and selected-row WPP-op colimit stability.
-/
structure
    MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/--
W879 derives closed-map WPP limit stability from W735/W716 boundary data.
-/
theorem limitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData

/--
W879 derives closed-embedding WPP limit stability from W735/W716 boundary data.
-/
theorem limitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  limitStabilityOfBoundaryDataW792 data.exactInputs.boundaryData

/--
W879 derives closed-map WPP colimit stability from selected-W461 and row data.
-/
theorem colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapSelectedRowsW792
    data.selectedW461 data.closedMapRows

/--
W879 derives closed-embedding WPP colimit stability from selected-W461 and row
data.
-/
theorem colimitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedEmbeddingSelectedRowsW792
    data.selectedW461 data.closedEmbeddingRows

/-- W879 closed-map branch converted to W877 direct-localization boundary data. -/
noncomputable def closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 where
  exactInputs := data.exactInputs
  limitStability := limitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879 data
  colimitStability :=
    colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879 data

/--
W879 closed-embedding branch converted to W877 direct-localization boundary
data.
-/
noncomputable def
    closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877 where
  exactInputs := data.exactInputs
  limitStability :=
    limitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879 data
  colimitStability :=
    colimitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879 data

/-- W879 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapW735DirectBoundaryW877
    (closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/-- W879 closed-embedding branch as WPP finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedEmbeddingW735DirectBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/--
W879 closed-map branch as canonical direct-localization stable-boundary inputs.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapW735W877
    (closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/--
W879 closed-embedding branch as canonical direct-localization stable-boundary
inputs.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedEmbeddingW735W877
    (closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/-- W879 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def acceptedStableOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapW735DirectLocalizationBoundaryW877
    (closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/--
W879 closed-embedding branch passes the accepted stable direct-localization
gate.
-/
noncomputable def
    acceptedStableOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/-- W879 closed-map branch produces the bounded-derived package. -/
noncomputable def boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapW735DirectLocalizationBoundaryW877
    (closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/-- W879 closed-embedding branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/--
W879 closed-map branch produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfClosedMapBoundarySourcePiZeroSelectedRowsW879_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapW735DirectLocalizationBoundaryW877_ready
    (closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/--
W879 closed-embedding branch produces the ready four-projection stable
certificate.
-/
theorem stableCertificateOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_ready
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedEmbeddingW735DirectLocalizationBoundaryW877_ready
    (closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879 data)

/-!
W879's direct-localization boundary path leaves only W735 branch data plus the
selected-row WPP-op providers. W735 already carries the W716 boundary data used
for limit stability.
-/
def boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879 :
    List String :=
  ["W735 closed-map or closed-embedding branch data, including W716 boundary,\
      normalized, and source-triangulation data",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-map or closed-embedding provider for WPP-op SnakeInput"]

theorem
    boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879_count :
    boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879.length =
      3 :=
  rfl

/-- Current checked W879 state. -/
structure MetrizableBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryRouteStateW879 :
    Type where
  seed : String
  declarations : List String
  limitResult : String
  colimitResult : String
  directBoundaryResult : String
  stableBoundaryResult : String
  derivedOrEliminatedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W879 state for the boundary source-pi-zero plus selected-row
direct-localization boundary route.
-/
def currentMetrizableBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryRouteStateW879 :
    MetrizableBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryRouteStateW879
    where
  seed := "w879-boundary-source-pi-zero-selected-rows-direct-localization-boundary-route"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879",
      "MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879",
      "limitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "limitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "colimitStabilityOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879",
      "closedEmbeddingW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879",
      "transferInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "transferInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "directLocalizationBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "acceptedStableOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "acceptedStableOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedRowsW879",
      "boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879",
      "stableCertificateOfClosedMapBoundarySourcePiZeroSelectedRowsW879_ready",
      "stableCertificateOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_ready",
      "boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879",
      "boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879_count"]
  limitResult :=
    "proved: W735/W716 boundary data supplies WPP limit stability through\
      source-pi-zero"
  colimitResult :=
    "proved: selected-W461 plus row-aware data supplies WPP-op colimit stability"
  directBoundaryResult :=
    "proved: derived WPP stability turns W735 data into W877\
      direct-localization boundary data"
  stableBoundaryResult :=
    "proved: the resulting direct-localization boundary passes the accepted\
      stable boundary and bounded-derived gates"
  derivedOrEliminatedInputs :=
    ["WPP limit right open-map pure LCA certificate",
      "WPP limit right-surjectivity pure LCA certificate",
      "closed quotient-cover boundary as a separate right-open input",
      "Epi boundary as a separate right-surjectivity input",
      "WPP-op colimit left closed-embedding certificate",
      "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
      "W778/W792 closed-range comparison, exact-closure, target-homology-zero,\
        and endpoint-topology fields for this direct-localization boundary"]
  remainingInputs :=
    boundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputNamesW879
  productSuccessClaimed := false

theorem currentW879BoundarySourcePiZeroSelectedRowsDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryRouteStateW879;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
