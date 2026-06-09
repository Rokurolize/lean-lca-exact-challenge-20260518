import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundaryDirectLocalization
import LeanLCAExactChallenge.Derived.W735W732SelectedCochainStableExactAtRoute

/-!
W877 packages one W735 branch record as the direct-localization stable boundary.

The construction combines three already-proved projections:
* W735/W876 supplies direct bounded left calculus.
* W735/W722 supplies the W657 source-side direct-localization core.
* W735/W719 plus WPP limit/colimit stability supplies finite-shape transfer inputs.

This is a nonterminal bridge: it removes separate boundary inputs but does not
construct a concrete W735 branch or claim product success.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W877 closed-map branch data for the direct-localization boundary. -/
structure MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair

/-- W877 closed-embedding branch data for the direct-localization boundary. -/
structure MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair

/-- W877 derives W657 direct-localization data from closed-map W735 source data. -/
def directLocalizationOfClosedMapW735DirectBoundaryW877
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
    where
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData

/--
W877 derives W657 direct-localization data from closed-embedding W735 source data.
-/
def directLocalizationOfClosedEmbeddingW735DirectBoundaryW877
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657
    where
  sourcePretriangulated :=
    sourcePretriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  sourceTriangulated :=
    sourceTriangulated_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData
  triangleCompletion :=
    triangleCompletion_of_sourceTriangulationDataW722
      data.exactInputs.sourceTriangulationData

/-- W877 closed-map W719 data as finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedMapW735DirectBoundaryW877
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  data.exactInputs.normalizedFixedTargetData.toWalkingParallelPairFiniteShapeTransferInputs
    data.limitStability data.colimitStability

/-- W877 closed-embedding W719 data as finite-shape transfer inputs. -/
noncomputable def transferInputsOfClosedEmbeddingW735DirectBoundaryW877
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  data.exactInputs.normalizedFixedTargetData.toWalkingParallelPairFiniteShapeTransferInputs
    data.limitStability data.colimitStability

/--
W877 closed-map branch as canonical direct-localization stable-boundary inputs.
-/
noncomputable def directLocalizationBoundaryInputsOfClosedMapW735W877
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs
    where
  transferInputs := transferInputsOfClosedMapW735DirectBoundaryW877 data
  directLeftCalculus :=
    directBoundedLeftCalculusOfClosedMapW735W732SelectedCochainStableExactAtW876
      data.exactInputs
  directLocalization := directLocalizationOfClosedMapW735DirectBoundaryW877 data

/--
W877 closed-embedding branch as canonical direct-localization stable-boundary inputs.
-/
noncomputable def directLocalizationBoundaryInputsOfClosedEmbeddingW735W877
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs
    where
  transferInputs := transferInputsOfClosedEmbeddingW735DirectBoundaryW877 data
  directLeftCalculus :=
    directBoundedLeftCalculusOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
      data.exactInputs
  directLocalization :=
    directLocalizationOfClosedEmbeddingW735DirectBoundaryW877 data

/--
W877 closed-map branch passes the canonical accepted stable direct-localization
boundary gate.
-/
noncomputable def acceptedStableOfClosedMapW735DirectLocalizationBoundaryW877
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapW735W877 data)

/--
W877 closed-embedding branch passes the canonical accepted stable
direct-localization boundary gate.
-/
noncomputable def acceptedStableOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingW735W877 data)

/-- W877 closed-map branch produces the canonical bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapW735DirectLocalizationBoundaryW877
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedMapW735W877 data)

/-- W877 closed-embedding branch produces the canonical bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedEmbeddingW735DirectLocalizationBoundaryW877
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (directLocalizationBoundaryInputsOfClosedEmbeddingW735W877 data)

/--
W877 closed-map branch produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfClosedMapW735DirectLocalizationBoundaryW877_ready
    (data : MetrizableClosedMapW735DirectLocalizationBoundaryDataW877) :
    let inputs := directLocalizationBoundaryInputsOfClosedMapW735W877 data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
    (directLocalizationBoundaryInputsOfClosedMapW735W877 data)

/--
W877 closed-embedding branch produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfClosedEmbeddingW735DirectLocalizationBoundaryW877_ready
    (data : MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877) :
    let inputs := directLocalizationBoundaryInputsOfClosedEmbeddingW735W877 data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
    (directLocalizationBoundaryInputsOfClosedEmbeddingW735W877 data)

/-- W877 remaining external inputs after W735 packages the boundary fields. -/
def w735DirectLocalizationBoundaryRouteInputNamesW877 : List String :=
  ["W735 closed-map or closed-embedding branch data",
    "WPP limit stability for WalkingParallelPair",
    "WPP colimit stability for WalkingParallelPair"]

theorem w735DirectLocalizationBoundaryRouteInputNamesW877_count :
    w735DirectLocalizationBoundaryRouteInputNamesW877.length = 3 :=
  rfl

/-- Current checked W877 state. -/
structure MetrizableW735DirectLocalizationBoundaryRouteStateW877 :
    Type where
  seed : String
  declarations : List String
  boundaryInputResult : String
  stableBoundaryResult : String
  derivedOrEliminatedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableW735DirectLocalizationBoundaryRouteStateW877 :
    MetrizableW735DirectLocalizationBoundaryRouteStateW877
    where
  seed := "w877-w735-direct-localization-boundary-route"
  declarations :=
    ["MetrizableClosedMapW735DirectLocalizationBoundaryDataW877",
      "MetrizableClosedEmbeddingW735DirectLocalizationBoundaryDataW877",
      "directLocalizationOfClosedMapW735DirectBoundaryW877",
      "directLocalizationOfClosedEmbeddingW735DirectBoundaryW877",
      "transferInputsOfClosedMapW735DirectBoundaryW877",
      "transferInputsOfClosedEmbeddingW735DirectBoundaryW877",
      "directLocalizationBoundaryInputsOfClosedMapW735W877",
      "directLocalizationBoundaryInputsOfClosedEmbeddingW735W877",
      "acceptedStableOfClosedMapW735DirectLocalizationBoundaryW877",
      "acceptedStableOfClosedEmbeddingW735DirectLocalizationBoundaryW877",
      "boundedDerivedOfClosedMapW735DirectLocalizationBoundaryW877",
      "boundedDerivedOfClosedEmbeddingW735DirectLocalizationBoundaryW877",
      "stableCertificateOfClosedMapW735DirectLocalizationBoundaryW877_ready",
      "stableCertificateOfClosedEmbeddingW735DirectLocalizationBoundaryW877_ready",
      "w735DirectLocalizationBoundaryRouteInputNamesW877",
      "w735DirectLocalizationBoundaryRouteInputNamesW877_count"]
  boundaryInputResult :=
    "proved: W735 branch data plus WPP limit/colimit stability constructs the\
      canonical direct-localization boundary inputs"
  stableBoundaryResult :=
    "proved: the constructed direct-localization boundary inputs feed the\
      accepted stable boundary and bounded-derived package"
  derivedOrEliminatedInputs :=
    ["separate direct bounded left calculus input",
      "separate W657 direct-localization triangulated source core",
      "separate finite-shape transfer input once WPP stability is supplied"]
  remainingInputs := w735DirectLocalizationBoundaryRouteInputNamesW877
  productSuccessClaimed := false

theorem currentW877W735DirectLocalizationBoundaryRoute_productSuccess :
    currentMetrizableW735DirectLocalizationBoundaryRouteStateW877.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
