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
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpRepresentativeImageSelectedProviderClosedRangeOnlyProjectionV370SupportW524

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
W1620 closed-map branch data where the row-aware closed-map provider is derived
from closed-embedding rows by W580 row dominance.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  selectedW461 : WppOpSelectedW461ProviderW781
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/--
W1621 closed-map branch data where the selected-W461 provider is derived from
the W735 relation and target-surjective compact fields.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  closedEmbeddingRows : WppOpClosedEmbeddingRowsProviderW781

/--
W1622 closed-map branch data where the row-aware closed-embedding provider is
derived from a W718 diagram-component closed-embedding provider.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  globalClosedEmbeddingComponents :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718

/--
W1621 derives the compact-target relation provider from W735's bundled W717
relation data and W715 target-surjective compact data.
-/
def compactTargetProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    ClosedNatTransOrdinaryCompactTargetRelationProviderW517 :=
  compactTargetProvider_of_pullback_targetSurjective_compactCodomain_w601
    (relationPullbackProvider_of_relationDataW717 data.exactInputs.relationData)
    (targetDifferenceSurjectiveProvider_of_targetOnlyW713
      (targetDifferenceSurjectiveForTargetProvider_of_surjectiveCompactW715
        data.exactInputs.targetSurjectiveCompactForTargetProvider))
    (targetCodomainCompactSpaceProvider_of_surjectiveCompactW715
      data.exactInputs.targetSurjectiveCompactForTargetProvider)

/--
W1621 derives W1620's selected-W461 input from W735's relation/target data via
the W601 compact-target provider and W524 selected-W461 bridge.
-/
noncomputable def selectedW461ProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    WppOpSelectedW461ProviderW781 :=
  selectedW461Provider_of_compactTargetRelation_w524
    (compactTargetProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621 data)

/--
W1622 assembles a W525 closed-embedding provider from the W718 bundled
diagram-only component fields, using the W714-to-W711 adapters.
-/
def
    closedEmbeddingProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    WppOpSelectedDifferenceClosedMapClosedRangeOnlyV370SupportW525.ComponentwiseClosedEmbeddingProviderW525 :=
  componentwiseClosedEmbeddingProvider_of_explicitComponentFieldsW711
    (selectedDifferenceClosedEmbeddingPi1Field_of_diagramFieldW714
      (selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        data.globalClosedEmbeddingComponents))
    (selectedDifferenceClosedEmbeddingPi2Field_of_diagramFieldW714
      (selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        data.globalClosedEmbeddingComponents))
    (selectedDifferenceClosedEmbeddingPi3Field_of_diagramFieldW714
      (selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        data.globalClosedEmbeddingComponents))

/--
W1622 derives W1621's row-aware closed-embedding input through W581 from the
W525 provider assembled out of W718 diagram components.
-/
def
    closedEmbeddingRowsProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    WppOpClosedEmbeddingRowsProviderW781 :=
  componentwiseClosedEmbeddingRowsProvider_of_globalClosedEmbeddingProvider_w581
    (closedEmbeddingProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
      data)

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

/--
W1620 projects closed-map data with closed-embedding rows to the W879 closed-map
surface, using W580 to derive the closed-map rows.
-/
def closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879
    where
  exactInputs := data.exactInputs
  selectedW461 := data.selectedW461
  closedMapRows :=
    componentwiseClosedMapRowsProvider_of_closedEmbeddingRows_w580
      data.closedEmbeddingRows

/--
W1620 closed-map WPP colimit stability, with closed-map row data supplied by
closed-embedding row dominance.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/--
W1621 projects the two-input target-data/closed-embedding-row surface to W1620
by deriving selected-W461 from the W735 relation and target fields.
-/
noncomputable def closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620
    where
  exactInputs := data.exactInputs
  selectedW461 :=
    selectedW461ProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621 data
  closedEmbeddingRows := data.closedEmbeddingRows

/--
W1622 projects the target-data/global-closed-embedding-component surface to
W1621 by deriving row-aware closed-embedding rows from W718 through
W714/W711/W581.
-/
noncomputable def
    closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621
    where
  exactInputs := data.exactInputs
  closedEmbeddingRows :=
    closedEmbeddingRowsProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
      data

/--
W1621 closed-map WPP colimit stability, with selected-W461 and closed-map rows
both theorem-derived from W735 target/relation data and closed-embedding rows.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/--
W1622 closed-map WPP colimit stability, with selected-W461, row-aware
closed-embedding rows, and closed-map rows all theorem-derived from W735 target
data and W718 diagram components.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

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

/-- W1620 closed-map branch converted to W877 direct-localization boundary data. -/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/-- W1620 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/-!
W1620 exposes a closed-map direct-localization branch whose row-aware closed-map
input is derived from closed-embedding rows, rather than supplied separately.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/-- W1620 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/-- W1620 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/--
W1620 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroSelectedRowsW879_ready
    (closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
      data)

/--
W1621 closed-map branch converted to W877 direct-localization boundary data.
-/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/--
W1622 closed-map branch converted to W877 direct-localization boundary data.
-/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

/-- W1621 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/-- W1622 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

/-!
W1621 exposes a closed-map direct-localization branch whose selected-W461 and
closed-map row inputs are both derived instead of supplied separately.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/-!
W1622 exposes a closed-map direct-localization branch whose row-aware
closed-embedding input is derived from W718 diagram components.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

/- W1621 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/- W1622 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

/- W1621 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/- W1622 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

/--
W1621 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_ready
    (closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
      data)

/--
W1622 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_ready
    (closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
      data)

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

/--
Input names for the W1620 closed-map route with row data derived from
closed-embedding rows through W580.
-/
def
    boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620 :
    List String :=
  ["W735 closed-map branch data, including W716 boundary, normalized, and\
      source-triangulation data",
    "selected W461 provider for WPP-op left closed-embedding",
    "row-aware closed-embedding provider for WPP-op SnakeInput; W580 derives\
      the closed-map row provider"]

theorem
    boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620_count :
    boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620.length =
      3 :=
  rfl

/--
Input names for the W1621 closed-map route with selected-W461 derived from
W735 relation/target data and row data derived through W580.
-/
def
    boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621 :
    List String :=
  ["W735 closed-map branch data, including W717 relation data, W715 target\
      surjective-compact data, W716 boundary, normalized, and\
      source-triangulation data",
    "row-aware closed-embedding provider for WPP-op SnakeInput; W580 derives\
      the closed-map row provider"]

theorem
    boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621_count :
    boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621.length =
      2 :=
  rfl

/--
Input names for the W1622 closed-map route with row-aware closed-embedding
data derived from W718 diagram closed-embedding components.
-/
def
    boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622 :
    List String :=
  ["W735 closed-map branch data, including W717 relation data, W715 target\
      surjective-compact data, W716 boundary, normalized, and\
      source-triangulation data",
    "W718 selected-difference closed-embedding diagram component provider;\
      W714/W711/W581 derive row-aware closed-embedding rows, then W580 derives\
      closed-map rows"]

theorem
    boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622_count :
    boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622.length =
      2 :=
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

/-- Current checked W1620 state for closed-embedding-row dominance at W879. -/
structure
    MetrizableBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1620 :
    Type where
  seed : String
  declarations : List String
  rowDominanceResult : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1620 state for deriving W879 closed-map row data from
closed-embedding rows.
-/
def
    currentMetrizableBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1620 :
    MetrizableBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1620
    where
  seed :=
    "w1620-boundary-source-pi-zero-selected-closed-embedding-rows-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620",
      "closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "transferInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "acceptedStableOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620",
      "stableCertificateOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_ready",
      "boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620",
      "boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620_count"]
  rowDominanceResult :=
    "proved: W580 closed-embedding rows supply the W879 closed-map row provider"
  stableBoundaryResult :=
    "proved: the W879 closed-map direct-localization boundary runs with the\
      theorem-derived row provider"
  remainingInputs :=
    boundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1620
  productSuccessClaimed := false

theorem
    currentW1620BoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1620;
    state.productSuccessClaimed) = false :=
  rfl

/--
Current checked W1621 state for deriving W1620 selected-W461 from W735
relation/target data.
-/
structure
    MetrizableBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1621 :
    Type where
  seed : String
  declarations : List String
  targetDataResult : String
  selectedW461Result : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1621 state for deriving both selected-W461 and closed-map rows.
-/
def
    currentMetrizableBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1621 :
    MetrizableBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1621
    where
  seed :=
    "w1621-boundary-source-pi-zero-target-data-closed-embedding-rows-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621",
      "compactTargetProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621",
      "selectedW461ProviderOfClosedMapBoundarySourcePiZeroTargetDataW1621",
      "closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "transferInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621",
      "stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_ready",
      "boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621",
      "boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621_count"]
  targetDataResult :=
    "proved: W735 W717 relation data plus W715 target-surjective compact data\
      derive the W517 compact-target relation provider"
  selectedW461Result :=
    "proved: the W517 compact-target provider supplies W1620's selected-W461\
      provider through W524"
  stableBoundaryResult :=
    "proved: the W1620 direct-localization boundary runs with both\
      selected-W461 and closed-map rows theorem-derived"
  remainingInputs :=
    boundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputNamesW1621
  productSuccessClaimed := false

theorem
    currentW1621BoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryRouteStateW1621;
    state.productSuccessClaimed) = false :=
  rfl

/--
Current checked W1622 state for deriving W1621 row-aware closed-embedding rows
from W718 diagram closed-embedding components.
-/
structure
    MetrizableBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryRouteStateW1622 :
    Type where
  seed : String
  declarations : List String
  componentAssemblyResult : String
  rowProviderResult : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1622 state for deriving selected-W461, row-aware
closed-embedding rows, and closed-map rows from theorem-level inputs.
-/
def
    currentMetrizableBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryRouteStateW1622 :
    MetrizableBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryRouteStateW1622
    where
  seed :=
    "w1622-boundary-source-pi-zero-target-data-global-closed-embedding-components-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622",
      "closedEmbeddingProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "closedEmbeddingRowsProviderOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "transferInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622",
      "stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_ready",
      "boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622",
      "boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622_count"]
  componentAssemblyResult :=
    "proved: W718 closed-embedding diagram components adapt through W714 to\
      W711 explicit component fields and assemble a W525 closed-embedding\
      provider"
  rowProviderResult :=
    "proved: W581 narrows the assembled W525 closed-embedding provider to\
      W1621's row-aware closed-embedding input"
  stableBoundaryResult :=
    "proved: the W1621 direct-localization boundary runs with selected-W461,\
      row-aware closed-embedding rows, and closed-map rows theorem-derived"
  remainingInputs :=
    boundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputNamesW1622
  productSuccessClaimed := false

theorem
    currentW1622BoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryRouteStateW1622;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
