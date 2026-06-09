import LeanLCAExactChallenge.Derived.W735DirectLocalizationBoundaryRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroBoundarySourcePiZeroProductRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute
import LeanLCAExactChallenge.Derived.EndpointTopologyFromClosednessBranch
import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute
import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipEndpointShortExactUnitConflationWitnessPrimitiveFieldRoute
import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeW735W732SelectedCochainConvergenceGuardW1519

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
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519
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
W1623 closed-map branch data where the W1519 selected-cochain convergence
surface supplies both W735 closed-map exact inputs and W718 closed-embedding
diagram components through its W973 closed-embedding closedness data.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623 :
    Type 2 where
  input :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519

/--
W1624 closed-map branch data where one W1007 branch-full-data input supplies
the W735 exact inputs and W718 closed-embedding diagram components.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624 :
    Type 2 where
  branchFullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007

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
W1623 extracts the W973 closed-embedding closedness data from the W1519 input
surface via the W1510 comparison layer.
-/
noncomputable def
    closedEmbeddingClosednessDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    input

/--
W1623 obtains W718 closed-embedding diagram components from W1519's W973 data.
-/
noncomputable def
    globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718 :=
  globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
    (closedEmbeddingClosednessDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      input)

/--
W1623 converts the W718 closed-embedding component provider to W718 closed-map
components for the W1519 closed-map W735 exact-input constructor.
-/
noncomputable def
    globalClosedMapComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    SelectedDifferenceClosedMapDiagramComponentProviderW718 where
  pi1 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
          input) S).isClosedMap
  pi2 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
          input) S).isClosedMap
  pi3 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
          input) S).isClosedMap

/--
W1623 obtains the W519 mapped-cokernel closed-embedding provider from W1519's
W973 data.
-/
noncomputable def
    mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    MappedExplicitCokernelClosedEmbeddingProviderW519 :=
  mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
    (closedEmbeddingClosednessDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      input)

/--
W1623 converts mapped explicit cokernel closed embeddings to closed maps for
the W1519 closed-map W735 exact-input constructor.
-/
noncomputable def
    mappedCokernelClosedMapProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    MappedExplicitCokernelClosedMapProviderW519 where
  isClosedMap := by
    intro X Y f
    exact
      ((mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
        input).isClosedEmbedding (X := X) (Y := Y) f).isClosedMap

/--
W1623 constructs W735 closed-map exact inputs from one W1519 input by deriving
both closed-map components and mapped-cokernel closed-map data from the same
closed-embedding closedness source.
-/
noncomputable def
    closedMapExactInputsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
    data.input
    (globalClosedMapComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data.input)
    (mappedCokernelClosedMapProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data.input)

/--
W1623 projects its one-input W1519 surface to W1622's closed-map target-data and
global closed-embedding component surface.
-/
noncomputable def
    closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622
    where
  exactInputs :=
    closedMapExactInputsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data.input

/--
W1624 extracts W973 closed-embedding closedness data directly from the W1007
branch-full-data input.
-/
noncomputable def
    closedEmbeddingClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfBranchFullDataW1007 input

/--
W1624 obtains W718 closed-embedding diagram components from W1007's W973 data.
-/
noncomputable def
    globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718 :=
  globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
    (closedEmbeddingClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 converts W718 closed-embedding component fields to closed-map component
fields for the closed-map W735 exact-input constructor.
-/
noncomputable def
    globalClosedMapComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    SelectedDifferenceClosedMapDiagramComponentProviderW718 where
  pi1 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi1DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
          input) S).isClosedMap
  pi2 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi2DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
          input) S).isClosedMap
  pi3 := by
    intro S
    exact
      (selectedDifferenceClosedEmbeddingPi3DiagramField_of_componentProviderW718
        (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
          input) S).isClosedMap

/--
W1624 obtains the W519 mapped-cokernel closed-embedding provider from W1007.
-/
noncomputable def
    mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MappedExplicitCokernelClosedEmbeddingProviderW519 :=
  mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
    (closedEmbeddingClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 converts mapped explicit cokernel closed embeddings to closed maps for
the closed-map W735 exact-input constructor.
-/
noncomputable def
    mappedCokernelClosedMapProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MappedExplicitCokernelClosedMapProviderW519 where
  isClosedMap := by
    intro X Y f
    exact
      ((mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        input).isClosedEmbedding (X := X) (Y := Y) f).isClosedMap

/--
W1624 presents W1007's W973 data as the W725 closed-embedding branch consumed
by the homology-free selected-cochain route.
-/
noncomputable def
    diagramAndMappedCokernelClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725 :=
  .closedEmbedding
    (globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)
    (mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 projects W949 endpoint-localized-unit data from the W1007 W950 package.
-/
noncomputable def
    endpointLocalizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    EndpointStrictExactLocalizedUnitDataProviderW949 :=
  endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 input)

/--
W1624 projects W948 normalized-source triangulation data from W1007.
-/
noncomputable def
    normalizedSourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    NormalizedFixedTargetSourceTriangulationDataProviderW948 :=
  normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
    (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 input)

/--
W1624 projects W719 normalized fixed-target data from W1007.
-/
noncomputable def
    normalizedFixedTargetDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppNormalizedFixedTargetDataProviderW719 :=
  normalizedFixedTargetDataOfNormalizedSourceTriangulationDataW948
    (normalizedSourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 projects W722 source-triangulation data from W1007.
-/
noncomputable def
    sourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppSourceTriangulationDataProviderW722 :=
  sourceTriangulationDataOfNormalizedSourceTriangulationDataW948
    (normalizedSourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 projects W945 localized-unit data from W1007's W949 package.
-/
noncomputable def
    localizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :=
  localizedUnitDataOfEndpointLocalizedUnitDataW949
    (endpointLocalizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 derives W721 localized-right-adjoint data from W1007's W945 localized
unit package.
-/
noncomputable def
    localizedRightAdjointDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppLocalizedRightAdjointDataProviderW721 :=
  localizedRightAdjointDataOfLocalizedUnitDataW945
    (localizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 derives W856 endpoint topology facts from W1007 endpoint strict
short-exactness.
-/
noncomputable def
    endpointTopologyFactsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppEndpointTopologyFactsProviderW856 where
  endpointClosedEmbedding := fun K i =>
    (endpointStrictExactOfBranchFullDataW1007 input K i).closed_inclusion
  endpointOpenMap := fun K i =>
    (endpointStrictExactOfBranchFullDataW1007 input K i).open_map
  endpointEpiOfExactAt :=
    endpointEpiOfShortExactPrimitiveW935
      (endpointShortExactOfEndpointStrictExactPrimitiveW938
        (endpointStrictExactOfBranchFullDataW1007 input))

/--
W1624 reconstructs W720 endpoint strict-topology data through W856 using
W1007's closed-embedding W519 branch plus endpoint facts.
-/
noncomputable def
    endpointStrictTopologyDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (input :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    MetrizableWppEndpointStrictTopologyDataProviderW720 :=
  endpointStrictTopologyDataOfClosednessBranchW856
    (diagramAndMappedCokernelClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)
    (endpointTopologyFactsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      input)

/--
W1624 assembles the W853 homology-free route data from one W1007 branch-full
data input.
-/
noncomputable def
    homologyFreeRouteDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853
    where
  boundaryData :=
    (boundaryRelationDataOfBranchFullDataW1007 data.branchFullData).boundaryData
  relationData :=
    (boundaryRelationDataOfBranchFullDataW1007 data.branchFullData).relationData
  targetSurjectiveCompactForTargetProvider :=
    targetSurjectiveCompactDataOfBranchFullDataW1007 data.branchFullData
  diagramAndMappedCokernelClosednessData :=
    diagramAndMappedCokernelClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData
  normalizedFixedTargetData :=
    normalizedFixedTargetDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData
  sourceTriangulationData :=
    sourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData
  endpointStrictTopologyData :=
    endpointStrictTopologyDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData
  localizedRightAdjointData :=
    localizedRightAdjointDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData

/--
W1624 constructs W735 closed-map exact inputs from one W1007 branch-full-data
input.
-/
noncomputable def
    closedMapExactInputsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedMapExactInputsOfHomologyFreeRouteDataW853
    (homologyFreeRouteDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data)
    (globalClosedMapComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData)
    (mappedCokernelClosedMapProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData)

/--
W1624 projects its one-input W1007 surface to W1622's closed-map target-data
and global closed-embedding component surface.
-/
noncomputable def
    closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622
    where
  exactInputs :=
    closedMapExactInputsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data
  globalClosedEmbeddingComponents :=
    globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data.branchFullData

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

/--
W1623 closed-map WPP colimit stability, with the W1622 inputs derived from one
W1519 closed-embedding closedness source.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/--
W1624 closed-map WPP colimit stability, with the W1622 inputs derived from one
W1007 branch-full-data source.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/--
W1623 closed-map branch converted to W877 direct-localization boundary data.
-/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/--
W1624 closed-map branch converted to W877 direct-localization boundary data.
-/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/-- W1623 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/-- W1624 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/-!
W1623 exposes a closed-map direct-localization branch whose W735 exact inputs
and W718 closed-embedding components are derived from one W1519 closedness
surface.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/-!
W1624 exposes a closed-map direct-localization branch whose W735 exact inputs
and W718 closed-embedding components are derived from one W1007 branch-full
data surface.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/- W1623 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/- W1624 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/- W1623 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/- W1624 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/--
W1623 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_ready
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
      data)

/--
W1624 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_ready
    (closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
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

/--
Input names for the W1623 closed-map route with W735 exact inputs and W718
closed-embedding components derived from one W1519 closedness surface.
-/
def
    boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623 :
    List String :=
  ["W1519 selected-cochain convergence input carrying W973 closed-embedding\
      closedness data; W1623 derives W718 closed-embedding components, W718\
      closed-map components, W519 closed-map mapped cokernel data, and W735\
      closed-map exact inputs"]

theorem
    boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623_count :
    boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623.length =
      1 :=
  rfl

/--
Input names for the W1624 closed-map route with W735 exact inputs and W718
closed-embedding components derived from one W1007 branch-full-data surface.
-/
def
    boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624 :
    List String :=
  ["W1007 branch-full-data input carrying W987 branch-specific full data;\
      W1624 derives W730 boundary/relation data, W715 target-surjective\
      compact data, W973 closed-embedding closedness data, W950 normalized\
      source/endpoint-localized-unit data, W856/W720 endpoint topology data,\
      W718 closed-map and closed-embedding components, W519 closed-map mapped\
      cokernel data, and W735 closed-map exact inputs"]

theorem
    boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624_count :
    boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624.length =
      1 :=
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

/--
Current checked W1623 state for deriving W1622's W735 exact-input and
closed-embedding component surface from one W1519 closedness input.
-/
structure
    MetrizableBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1623 :
    Type where
  seed : String
  declarations : List String
  closednessExtractionResult : String
  closedMapConversionResult : String
  exactInputResult : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1623 state for the one-input W1519 closedness
direct-localization boundary route.
-/
def
    currentMetrizableBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1623 :
    MetrizableBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1623
    where
  seed :=
    "w1623-boundary-source-pi-zero-w1519-closed-embedding-closedness-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623",
      "closedEmbeddingClosednessDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "globalClosedEmbeddingComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "globalClosedMapComponentsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "mappedCokernelClosedMapProviderOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "closedMapExactInputsOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "transferInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "acceptedStableOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623",
      "stableCertificateOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_ready",
      "boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623",
      "boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623_count"]
  closednessExtractionResult :=
    "proved: W1519's input exposes W973 closed-embedding closedness data\
      through the W1510 comparison layer"
  closedMapConversionResult :=
    "proved: closed-embedding W718 components and W519 mapped cokernels supply\
      the corresponding closed-map providers"
  exactInputResult :=
    "proved: W1519 constructs W735 closed-map exact inputs from the derived\
      closed-map components and mapped-cokernel provider"
  stableBoundaryResult :=
    "proved: the W1622 direct-localization boundary runs with its two inputs\
      derived from the single W1519 closedness surface"
  remainingInputs :=
    boundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1623
  productSuccessClaimed := false

theorem
    currentW1623BoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1623;
    state.productSuccessClaimed) = false :=
  rfl

/--
Current checked W1624 state for deriving W1622's W735 exact-input and
closed-embedding component surface from one W1007 branch-full-data input.
-/
structure
    MetrizableBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1624 :
    Type where
  seed : String
  declarations : List String
  closednessExtractionResult : String
  endpointTopologyResult : String
  exactInputResult : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1624 state for the one-input W1007 branch-full-data
direct-localization boundary route.
-/
def
    currentMetrizableBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1624 :
    MetrizableBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1624
    where
  seed :=
    "w1624-boundary-source-pi-zero-branch-full-data-closed-embedding-closedness-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624",
      "closedEmbeddingClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "globalClosedEmbeddingComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "globalClosedMapComponentsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "mappedCokernelClosedEmbeddingProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "mappedCokernelClosedMapProviderOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "diagramAndMappedCokernelClosednessDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "endpointLocalizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "normalizedSourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "normalizedFixedTargetDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "sourceTriangulationDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "localizedUnitDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "localizedRightAdjointDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "endpointTopologyFactsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "endpointStrictTopologyDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "homologyFreeRouteDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "closedMapExactInputsOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "transferInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "acceptedStableOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624",
      "stableCertificateOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_ready",
      "boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624",
      "boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624_count"]
  closednessExtractionResult :=
    "proved: W1007 exposes W973 closed-embedding closedness data, W718\
      closed-embedding components, and W519 mapped-cokernel closed embeddings\
      from one W987 branch-full-data input"
  endpointTopologyResult :=
    "proved: W1007 endpoint strict exactness supplies the three W856 endpoint\
      topology facts, while W973/W519 supplies forgetful homology preservation;\
      together they reconstruct W720 endpoint strict-topology data"
  exactInputResult :=
    "proved: W1007 fields assemble W853 homology-free route data and then\
      construct W735 closed-map exact inputs"
  stableBoundaryResult :=
    "proved: the W1622 direct-localization boundary runs with its two inputs\
      derived from the single W1007 branch-full-data surface"
  remainingInputs :=
    boundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1624
  productSuccessClaimed := false

theorem
    currentW1624BoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1624;
    state.productSuccessClaimed) = false :=
  rfl

/--
W1625 closed-map branch data where the W1007 wrapper is eliminated and the
direct-localization boundary consumes the underlying W987 full-data provider.
-/
structure
    MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625 :
    Type 2 where
  fullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987

/--
W1625 turns the underlying W987 full-data provider into the W1007 surface
required by the already checked W1624 route.
-/
def branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007
    where
  branchFullData := fullData

/--
W1625 projects its direct W987 input to W1624's branch-full-data route surface.
-/
def
    branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    MetrizableClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1624
    where
  branchFullData :=
    branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
      data.fullData

/-- W1625's W1007 wrapper contains exactly its original W987 input. -/
theorem branchFullDataInputOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    branchFullDataInputOfBranchFullDataW1007
        (branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          data.fullData) =
      data.fullData :=
  rfl

/-- W1625's W1007 projection keeps W987's boundary/relation component. -/
theorem boundaryRelationDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    boundaryRelationDataOfBranchFullDataW1007
        (branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          data.fullData) =
      boundaryRelationDataOfFullDataW987 data.fullData :=
  rfl

/-- W1625's W1007 projection keeps W987's W986 target/endpoint component. -/
theorem targetNormalizedEndpointDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        (branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          data.fullData) =
      targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        data.fullData :=
  rfl

/--
W1625 closed-map WPP colimit stability with W1624's W1007 wrapper eliminated
from the external input surface.
-/
theorem
    colimitStabilityOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair :=
  colimitStabilityOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/--
W1625 closed-map branch converted to W877 direct-localization boundary data.
-/
noncomputable def
    closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    MetrizableClosedMapW735DirectLocalizationBoundaryDataW877 :=
  closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/-- W1625 closed-map branch as WPP finite-shape transfer inputs. -/
noncomputable def
    transferInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    MetrizableWalkingParallelPairFiniteShapeTransferInputs :=
  transferInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/--
W1625 exposes a closed-map direct-localization branch whose remaining input is
the W987 full-data provider itself.
-/
noncomputable def
    directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/- W1625 closed-map branch passes the accepted stable direct-localization gate. -/
noncomputable def
    acceptedStableOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  acceptedStableOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/- W1625 closed-map branch produces the bounded-derived package. -/
noncomputable def
    boundedDerivedOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/--
W1625 closed-map branch produces the ready four-projection stable certificate.
-/
theorem
    stableCertificateOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_ready
    (data :
      MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625) :
    let inputs :=
      directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        data
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready :=
  stableCertificateOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_ready
    (branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
      data)

/--
Input names for the W1625 closed-map route after eliminating W1007 from the
external direct-localization boundary surface.
-/
def
    boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625 :
    List String :=
  fullDataInputNamesW987

theorem
    boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625_count :
    boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625.length =
      1 :=
  fullDataInputNamesW987_count

/--
Current checked W1625 state for the one-input W987 full-data direct-localization
boundary route.
-/
structure
    MetrizableBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1625 :
    Type where
  seed : String
  declarations : List String
  wrapperEliminationResult : String
  stableBoundaryResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/--
Current checked W1625 state records that the W1007 branch-full-data wrapper is
no longer part of the remaining external input surface.
-/
def
    currentMetrizableBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1625 :
    MetrizableBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1625
    where
  seed :=
    "w1625-boundary-source-pi-zero-full-data-closed-embedding-closedness-direct-localization-boundary"
  declarations :=
    ["MetrizableClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1625",
      "branchFullDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625",
      "branchFullDataInputOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "boundaryRelationDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "targetNormalizedEndpointDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "colimitStabilityOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "closedMapW735DirectBoundaryDataOfBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "transferInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "acceptedStableOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "boundedDerivedOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625",
      "stableCertificateOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_ready",
      "boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625",
      "boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625_count"]
  wrapperEliminationResult :=
    "proved: the W1625 route consumes the underlying W987 full-data provider\
      directly, then reconstructs exactly the W1007 branch-full-data surface\
      needed by W1624 without keeping W1007 as an external obligation"
  stableBoundaryResult :=
    "proved: the W1624 direct-localization boundary, accepted-stable gate,\
      bounded-derived package, and ready stable certificate run from the\
      direct W987 input"
  remainingInputs :=
    boundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputNamesW1625
  productSuccessClaimed := false

theorem
    currentW1625BoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundary_productSuccess :
    (let state :=
      currentMetrizableBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryRouteStateW1625;
    state.productSuccessClaimed) = false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
