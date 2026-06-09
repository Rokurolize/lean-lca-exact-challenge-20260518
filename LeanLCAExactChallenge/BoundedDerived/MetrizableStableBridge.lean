import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundaryDirectLocalization
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryRoute
import LeanLCAExactChallenge.Derived.RouteDataSelectedCochainStableRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute
import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldsRoute
import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableSemanticAdapterComparisonW1539

/-!
This file records the current bridge from the direct-source metrizable stable
instance facts into the short product-facing bounded-derived API.

It does not assert final product success: the declarations here are still
parameterized by the direct-source facts or inputs. The point is to keep the
accepted/certificate route from being the only way to mention the stable
package that the final surface needs.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace BoundedDerived
namespace Metrizable

abbrev DirectSourceInput : Type 2 :=
  Dbounded.W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539

abbrev StableInstanceFacts : Type 2 :=
  Dbounded.W829DirectSourceStableInstanceFactsW1537

abbrev ClosedMapComponentProvider : Type 1 :=
  Dbounded.SelectedDifferenceClosedMapDiagramComponentProviderW718

abbrev ClosedEmbeddingComponentProvider : Type 1 :=
  Dbounded.SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718

abbrev ClosedMapCokernelProvider : Type 1 :=
  MappedExplicitCokernelClosedMapProviderW519

abbrev ClosedEmbeddingCokernelProvider : Type 1 :=
  MappedExplicitCokernelClosedEmbeddingProviderW519

abbrev ClosednessEndpointStrictExactInput : Type 2 :=
  Dbounded.MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944

abbrev ClosednessEndpointLocalizedUnitBoundaryRelationInput : Type 2 :=
  Dbounded.MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW946

abbrev ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput :
    Type 2 :=
  Dbounded.MetrizableWppClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW947

abbrev ClosedEmbeddingClosednessFieldsInputW961 : Type 2 :=
  Dbounded.MetrizableWppClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointUnitComponentsPrimitiveFieldLeavesW961

abbrev ClosedMapExactInputsSelectedCochainComparisonInputW1614 : Type 2 :=
  Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

abbrev ClosedEmbeddingExactInputsSelectedCochainComparisonInputW1614 : Type 2 :=
  Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

abbrev ClosedMapConcreteFieldsSelectedCochainComparisonInputW1615 : Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615

abbrev ClosedEmbeddingConcreteFieldsSelectedCochainComparisonInputW1615 :
    Type 2 :=
  Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615

abbrev ClosedMapSplitFieldsSelectedCochainComparisonInputW1616 : Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616

abbrev ClosedEmbeddingSplitFieldsSelectedCochainComparisonInputW1616 : Type 2 :=
  Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616

abbrev ClosedMapStructuralFieldsSelectedCochainComparisonInputW1617 : Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617

abbrev ClosedEmbeddingStructuralFieldsSelectedCochainComparisonInputW1617 :
    Type 2 :=
  Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617

abbrev ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879 :
    Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879

abbrev ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879 :
    Type 2 :=
  Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryDataW879

abbrev ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620 :
    Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryDataW1620

abbrev ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621 :
    Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryDataW1621

abbrev ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622 :
    Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryDataW1622

abbrev ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623 :
    Type 2 :=
  Dbounded.MetrizableClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryDataW1623

abbrev RouteDataSelectedCochainComparisonInputW852 : Type 2 :=
  Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732

abbrev StableInstanceBoundaryInput : Type 1 :=
  Dbounded.MetrizableStableInstanceBoundaryInputs

abbrev DirectLocalizationBoundaryInput : Type 1 :=
  Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs

noncomputable def stablePackageOfStableInstanceBoundary
    (inputs : StableInstanceBoundaryInput) : StablePackage :=
  Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
    inputs

noncomputable def stablePackageOfDirectLocalizationBoundary
    (inputs : DirectLocalizationBoundaryInput) : StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    inputs

theorem stablePackageOfDirectLocalizationBoundary_eq_stableInstanceBoundary
    (inputs : DirectLocalizationBoundaryInput) :
    stablePackageOfDirectLocalizationBoundary inputs =
      stablePackageOfStableInstanceBoundary
        (Dbounded.metrizableStableInstanceBoundaryInputs_of_directLocalization
          inputs) :=
  rfl

theorem stablePackageOfDirectLocalizationBoundary_inputCount_lt_stableInstanceBoundary :
    Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames.length <
      Dbounded.metrizableStableInstanceBoundaryRemainingInputNames.length := by
  rw [Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames_count,
    Dbounded.metrizableStableInstanceBoundaryRemainingInputNames_count]
  norm_num

def closednessEndpointStrictExactInputOfLocalizedUnitBoundaryRelationInput
    (input : ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    ClosednessEndpointStrictExactInput :=
  Dbounded.w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
    (Dbounded.w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
      input)

def closednessEndpointLocalizedUnitBoundaryRelationInputOfTargetNoUnivClosednessInput
    (input :
      ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    ClosednessEndpointLocalizedUnitBoundaryRelationInput :=
  Dbounded.w946LeavesOfTargetNoUnivClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    input

noncomputable def stablePackageOfInstanceFacts
    (facts : StableInstanceFacts) : StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfStableInstanceFactsW1537 facts

theorem stablePackageOfInstanceFacts_carrier
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).quasicategoryCarrier = rfl :=
  rfl

theorem stablePackageOfInstanceFacts_preadditive
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).preadditive = facts.preadditive :=
  rfl

theorem stablePackageOfInstanceFacts_finiteLimits
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).finiteLimitInstance = facts.finiteLimits :=
  rfl

theorem stablePackageOfInstanceFacts_finiteColimits
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).finiteColimitInstance = facts.finiteColimits :=
  rfl

theorem stablePackageOfInstanceFacts_zeroObject
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).zeroObjectInstance = facts.zeroObject :=
  rfl

theorem stablePackageOfInstanceFacts_shiftAdditive
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).shiftAdditiveAll = facts.shiftAdditiveAll :=
  rfl

theorem stablePackageOfInstanceFacts_suspensionAdditive
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).suspensionAdditive = facts.suspensionAdditive :=
  rfl

theorem stablePackageOfInstanceFacts_pretriangulated
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).pretriangulatedStructure =
      facts.pretriangulated :=
  rfl

theorem stablePackageOfInstanceFacts_triangulated
    (facts : StableInstanceFacts) :
    (stablePackageOfInstanceFacts facts).triangulatedStructure = facts.triangulated :=
  rfl

noncomputable def stablePackageOfClosednessEndpointStrictExactInput
    (input : ClosednessEndpointStrictExactInput) : StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    input

theorem stablePackageOfClosednessEndpointStrictExactInput_eq_w944
    (input : ClosednessEndpointStrictExactInput) :
    stablePackageOfClosednessEndpointStrictExactInput input =
      Dbounded.boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
        input :=
  rfl

noncomputable def stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput
    (input : ClosednessEndpointLocalizedUnitBoundaryRelationInput) : StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
    input

theorem stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput_eq_w946
    (input : ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput input =
      Dbounded.boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
        input :=
  rfl

theorem
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput_eq_closednessEndpointStrictExactInput
    (input : ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput input =
      stablePackageOfClosednessEndpointStrictExactInput
        (closednessEndpointStrictExactInputOfLocalizedUnitBoundaryRelationInput
          input) :=
  rfl

noncomputable def
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
    (input :
      ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
    input

theorem
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput_eq_w947
    (input :
      ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
        input =
      Dbounded.boundedDerivedInfinityCategoryOfClosedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW947
        input :=
  rfl

theorem
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput_eq_localizedUnitBoundaryRelationInput
    (input :
      ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
        input =
      stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput
        (closednessEndpointLocalizedUnitBoundaryRelationInputOfTargetNoUnivClosednessInput
          input) :=
  rfl

noncomputable def stablePackageOfClosedEmbeddingClosednessFieldsW961
    (input : ClosedEmbeddingClosednessFieldsInputW961) : StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsW961
    input

theorem stablePackageOfClosedEmbeddingClosednessFieldsW961_eq_w961
    (input : ClosedEmbeddingClosednessFieldsInputW961) :
    stablePackageOfClosedEmbeddingClosednessFieldsW961 input =
      Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsW961
        input :=
  rfl

noncomputable def stablePackageOfRouteDataSelectedCochainComparisonW852
    (routeData : RouteDataSelectedCochainComparisonInputW852) : StablePackage :=
  Dbounded.boundedDerivedOfRouteDataDirectBoundaryW852
    routeData

theorem stablePackageOfRouteDataW852_eq_directBoundary
    (routeData : RouteDataSelectedCochainComparisonInputW852) :
    stablePackageOfRouteDataSelectedCochainComparisonW852 routeData =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfRouteDataComparisonSelectedCochainW852
          routeData) :=
  rfl

noncomputable def stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs : ClosedMapExactInputsSelectedCochainComparisonInputW1614) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    exactInputs

noncomputable def
    stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs : ClosedEmbeddingExactInputsSelectedCochainComparisonInputW1614) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
    exactInputs

theorem stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary
    (exactInputs : ClosedMapExactInputsSelectedCochainComparisonInputW1614) :
    stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614 exactInputs =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
          exactInputs) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary
    (exactInputs : ClosedEmbeddingExactInputsSelectedCochainComparisonInputW1614) :
    stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614 exactInputs =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
          exactInputs) :=
  rfl

noncomputable def
    stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data : ClosedMapConcreteFieldsSelectedCochainComparisonInputW1615) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    data

noncomputable def
    stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data : ClosedEmbeddingConcreteFieldsSelectedCochainComparisonInputW1615) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
    data

theorem
    stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_exactInputsSelectedCochainComparisonW1614
    (data : ClosedMapConcreteFieldsSelectedCochainComparisonInputW1615) :
    stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615 data =
      stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614
        (Dbounded.closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_exactInputsSelectedCochainComparisonW1614
    (data : ClosedEmbeddingConcreteFieldsSelectedCochainComparisonInputW1615) :
    stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        data =
      stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
        (Dbounded.closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary
    (data : ClosedMapConcreteFieldsSelectedCochainComparisonInputW1615) :
    stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary
    (data : ClosedEmbeddingConcreteFieldsSelectedCochainComparisonInputW1615) :
    stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

noncomputable def stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data : ClosedMapSplitFieldsSelectedCochainComparisonInputW1616) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
    data

noncomputable def
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data : ClosedEmbeddingSplitFieldsSelectedCochainComparisonInputW1616) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
    data

theorem stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615
    (data : ClosedMapSplitFieldsSelectedCochainComparisonInputW1616) :
    stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616 data =
      stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615
    (data : ClosedEmbeddingSplitFieldsSelectedCochainComparisonInputW1616) :
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
        data =
      stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          data) :=
  rfl

theorem stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary
    (data : ClosedMapSplitFieldsSelectedCochainComparisonInputW1616) :
    stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616 data =
      Dbounded.boundedDerivedOfClosedMapSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        data :=
  rfl

theorem
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary
    (data : ClosedEmbeddingSplitFieldsSelectedCochainComparisonInputW1616) :
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616 data =
      Dbounded.boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        data :=
  rfl

noncomputable def
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data : ClosedMapStructuralFieldsSelectedCochainComparisonInputW1617) :
    StablePackage :=
  stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

noncomputable def
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data : ClosedEmbeddingStructuralFieldsSelectedCochainComparisonInputW1617) :
    StablePackage :=
  stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
      data)

theorem
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616
    (data : ClosedMapStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616
        (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616
    (data : ClosedEmbeddingStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
        (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_concreteFieldsSelectedCochainComparisonW1615
    (data : ClosedMapStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615]

theorem
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_concreteFieldsSelectedCochainComparisonW1615
    (data : ClosedEmbeddingStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615]

theorem
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_directLocalizationBoundary
    (data : ClosedMapStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      Dbounded.boundedDerivedOfClosedMapSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_directLocalizationBoundary
    (data : ClosedEmbeddingStructuralFieldsSelectedCochainComparisonInputW1617) :
    stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      Dbounded.boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

noncomputable def
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
    (data : ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedRowsW879 data

noncomputable def
    stablePackageOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
    (data :
      ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    data

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879_eq_directLocalizationBoundary
    (data : ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
          data) :=
  rfl

theorem
    stablePackageOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879_eq_directLocalizationBoundary
    (data :
      ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    stablePackageOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
          data) :=
  rfl

noncomputable def
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620
    (data :
      ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    data

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620_eq_selectedRowsW879
    (data :
      ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620
        data =
      stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
        (Dbounded.closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
          data) :=
  rfl

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620_eq_directLocalizationBoundary
    (data :
      ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
          data) :=
  rfl

noncomputable def
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    data

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621_eq_selectedClosedEmbeddingRowsW1620
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621
        data =
      stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620
        (Dbounded.closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
          data) :=
  rfl

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621_eq_directLocalizationBoundary
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
          data) :=
  rfl

noncomputable def
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    data

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622_eq_targetDataClosedEmbeddingRowsW1621
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622
        data =
      stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621
        (Dbounded.closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
          data) :=
  rfl

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622_eq_directLocalizationBoundary
    (data :
      ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
          data) :=
  rfl

noncomputable def
    stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623
    (data :
      ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    StablePackage :=
  Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    data

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623_eq_targetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623
        data =
      stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622
        (Dbounded.closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
          data) :=
  rfl

theorem
    stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623_eq_directLocalizationBoundary
    (data :
      ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623
        data =
      stablePackageOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
          data) :=
  rfl

noncomputable def closedMapStablePackageOfDirectSource
    (input : DirectSourceInput)
    (globalClosedMapComponents : ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider : ClosedMapCokernelProvider) :
    StablePackage :=
  Dbounded.closedMapW829DirectSourceStableInstancePackageW1537 input
    globalClosedMapComponents mappedCokernelClosedMapProvider

noncomputable def closedEmbeddingStablePackageOfDirectSource
    (input : DirectSourceInput)
    (globalClosedEmbeddingComponents : ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider : ClosedEmbeddingCokernelProvider) :
    StablePackage :=
  Dbounded.closedEmbeddingW829DirectSourceStableInstancePackageW1537 input
    globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

noncomputable def closedMapStablePackageOfDirectLocalizationBoundary
    (input : DirectSourceInput)
    (globalClosedMapComponents : ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider : ClosedMapCokernelProvider) :
    StablePackage :=
  Dbounded.closedMapBoundedDerivedInfinityCategoryOfW829DirectLocalizationBoundaryW1533
    input globalClosedMapComponents mappedCokernelClosedMapProvider

noncomputable def closedEmbeddingStablePackageOfDirectLocalizationBoundary
    (input : DirectSourceInput)
    (globalClosedEmbeddingComponents : ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider : ClosedEmbeddingCokernelProvider) :
    StablePackage :=
  Dbounded.closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectLocalizationBoundaryW1533
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

theorem closedMapStablePackageOfDirectLocalizationBoundary_eq_w1533
    (input : DirectSourceInput)
    (globalClosedMapComponents : ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider : ClosedMapCokernelProvider) :
    closedMapStablePackageOfDirectLocalizationBoundary input globalClosedMapComponents
      mappedCokernelClosedMapProvider =
        Dbounded.closedMapBoundedDerivedInfinityCategoryOfW829DirectLocalizationBoundaryW1533
          input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

theorem closedEmbeddingStablePackageOfDirectLocalizationBoundary_eq_w1533
    (input : DirectSourceInput)
    (globalClosedEmbeddingComponents : ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider : ClosedEmbeddingCokernelProvider) :
    closedEmbeddingStablePackageOfDirectLocalizationBoundary input
      globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
        Dbounded.closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectLocalizationBoundaryW1533
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

theorem closedMapStablePackageOfDirectSource_eq_directLocalizationBoundary
    (input : DirectSourceInput)
    (globalClosedMapComponents : ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider : ClosedMapCokernelProvider) :
    closedMapStablePackageOfDirectSource input globalClosedMapComponents
      mappedCokernelClosedMapProvider =
        closedMapStablePackageOfDirectLocalizationBoundary input
          globalClosedMapComponents mappedCokernelClosedMapProvider :=
  Dbounded.closedMapW829StableInstancePackage_eq_directLocalizationBoundaryPackageW1538
    input globalClosedMapComponents mappedCokernelClosedMapProvider

theorem closedEmbeddingStablePackageOfDirectSource_eq_directLocalizationBoundary
    (input : DirectSourceInput)
    (globalClosedEmbeddingComponents : ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider : ClosedEmbeddingCokernelProvider) :
    closedEmbeddingStablePackageOfDirectSource input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =
        closedEmbeddingStablePackageOfDirectLocalizationBoundary input
          globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  Dbounded.closedEmbeddingW829StableInstancePackage_eq_directLocalizationBoundaryPackageW1538
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

theorem closedMapStablePackageOfDirectSource_eq_semanticAdapter
    (input : DirectSourceInput)
    (globalClosedMapComponents : ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider : ClosedMapCokernelProvider) :
    closedMapStablePackageOfDirectSource input globalClosedMapComponents
      mappedCokernelClosedMapProvider =
        Dbounded.closedMapW829StableSemanticAdapterPackageW1539 input
          globalClosedMapComponents mappedCokernelClosedMapProvider :=
  (Dbounded.closedMapW829StableSemanticAdapterPackage_eq_typeclassPackageW1539 input
    globalClosedMapComponents mappedCokernelClosedMapProvider).symm

theorem closedEmbeddingStablePackageOfDirectSource_eq_semanticAdapter
    (input : DirectSourceInput)
    (globalClosedEmbeddingComponents : ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider : ClosedEmbeddingCokernelProvider) :
    closedEmbeddingStablePackageOfDirectSource input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider =
        Dbounded.closedEmbeddingW829StableSemanticAdapterPackageW1539 input
          globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  (Dbounded.closedEmbeddingW829StableSemanticAdapterPackage_eq_typeclassPackageW1539
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).symm

end Metrizable
end BoundedDerived

end LeanLCAExactChallenge
