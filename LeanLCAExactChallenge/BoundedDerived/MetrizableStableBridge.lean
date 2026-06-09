import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataPrimitiveFieldRoute
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

def closednessEndpointStrictExactInputOfLocalizedUnitBoundaryRelationInput
    (input : ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    ClosednessEndpointStrictExactInput :=
  Dbounded.w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
    (Dbounded.w945LeavesOfBoundaryRelationDataTargetNoUnivMembershipDataClosednessDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW946
      input)

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
