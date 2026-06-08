import LeanLCAExactChallenge.BoundedDerived.Basic
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
