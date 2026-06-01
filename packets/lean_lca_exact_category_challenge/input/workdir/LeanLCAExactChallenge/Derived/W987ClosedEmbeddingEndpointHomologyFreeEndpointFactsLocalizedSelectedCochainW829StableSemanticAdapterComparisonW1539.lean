import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableInstancePackageComparisonW1538

/-!
W1539 compares the legacy semantic-input adapter with the W1537 typeclass-route
stable packages. It records that once the W1537 direct-source stable instance
facts are arranged as `MetrizableOrdinaryStableSemanticInput`, the semantic
adapter produces the same product-facing bounded-derived package, the same
direct-source package, and the same field projections on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1539 reuses the W1538 typeclass/direct-source comparison surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538

/-- Arrange W1537 stable instance-family facts as the legacy semantic-input adapter. -/
noncomputable def stableSemanticInputOfDirectSourceStableInstanceFactsW1539
    (facts : W829DirectSourceStableInstanceFactsW1537) :
    Dbounded.MetrizableOrdinaryStableSemanticInput where
  preadditive := facts.preadditive
  finiteLimits := facts.finiteLimits
  finiteColimits := facts.finiteColimits
  zeroObject := facts.zeroObject
  shiftAdditiveAll := facts.shiftAdditiveAll
  suspensionAdditive := facts.suspensionAdditive
  pretriangulated := facts.pretriangulated
  triangulated := facts.triangulated

/-- Closed-map semantic adapter input from W1537 direct-source stable instance facts. -/
noncomputable def closedMapW829StableSemanticAdapterInputW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  stableSemanticInputOfDirectSourceStableInstanceFactsW1539
    (closedMapW829DirectSourceStableInstanceFactsW1537
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- Closed-embedding semantic adapter input from W1537 direct-source stable instance facts. -/
noncomputable def closedEmbeddingW829StableSemanticAdapterInputW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  stableSemanticInputOfDirectSourceStableInstanceFactsW1539
    (closedEmbeddingW829DirectSourceStableInstanceFactsW1537
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- Closed-map W1539 semantic-adapter accepted certificate package. -/
noncomputable def closedMapW829StableSemanticAdapterAcceptedW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (closedMapW829StableSemanticAdapterInputW1539
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- Closed-embedding W1539 semantic-adapter accepted certificate package. -/
noncomputable def closedEmbeddingW829StableSemanticAdapterAcceptedW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (closedEmbeddingW829StableSemanticAdapterInputW1539
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- Closed-map W1539 semantic-adapter package from W1537 direct-source facts. -/
noncomputable def closedMapW829StableSemanticAdapterPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (closedMapW829StableSemanticAdapterInputW1539
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- Closed-embedding W1539 semantic-adapter package from W1537 direct-source facts. -/
noncomputable def closedEmbeddingW829StableSemanticAdapterPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (closedEmbeddingW829StableSemanticAdapterInputW1539
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- Closed-map semantic-adapter certificate readiness from W1537 facts. -/
theorem closedMapW829StableSemanticAdapterCertificate_readyW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapW829StableSemanticAdapterAcceptedW1539
      input globalClosedMapComponents mappedCokernelClosedMapProvider).certificate.ready :=
  (closedMapW829StableSemanticAdapterAcceptedW1539
    input globalClosedMapComponents mappedCokernelClosedMapProvider).ready

/-- Closed-embedding semantic-adapter certificate readiness from W1537 facts. -/
theorem closedEmbeddingW829StableSemanticAdapterCertificate_readyW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingW829StableSemanticAdapterAcceptedW1539
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).certificate.ready :=
  (closedEmbeddingW829StableSemanticAdapterAcceptedW1539
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).ready

/-- Closed-map semantic-adapter evidence is accepted by the stable route checker. -/
theorem closedMapW829StableSemanticAdapterRouteAcceptedW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (closedMapW829StableSemanticAdapterAcceptedW1539
            input globalClosedMapComponents mappedCokernelClosedMapProvider).certificate) =
      true :=
  (closedMapW829StableSemanticAdapterAcceptedW1539
    input globalClosedMapComponents mappedCokernelClosedMapProvider).accepted

/-- Closed-embedding semantic-adapter evidence is accepted by the stable route checker. -/
theorem closedEmbeddingW829StableSemanticAdapterRouteAcceptedW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.StableRouteAttempt.accepted
        (C := MetrizableLCA.{0})
        (.fullCertificate
          (closedEmbeddingW829StableSemanticAdapterAcceptedW1539
            input globalClosedEmbeddingComponents
            mappedCokernelClosedEmbeddingProvider).certificate) =
      true :=
  (closedEmbeddingW829StableSemanticAdapterAcceptedW1539
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).accepted

/-- Closed-map semantic-adapter package is the W1537 typeclass-route package. -/
theorem closedMapW829StableSemanticAdapterPackage_eq_typeclassPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterPackageW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapW829DirectSourceStableInstancePackageW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding semantic-adapter package is the W1537 typeclass-route package. -/
theorem closedEmbeddingW829StableSemanticAdapterPackage_eq_typeclassPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829StableSemanticAdapterPackageW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingW829DirectSourceStableInstancePackageW1537
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map semantic-adapter package is the W1533 direct-source package. -/
theorem closedMapW829StableSemanticAdapterPackage_eq_directSourcePackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterPackageW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding semantic-adapter package is the W1533 direct-source package. -/
theorem closedEmbeddingW829StableSemanticAdapterPackage_eq_directSourcePackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829StableSemanticAdapterPackageW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map semantic-adapter package is the W1534 accepted package. -/
theorem closedMapW829StableSemanticAdapterPackage_eq_acceptedPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterPackageW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding semantic-adapter package is the W1534 accepted package. -/
theorem closedEmbeddingW829StableSemanticAdapterPackage_eq_acceptedPackageW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829StableSemanticAdapterPackageW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Reprojecting the closed-map semantic-adapter package recovers W1536 projections. -/
theorem
    closedMapW829StableSemanticAdapterPackageProjectionFacts_eq_directSourceProjectionFactsW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedMapW829StableSemanticAdapterPackageW1539
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedMapW829DirectSourceStableProjectionFactsW1536
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Reprojecting the closed-embedding semantic-adapter package recovers W1536 projections. -/
theorem
    closedEmbeddingW829StableSemanticAdapterPackageProjectionFacts_eq_directSourceProjectionFactsW1539
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedEmbeddingW829StableSemanticAdapterPackageW1539
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      closedEmbeddingW829DirectSourceStableProjectionFactsW1536
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1539 names the semantic-adapter erasure facts for the W1537 route. -/
def w829StableSemanticAdapterComparisonFactNamesW1539 : List String :=
  ["closed-map semantic adapter certificate ready",
    "closed-embedding semantic adapter certificate ready",
    "closed-map semantic adapter route accepted",
    "closed-embedding semantic adapter route accepted",
    "closed-map semantic adapter package equals W1537 typeclass package",
    "closed-embedding semantic adapter package equals W1537 typeclass package",
    "closed-map semantic adapter package equals W1533 direct package",
    "closed-embedding semantic adapter package equals W1533 direct package",
    "closed-map semantic adapter package equals W1534 accepted package",
    "closed-embedding semantic adapter package equals W1534 accepted package",
    "closed-map semantic adapter reprojected fields equal W1536 direct projections",
    "closed-embedding semantic adapter reprojected fields equal W1536 direct projections"]

theorem w829StableSemanticAdapterComparisonFactNamesW1539_count :
    w829StableSemanticAdapterComparisonFactNamesW1539.length = 12 :=
  rfl

/-- W1539 keeps the W1538 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538_count

/-- Current W1539 nonterminal state after comparing semantic and typeclass adapters. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonStateW1539 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  remainingInputs : List String
  comparisonFacts : List String
  productSuccessClaimed : Bool

/-- W1539 records that the legacy semantic adapter and W1537 typeclass route agree. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonStateW1539 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonStateW1539
    where
  seed :=
    "w1539-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-semantic-adapter-comparison"
  declarations :=
    ["stableSemanticInputOfDirectSourceStableInstanceFactsW1539",
      "closedMapW829StableSemanticAdapterInputW1539",
      "closedEmbeddingW829StableSemanticAdapterInputW1539",
      "closedMapW829StableSemanticAdapterAcceptedW1539",
      "closedEmbeddingW829StableSemanticAdapterAcceptedW1539",
      "closedMapW829StableSemanticAdapterPackageW1539",
      "closedEmbeddingW829StableSemanticAdapterPackageW1539",
      "closedMapW829StableSemanticAdapterCertificate_readyW1539",
      "closedEmbeddingW829StableSemanticAdapterCertificate_readyW1539",
      "closedMapW829StableSemanticAdapterRouteAcceptedW1539",
      "closedEmbeddingW829StableSemanticAdapterRouteAcceptedW1539",
      "closedMapW829StableSemanticAdapterPackage_eq_typeclassPackageW1539",
      "closedEmbeddingW829StableSemanticAdapterPackage_eq_typeclassPackageW1539",
      "closedMapW829StableSemanticAdapterPackage_eq_directSourcePackageW1539",
      "closedEmbeddingW829StableSemanticAdapterPackage_eq_directSourcePackageW1539",
      "closedMapW829StableSemanticAdapterPackage_eq_acceptedPackageW1539",
      "closedEmbeddingW829StableSemanticAdapterPackage_eq_acceptedPackageW1539",
      "closedMapW829StableSemanticAdapterPackageProjectionFacts_eq_directSourceProjectionFactsW1539",
      "closedEmbeddingW829StableSemanticAdapterPackageProjectionFacts_eq_directSourceProjectionFactsW1539",
      "w829StableSemanticAdapterComparisonFactNamesW1539_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539_count"]
  comparisonResult :=
    "proved: W1537 direct-source stable instance facts, when arranged as the \
      legacy semantic adapter input, produce the same accepted certificate \
      route and the same product-facing bounded-derived package as the \
      W1537 typeclass package, W1533 direct package, and W1534 accepted package"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539
  comparisonFacts := w829StableSemanticAdapterComparisonFactNamesW1539
  productSuccessClaimed := false

theorem currentW1539W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonStateW1539.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
