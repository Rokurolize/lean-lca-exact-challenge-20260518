import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableInstanceFactsFromDirectSourceW1537

/-!
W1538 compares the W1537 typeclass-route packages with the earlier W1533
direct-source packages. The point is to record that the stable instance-family
adapter does not create a new product-facing object: it definitionally recovers
the same direct-source bounded-derived package and the same W1535/W1536 field
projections on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1538 reuses the W1537 stable instance-family surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537

/-- Closed-map W1537 typeclass-route package is the W1533 direct-source package. -/
theorem closedMapW829StableInstancePackage_eq_directSourcePackageW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829DirectSourceStableInstancePackageW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1537 typeclass-route package is the W1533 direct-source package. -/
theorem closedEmbeddingW829StableInstancePackage_eq_directSourcePackageW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829DirectSourceStableInstancePackageW1537
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map W1537 typeclass-route package is also the W1534 accepted package. -/
theorem closedMapW829StableInstancePackage_eq_acceptedPackageW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829DirectSourceStableInstancePackageW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1537 typeclass-route package is also the W1534 accepted package. -/
theorem closedEmbeddingW829StableInstancePackage_eq_acceptedPackageW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829DirectSourceStableInstancePackageW1537
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Reprojecting the closed-map W1537 typeclass package recovers W1536 direct projections. -/
theorem closedMapW829StableInstancePackageProjectionFacts_eq_directSourceProjectionFactsW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedMapW829DirectSourceStableInstancePackageW1537
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedMapW829DirectSourceStableProjectionFactsW1536
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Reprojecting the closed-embedding W1537 typeclass package recovers W1536 projections. -/
theorem
    closedEmbeddingW829StableInstancePackageProjectionFacts_eq_directSourceProjectionFactsW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedEmbeddingW829DirectSourceStableInstancePackageW1537
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      closedEmbeddingW829DirectSourceStableProjectionFactsW1536
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Reprojecting the closed-map W1537 package recovers W1535 accepted projections. -/
theorem closedMapW829StableInstancePackageProjectionFacts_eq_acceptedProjectionFactsW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedMapW829DirectSourceStableInstancePackageW1537
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Reprojecting the closed-embedding W1537 package recovers W1535 accepted projections. -/
theorem closedEmbeddingW829StableInstancePackageProjectionFacts_eq_acceptedProjectionFactsW1538
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputW1538)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedEmbeddingW829DirectSourceStableInstancePackageW1537
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1538 names the adapter-erasure equalities for the W1537 typeclass route. -/
def w829StableInstancePackageComparisonFactNamesW1538 : List String :=
  ["closed-map W1537 typeclass package equals W1533 direct package",
    "closed-embedding W1537 typeclass package equals W1533 direct package",
    "closed-map W1537 typeclass package equals W1534 accepted package",
    "closed-embedding W1537 typeclass package equals W1534 accepted package",
    "closed-map W1537 reprojected fields equal W1536 direct projections",
    "closed-embedding W1537 reprojected fields equal W1536 direct projections",
    "closed-map W1537 reprojected fields equal W1535 accepted projections",
    "closed-embedding W1537 reprojected fields equal W1535 accepted projections"]

theorem w829StableInstancePackageComparisonFactNamesW1538_count :
    w829StableInstancePackageComparisonFactNamesW1538.length = 8 :=
  rfl

/-- W1538 keeps the W1537 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537_count

/-- Current W1538 nonterminal state after erasing the W1537 typeclass adapter. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonStateW1538 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  remainingInputs : List String
  comparisonFacts : List String
  productSuccessClaimed : Bool

/-- W1538 records that W1537's typeclass-route package is the same direct package. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonStateW1538 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonStateW1538
    where
  seed :=
    "w1538-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-instance-package-comparison"
  declarations :=
    ["closedMapW829StableInstancePackage_eq_directSourcePackageW1538",
      "closedEmbeddingW829StableInstancePackage_eq_directSourcePackageW1538",
      "closedMapW829StableInstancePackage_eq_acceptedPackageW1538",
      "closedEmbeddingW829StableInstancePackage_eq_acceptedPackageW1538",
      "closedMapW829StableInstancePackageProjectionFacts_eq_directSourceProjectionFactsW1538",
      "closedEmbeddingW829StableInstancePackageProjectionFacts_eq_directSourceProjectionFactsW1538",
      "closedMapW829StableInstancePackageProjectionFacts_eq_acceptedProjectionFactsW1538",
      "closedEmbeddingW829StableInstancePackageProjectionFacts_eq_acceptedProjectionFactsW1538",
      "w829StableInstancePackageComparisonFactNamesW1538_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538_count"]
  comparisonResult :=
    "proved: W1537 typeclass-route stable packages erase definitionally to the \
      W1533 direct-source packages and recover W1535/W1536 projections on both \
      branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonInputNamesW1538
  comparisonFacts := w829StableInstancePackageComparisonFactNamesW1538
  productSuccessClaimed := false

theorem currentW1538W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstancePackageComparisonStateW1538.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
