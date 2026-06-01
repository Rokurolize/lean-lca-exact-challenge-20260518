import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableSemanticAdapterComparisonW1539

/-!
W1540 compares the original W1534 stable-certificate route with the W1539
semantic-adapter route. The point is to record that the certificate wrapper,
the accepted wrapper, and the semantic adapter are not separate product-facing
objects: they erase to the same direct-source stable data and package on both
branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1540 reuses the W1539 semantic-adapter comparison surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputW1539

/-- Closed-map W1539 semantic input is the W1534 direct-source semantic input. -/
theorem closedMapW829StableSemanticAdapterInput_eq_W1534SemanticInputW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterInputW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapOrdinaryStableSemanticInputW829DirectSourceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1539 semantic input is the W1534 direct-source semantic input. -/
theorem closedEmbeddingW829StableSemanticAdapterInput_eq_W1534SemanticInputW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829StableSemanticAdapterInputW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingOrdinaryStableSemanticInputW829DirectSourceW1534
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map W1539 accepted evidence is the W1534 accepted evidence. -/
theorem closedMapW829StableSemanticAdapterAccepted_eq_W1534AcceptedW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterAcceptedW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapAcceptedStableBoundedDerivedInfinityCategoryW829DirectSourceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1539 accepted evidence is the W1534 accepted evidence. -/
theorem closedEmbeddingW829StableSemanticAdapterAccepted_eq_W1534AcceptedW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829StableSemanticAdapterAcceptedW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingAcceptedStableBoundedDerivedInfinityCategoryW829DirectSourceW1534
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map W1539 certificate is the W1534 stable four-projection certificate. -/
theorem closedMapW829StableSemanticAdapterCertificate_eq_W1534CertificateW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapW829StableSemanticAdapterAcceptedW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider).certificate =
      closedMapStableFourProjectionCertificateW829DirectSourceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1539 certificate is the W1534 stable four-projection certificate. -/
theorem closedEmbeddingW829StableSemanticAdapterCertificate_eq_W1534CertificateW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingW829StableSemanticAdapterAcceptedW1539
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).certificate =
      closedEmbeddingStableFourProjectionCertificateW829DirectSourceW1534
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- Closed-map W1539 semantic-adapter package is the W1534 accepted package. -/
theorem closedMapW829StableSemanticAdapterPackage_eq_W1534AcceptedPackageW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829StableSemanticAdapterPackageW1539
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Closed-embedding W1539 semantic-adapter package is the W1534 accepted package. -/
theorem closedEmbeddingW829StableSemanticAdapterPackage_eq_W1534AcceptedPackageW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
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

/-- Reprojecting the closed-map W1539 package recovers W1535 accepted projections. -/
theorem
    closedMapW829StableSemanticAdapterPackageProjectionFacts_eq_W1535AcceptedProjectionFactsW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedMapW829StableSemanticAdapterPackageW1539
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- Reprojecting the closed-embedding W1539 package recovers W1535 projections. -/
theorem
    closedEmbeddingW829StableSemanticAdapterPackageProjectionFacts_eq_W1535AcceptedProjectionFactsW1540
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputW1540)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    stableProjectionFactsOfBoundedDerivedPackageW1535
        (closedEmbeddingW829StableSemanticAdapterPackageW1539
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1540 names the erasure comparisons between W1534 and W1539. -/
def w829StableCertificateSemanticAdapterComparisonFactNamesW1540 : List String :=
  ["closed-map W1539 semantic input equals W1534 semantic input",
    "closed-embedding W1539 semantic input equals W1534 semantic input",
    "closed-map W1539 accepted evidence equals W1534 accepted evidence",
    "closed-embedding W1539 accepted evidence equals W1534 accepted evidence",
    "closed-map W1539 certificate equals W1534 certificate",
    "closed-embedding W1539 certificate equals W1534 certificate",
    "closed-map W1539 package equals W1534 accepted package",
    "closed-embedding W1539 package equals W1534 accepted package",
    "closed-map W1539 reprojected fields equal W1535 accepted projections",
    "closed-embedding W1539 reprojected fields equal W1535 accepted projections"]

theorem w829StableCertificateSemanticAdapterComparisonFactNamesW1540_count :
    w829StableCertificateSemanticAdapterComparisonFactNamesW1540.length = 10 :=
  rfl

/-- W1540 keeps the W1539 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableSemanticAdapterComparisonInputNamesW1539_count

/-- Current W1540 nonterminal state after aligning the W1534 and W1539 routes. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  remainingInputs : List String
  comparisonFacts : List String
  productSuccessClaimed : Bool

/-- W1540 records that the W1534 certificate route and W1539 adapter route agree. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540
    where
  seed :=
    "w1540-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-certificate-semantic-adapter-comparison"
  declarations :=
    ["closedMapW829StableSemanticAdapterInput_eq_W1534SemanticInputW1540",
      "closedEmbeddingW829StableSemanticAdapterInput_eq_W1534SemanticInputW1540",
      "closedMapW829StableSemanticAdapterAccepted_eq_W1534AcceptedW1540",
      "closedEmbeddingW829StableSemanticAdapterAccepted_eq_W1534AcceptedW1540",
      "closedMapW829StableSemanticAdapterCertificate_eq_W1534CertificateW1540",
      "closedEmbeddingW829StableSemanticAdapterCertificate_eq_W1534CertificateW1540",
      "closedMapW829StableSemanticAdapterPackage_eq_W1534AcceptedPackageW1540",
      "closedEmbeddingW829StableSemanticAdapterPackage_eq_W1534AcceptedPackageW1540",
      "closedMapW829StableSemanticAdapterPackageProjectionFacts_eq_W1535AcceptedProjectionFactsW1540",
      "closedEmbeddingW829StableSemanticAdapterPackageProjectionFacts_eq_W1535AcceptedProjectionFactsW1540",
      "w829StableCertificateSemanticAdapterComparisonFactNamesW1540_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540_count"]
  comparisonResult :=
    "proved: W1534 stable-certificate and accepted-route evidence erase \
      definitionally to the same W1539 semantic-adapter input, accepted \
      evidence, package, and W1535 projections on both branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540
  comparisonFacts := w829StableCertificateSemanticAdapterComparisonFactNamesW1540
  productSuccessClaimed := false

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.productSuccessClaimed =
      false :=
  rfl

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_remainingInputs_eq_inputNamesW1544 :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.remainingInputs =
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540 :=
  rfl

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_remainingInputs_countW1544 :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.remainingInputs.length =
      74 := by
  simpa [
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonInputNamesW1540_count

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_comparisonFacts_eq_factNamesW1544 :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.comparisonFacts =
      w829StableCertificateSemanticAdapterComparisonFactNamesW1540 :=
  rfl

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_comparisonFacts_countW1544 :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.comparisonFacts.length =
      10 := by
  simpa [
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540]
    using w829StableCertificateSemanticAdapterComparisonFactNamesW1540_count

theorem currentW1540W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparison_declarations_countW1544 :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateSemanticAdapterComparisonStateW1540.declarations.length =
      12 :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
