import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableProjectionFactsFromAcceptedDirectSourceW1535

/-!
W1536 compares the W1535 accepted-package projections with the underlying
W1533 direct-source stable package. The accepted W1534 guard does not alter the
bounded-derived package; this file records that erasure and exposes direct
projection facts for both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1536 reuses the W1535 projection surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535

/-- W1536 closed-map direct-source projection facts, bypassing the accepted-package wrapper. -/
noncomputable def closedMapW829DirectSourceStableProjectionFactsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    W829AcceptedDirectSourceStableProjectionFactsW1535 :=
  stableProjectionFactsOfBoundedDerivedPackageW1535
    (closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1536 closed-embedding direct-source projection facts, bypassing the accepted-package wrapper. -/
noncomputable def closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    W829AcceptedDirectSourceStableProjectionFactsW1535 :=
  stableProjectionFactsOfBoundedDerivedPackageW1535
    (closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- The W1534 closed-map accepted package erases to the W1533 direct-source package. -/
theorem closedMapW829AcceptedStablePackage_eq_directSourceW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- The W1534 closed-embedding accepted package erases to the W1533 direct-source package. -/
theorem closedEmbeddingW829AcceptedStablePackage_eq_directSourceW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1535 closed-map accepted projections agree with the W1536 direct-source projections. -/
theorem closedMapW829AcceptedProjectionFacts_eq_directSourceW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapW829DirectSourceStableProjectionFactsW1536
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1535 closed-embedding accepted projections agree with the W1536 direct-source projections. -/
theorem closedEmbeddingW829AcceptedProjectionFacts_eq_directSourceW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingW829DirectSourceStableProjectionFactsW1536
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

theorem closedMapW829DirectSourceCarrierW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.infinityCategory MetrizableLCA.{0} =
      BoundedDerivedOrdinaryQuasicategory MetrizableLCA.{0} :=
  (closedMapW829DirectSourceStableProjectionFactsW1536
    input globalClosedMapComponents mappedCokernelClosedMapProvider).quasicategoryCarrier

theorem closedEmbeddingW829DirectSourceCarrierW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.infinityCategory MetrizableLCA.{0} =
      BoundedDerivedOrdinaryQuasicategory MetrizableLCA.{0} :=
  (closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).quasicategoryCarrier

theorem closedMapW829DirectSourceFiniteLimitsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableProjectionFactsW1536
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteLimits⟩

theorem closedEmbeddingW829DirectSourceFiniteLimitsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).finiteLimits⟩

theorem closedMapW829DirectSourceFiniteColimitsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableProjectionFactsW1536
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteColimits⟩

theorem closedEmbeddingW829DirectSourceFiniteColimitsW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).finiteColimits⟩

@[reducible] noncomputable def closedMapW829DirectSourcePretriangulatedW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableProjectionFactsW1536
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829DirectSourceStableProjectionFactsW1536
    input globalClosedMapComponents mappedCokernelClosedMapProvider).pretriangulated

@[reducible] noncomputable def closedEmbeddingW829DirectSourcePretriangulatedW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableProjectionFactsW1536
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).pretriangulated

@[reducible] noncomputable def closedMapW829DirectSourceTriangulatedW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableProjectionFactsW1536
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829DirectSourceStableProjectionFactsW1536
    input globalClosedMapComponents mappedCokernelClosedMapProvider).triangulated

@[reducible] noncomputable def closedEmbeddingW829DirectSourceTriangulatedW1536
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableProjectionFactsW1536
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829DirectSourceStableProjectionFactsW1536
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).triangulated

/-- W1536 names the direct-source comparison facts that erase the accepted wrapper. -/
def w829StableProjectionDirectSourceComparisonFactNamesW1536 : List String :=
  ["closed-map accepted package equals W1533 direct package",
    "closed-embedding accepted package equals W1533 direct package",
    "closed-map accepted projections equal direct-source projections",
    "closed-embedding accepted projections equal direct-source projections",
    "closed-map direct-source carrier equality",
    "closed-embedding direct-source carrier equality",
    "closed-map direct-source finite limits",
    "closed-embedding direct-source finite limits",
    "closed-map direct-source finite colimits",
    "closed-embedding direct-source finite colimits",
    "closed-map direct-source pretriangulated structure",
    "closed-embedding direct-source pretriangulated structure",
    "closed-map direct-source triangulated structure",
    "closed-embedding direct-source triangulated structure"]

theorem w829StableProjectionDirectSourceComparisonFactNamesW1536_count :
    w829StableProjectionDirectSourceComparisonFactNamesW1536.length = 14 :=
  rfl

/-- W1536 keeps the W1535 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535_count

/-- Current W1536 nonterminal state after comparing accepted and direct-source projections. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonStateW1536 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  remainingInputs : List String
  directProjectionFacts : List String
  productSuccessClaimed : Bool

/-- W1536 records that the accepted wrapper erases to the direct-source stable projections. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonStateW1536 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonStateW1536
    where
  seed :=
    "w1536-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-projection-direct-source-comparison"
  declarations :=
    ["closedMapW829DirectSourceStableProjectionFactsW1536",
      "closedEmbeddingW829DirectSourceStableProjectionFactsW1536",
      "closedMapW829AcceptedStablePackage_eq_directSourceW1536",
      "closedEmbeddingW829AcceptedStablePackage_eq_directSourceW1536",
      "closedMapW829AcceptedProjectionFacts_eq_directSourceW1536",
      "closedEmbeddingW829AcceptedProjectionFacts_eq_directSourceW1536",
      "closedMapW829DirectSourceCarrierW1536",
      "closedEmbeddingW829DirectSourceCarrierW1536",
      "closedMapW829DirectSourceFiniteLimitsW1536",
      "closedEmbeddingW829DirectSourceFiniteLimitsW1536",
      "closedMapW829DirectSourceFiniteColimitsW1536",
      "closedEmbeddingW829DirectSourceFiniteColimitsW1536",
      "closedMapW829DirectSourcePretriangulatedW1536",
      "closedEmbeddingW829DirectSourcePretriangulatedW1536",
      "closedMapW829DirectSourceTriangulatedW1536",
      "closedEmbeddingW829DirectSourceTriangulatedW1536",
      "w829StableProjectionDirectSourceComparisonFactNamesW1536_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536_count"]
  comparisonResult :=
    "proved: the W1534 accepted-package guard erases to the W1533 \
      direct-source stable package, and the W1535 field projections agree \
      with direct-source projection facts on both branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536
  directProjectionFacts := w829StableProjectionDirectSourceComparisonFactNamesW1536
  productSuccessClaimed := false

theorem currentW1536W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonStateW1536.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
