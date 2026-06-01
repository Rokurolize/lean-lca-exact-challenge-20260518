import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableCertificateFromDirectSourceW1534

/-!
W1535 unpacks the W1534 accepted stable bounded-derived packages into concrete
field projections of `BoundedDerivedInfinityCategory`. This keeps the route
nonterminal, but moves the W829 stable evidence away from certificate names and
toward the actual package fields consumed by the bounded-derived task.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1535 reuses the W1534 accepted stable-certificate surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateFromDirectSourceInputW1534

/-- Field-level projections of the accepted W829 direct-source stable package. -/
structure W829AcceptedDirectSourceStableProjectionFactsW1535 : Type 2 where
  quasicategoryCarrier :
    Dbounded.infinityCategory MetrizableLCA.{0} =
      BoundedDerivedOrdinaryQuasicategory MetrizableLCA.{0}
  preadditive : Preadditive (Dbounded MetrizableLCA.{0})
  finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0})
  finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0})
  zeroObject : HasZeroObject (Dbounded MetrizableLCA.{0})
  shiftAdditiveAll :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := preadditive
    ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive
  suspensionAdditive :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := preadditive
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      shiftAdditiveAll
    (shiftFunctor (Dbounded MetrizableLCA.{0}) (1 : ℤ)).Additive
  pretriangulated :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0})
  triangulated :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0})

/-- Unpack a bounded-derived stable package into its field-level projections. -/
noncomputable def stableProjectionFactsOfBoundedDerivedPackageW1535
    (package :
      BoundedDerivedInfinityCategory MetrizableLCA.{0}
        (Dbounded.infinityCategory MetrizableLCA.{0})) :
    W829AcceptedDirectSourceStableProjectionFactsW1535 where
  quasicategoryCarrier := package.quasicategoryCarrier
  preadditive := package.preadditive
  finiteLimits := package.finiteLimitInstance
  finiteColimits := package.finiteColimitInstance
  zeroObject := package.zeroObjectInstance
  shiftAdditiveAll := package.shiftAdditiveAll
  suspensionAdditive := package.suspensionAdditive
  pretriangulated := package.pretriangulatedStructure
  triangulated := package.triangulatedStructure

/-- W1535 closed-map field projections from the W1534 accepted direct-source package. -/
noncomputable def closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    W829AcceptedDirectSourceStableProjectionFactsW1535 :=
  stableProjectionFactsOfBoundedDerivedPackageW1535
    (closedMapBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1535 closed-embedding field projections from the W1534 accepted direct-source package. -/
noncomputable def closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    W829AcceptedDirectSourceStableProjectionFactsW1535 :=
  stableProjectionFactsOfBoundedDerivedPackageW1535
    (closedEmbeddingBoundedDerivedInfinityCategoryOfW829AcceptedDirectSourceConvergenceW1534
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

theorem closedMapW829AcceptedDirectSourceCarrierW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.infinityCategory MetrizableLCA.{0} =
      BoundedDerivedOrdinaryQuasicategory MetrizableLCA.{0} :=
  (closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedMapComponents mappedCokernelClosedMapProvider).quasicategoryCarrier

theorem closedEmbeddingW829AcceptedDirectSourceCarrierW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.infinityCategory MetrizableLCA.{0} =
      BoundedDerivedOrdinaryQuasicategory MetrizableLCA.{0} :=
  (closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider).quasicategoryCarrier

theorem closedMapW829AcceptedDirectSourceFiniteLimitsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteLimits⟩

theorem closedEmbeddingW829AcceptedDirectSourceFiniteLimitsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider).finiteLimits⟩

theorem closedMapW829AcceptedDirectSourceFiniteColimitsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteColimits⟩

theorem closedEmbeddingW829AcceptedDirectSourceFiniteColimitsW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider).finiteColimits⟩

@[reducible] noncomputable def closedMapW829AcceptedDirectSourcePretriangulatedW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedMapComponents mappedCokernelClosedMapProvider).pretriangulated

@[reducible] noncomputable def
    closedEmbeddingW829AcceptedDirectSourcePretriangulatedW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider).pretriangulated

@[reducible] noncomputable def closedMapW829AcceptedDirectSourceTriangulatedW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedMapComponents mappedCokernelClosedMapProvider).triangulated

@[reducible] noncomputable def closedEmbeddingW829AcceptedDirectSourceTriangulatedW1535
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputW1535)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider).triangulated

/-- W1535 names the concrete stable package fields exposed from W1534. -/
def w829AcceptedDirectSourceStableProjectionFactNamesW1535 : List String :=
  ["quasicategoryCarrier", "preadditive", "finiteLimits", "finiteColimits",
    "zeroObject", "shiftAdditiveAll", "suspensionAdditive", "pretriangulated",
    "triangulated"]

theorem w829AcceptedDirectSourceStableProjectionFactNamesW1535_count :
    w829AcceptedDirectSourceStableProjectionFactNamesW1535.length = 9 :=
  rfl

/-- W1535 keeps the W1534 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateFromDirectSourceInputNamesW1534

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableCertificateFromDirectSourceInputNamesW1534_count

/-- Current W1535 nonterminal state after exposing W1534 stable package fields. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceStateW1535 :
    Type where
  seed : String
  declarations : List String
  projectionResult : String
  remainingInputs : List String
  stableProjectionFacts : List String
  productSuccessClaimed : Bool

/-- W1535 records field-level projection facts for the accepted W1534 packages. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceStateW1535 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceStateW1535 where
  seed :=
    "w1535-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-projection-facts-from-accepted-direct-source"
  declarations :=
    ["W829AcceptedDirectSourceStableProjectionFactsW1535",
      "stableProjectionFactsOfBoundedDerivedPackageW1535",
      "closedMapW829AcceptedDirectSourceStableProjectionFactsW1535",
      "closedEmbeddingW829AcceptedDirectSourceStableProjectionFactsW1535",
      "closedMapW829AcceptedDirectSourceCarrierW1535",
      "closedEmbeddingW829AcceptedDirectSourceCarrierW1535",
      "closedMapW829AcceptedDirectSourceFiniteLimitsW1535",
      "closedEmbeddingW829AcceptedDirectSourceFiniteLimitsW1535",
      "closedMapW829AcceptedDirectSourceFiniteColimitsW1535",
      "closedEmbeddingW829AcceptedDirectSourceFiniteColimitsW1535",
      "closedMapW829AcceptedDirectSourcePretriangulatedW1535",
      "closedEmbeddingW829AcceptedDirectSourcePretriangulatedW1535",
      "closedMapW829AcceptedDirectSourceTriangulatedW1535",
      "closedEmbeddingW829AcceptedDirectSourceTriangulatedW1535",
      "w829AcceptedDirectSourceStableProjectionFactNamesW1535_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535_count"]
  projectionResult :=
    "proved: the W1534 accepted stable bounded-derived packages expose the \
      actual carrier, finite-limit, finite-colimit, pretriangulated, and \
      triangulated fields on both branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceInputNamesW1535
  stableProjectionFacts := w829AcceptedDirectSourceStableProjectionFactNamesW1535
  productSuccessClaimed := false

theorem currentW1535W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSource_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsFromAcceptedDirectSourceStateW1535.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
