import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829StableProjectionFactsDirectSourceComparisonW1536

/-!
W1537 turns the W1536 direct-source stable projections into the instance-family
shape required by `boundedDerivedInfinityCategoryOfMetrizableStableInstances`.
This is still nonterminal because the data are parameterized by the W987 ledger,
but it records that the direct-source branch supplies the stable typeclass route
fields rather than only package projections.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1537 reuses the W1536 direct-source comparison surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputW1536

/-- Direct-source stable facts arranged as the `Dbounded` stable instance families. -/
structure W829DirectSourceStableInstanceFactsW1537 : Type 2 where
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

/-- Convert direct-source projection facts into stable instance-family facts. -/
noncomputable def stableInstanceFactsOfDirectSourceProjectionFactsW1537
    (facts : W829AcceptedDirectSourceStableProjectionFactsW1535) :
    W829DirectSourceStableInstanceFactsW1537 where
  preadditive := facts.preadditive
  finiteLimits := facts.finiteLimits
  finiteColimits := facts.finiteColimits
  zeroObject := facts.zeroObject
  shiftAdditiveAll := facts.shiftAdditiveAll
  suspensionAdditive := facts.suspensionAdditive
  pretriangulated := facts.pretriangulated
  triangulated := facts.triangulated

/-- Closed-map direct-source stable instance facts from W1536 projections. -/
noncomputable def closedMapW829DirectSourceStableInstanceFactsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    W829DirectSourceStableInstanceFactsW1537 :=
  stableInstanceFactsOfDirectSourceProjectionFactsW1537
    (closedMapW829DirectSourceStableProjectionFactsW1536
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- Closed-embedding direct-source stable instance facts from W1536 projections. -/
noncomputable def closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    W829DirectSourceStableInstanceFactsW1537 :=
  stableInstanceFactsOfDirectSourceProjectionFactsW1537
    (closedEmbeddingW829DirectSourceStableProjectionFactsW1536
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- Build the typeclass-route stable package from direct-source stable instance facts. -/
noncomputable def boundedDerivedInfinityCategoryOfStableInstanceFactsW1537
    (facts : W829DirectSourceStableInstanceFactsW1537) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
  letI : HasFiniteLimits (Dbounded MetrizableLCA.{0}) := facts.finiteLimits
  letI : HasFiniteColimits (Dbounded MetrizableLCA.{0}) := facts.finiteColimits
  letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
  letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
    facts.shiftAdditiveAll
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
  letI : IsTriangulated (Dbounded MetrizableLCA.{0}) := facts.triangulated
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances

/-- Closed-map typeclass-route stable package from W1537 instance facts. -/
noncomputable def closedMapW829DirectSourceStableInstancePackageW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfStableInstanceFactsW1537
    (closedMapW829DirectSourceStableInstanceFactsW1537
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- Closed-embedding typeclass-route stable package from W1537 instance facts. -/
noncomputable def closedEmbeddingW829DirectSourceStableInstancePackageW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfStableInstanceFactsW1537
    (closedEmbeddingW829DirectSourceStableInstanceFactsW1537
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

theorem closedMapW829DirectSourceStableInstancePreadditiveW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (Preadditive (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).preadditive⟩

theorem closedEmbeddingW829DirectSourceStableInstancePreadditiveW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (Preadditive (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).preadditive⟩

theorem closedMapW829DirectSourceStableInstanceFiniteLimitsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteLimits⟩

theorem closedEmbeddingW829DirectSourceStableInstanceFiniteLimitsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteLimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).finiteLimits⟩

theorem closedMapW829DirectSourceStableInstanceFiniteColimitsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteColimits⟩

theorem closedEmbeddingW829DirectSourceStableInstanceFiniteColimitsW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasFiniteColimits (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).finiteColimits⟩

theorem closedMapW829DirectSourceStableInstanceZeroObjectW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Nonempty (HasZeroObject (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).zeroObject⟩

theorem closedEmbeddingW829DirectSourceStableInstanceZeroObjectW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Nonempty (HasZeroObject (Dbounded MetrizableLCA.{0})) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).zeroObject⟩

theorem closedMapW829DirectSourceStableInstanceShiftAdditiveAllW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableInstanceFactsW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    Nonempty (∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).shiftAdditiveAll⟩

theorem closedEmbeddingW829DirectSourceStableInstanceShiftAdditiveAllW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableInstanceFactsW1537
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    Nonempty (∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).shiftAdditiveAll⟩

theorem closedMapW829DirectSourceStableInstanceSuspensionAdditiveW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableInstanceFactsW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Nonempty ((shiftFunctor (Dbounded MetrizableLCA.{0}) (1 : ℤ)).Additive) :=
  ⟨(closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).suspensionAdditive⟩

theorem closedEmbeddingW829DirectSourceStableInstanceSuspensionAdditiveW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableInstanceFactsW1537
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Nonempty ((shiftFunctor (Dbounded MetrizableLCA.{0}) (1 : ℤ)).Additive) :=
  ⟨(closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).suspensionAdditive⟩

@[reducible] noncomputable def closedMapW829DirectSourceStableInstancePretriangulatedW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableInstanceFactsW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).pretriangulated

@[reducible] noncomputable def
    closedEmbeddingW829DirectSourceStableInstancePretriangulatedW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableInstanceFactsW1537
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).pretriangulated

@[reducible] noncomputable def closedMapW829DirectSourceStableInstanceTriangulatedW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let facts :=
      closedMapW829DirectSourceStableInstanceFactsW1537
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedMapW829DirectSourceStableInstanceFactsW1537
    input globalClosedMapComponents mappedCokernelClosedMapProvider).triangulated

@[reducible] noncomputable def
    closedEmbeddingW829DirectSourceStableInstanceTriangulatedW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let facts :=
      closedEmbeddingW829DirectSourceStableInstanceFactsW1537
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := facts.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := facts.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      facts.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := facts.pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0}) :=
  (closedEmbeddingW829DirectSourceStableInstanceFactsW1537
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).triangulated

theorem closedMapW829DirectSourceStableInstancePackageCarrierW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapW829DirectSourceStableInstancePackageW1537
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).quasicategoryCarrier =
      rfl :=
  rfl

theorem closedEmbeddingW829DirectSourceStableInstancePackageCarrierW1537
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputW1537)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingW829DirectSourceStableInstancePackageW1537
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).quasicategoryCarrier =
      rfl :=
  rfl

/-- W1537 names the stable instance families supplied by direct-source projections. -/
def w829StableInstanceFactNamesFromDirectSourceW1537 : List String :=
  ["Preadditive (Dbounded MetrizableLCA)",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "HasZeroObject (Dbounded MetrizableLCA)",
    "forall n, (shiftFunctor (Dbounded MetrizableLCA) n).Additive",
    "(shiftFunctor (Dbounded MetrizableLCA) 1).Additive",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)",
    "typeclass-route BoundedDerivedInfinityCategory package"]

theorem w829StableInstanceFactNamesFromDirectSourceW1537_count :
    w829StableInstanceFactNamesFromDirectSourceW1537.length = 9 :=
  rfl

/-- W1537 keeps the W1536 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableProjectionFactsDirectSourceComparisonInputNamesW1536_count

/-- Current W1537 nonterminal state after arranging direct-source fields as stable instances. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceStateW1537 :
    Type where
  seed : String
  declarations : List String
  instanceResult : String
  remainingInputs : List String
  stableInstanceFacts : List String
  productSuccessClaimed : Bool

/-- W1537 records stable instance-family evidence from W1536 direct-source projections. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceStateW1537 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceStateW1537
    where
  seed :=
    "w1537-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-instance-facts-from-direct-source"
  declarations :=
    ["W829DirectSourceStableInstanceFactsW1537",
      "stableInstanceFactsOfDirectSourceProjectionFactsW1537",
      "closedMapW829DirectSourceStableInstanceFactsW1537",
      "closedEmbeddingW829DirectSourceStableInstanceFactsW1537",
      "boundedDerivedInfinityCategoryOfStableInstanceFactsW1537",
      "closedMapW829DirectSourceStableInstancePackageW1537",
      "closedEmbeddingW829DirectSourceStableInstancePackageW1537",
      "closedMapW829DirectSourceStableInstancePreadditiveW1537",
      "closedEmbeddingW829DirectSourceStableInstancePreadditiveW1537",
      "closedMapW829DirectSourceStableInstanceFiniteLimitsW1537",
      "closedEmbeddingW829DirectSourceStableInstanceFiniteLimitsW1537",
      "closedMapW829DirectSourceStableInstanceFiniteColimitsW1537",
      "closedEmbeddingW829DirectSourceStableInstanceFiniteColimitsW1537",
      "closedMapW829DirectSourceStableInstanceZeroObjectW1537",
      "closedEmbeddingW829DirectSourceStableInstanceZeroObjectW1537",
      "closedMapW829DirectSourceStableInstanceShiftAdditiveAllW1537",
      "closedEmbeddingW829DirectSourceStableInstanceShiftAdditiveAllW1537",
      "closedMapW829DirectSourceStableInstanceSuspensionAdditiveW1537",
      "closedEmbeddingW829DirectSourceStableInstanceSuspensionAdditiveW1537",
      "closedMapW829DirectSourceStableInstancePretriangulatedW1537",
      "closedEmbeddingW829DirectSourceStableInstancePretriangulatedW1537",
      "closedMapW829DirectSourceStableInstanceTriangulatedW1537",
      "closedEmbeddingW829DirectSourceStableInstanceTriangulatedW1537",
      "closedMapW829DirectSourceStableInstancePackageCarrierW1537",
      "closedEmbeddingW829DirectSourceStableInstancePackageCarrierW1537",
      "w829StableInstanceFactNamesFromDirectSourceW1537_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537_count"]
  instanceResult :=
    "proved: W1536 direct-source projections supply the stable instance-family \
      shape required by the typeclass-route bounded-derived package on both \
      branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceInputNamesW1537
  stableInstanceFacts := w829StableInstanceFactNamesFromDirectSourceW1537
  productSuccessClaimed := false

theorem currentW1537W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSource_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableInstanceFactsFromDirectSourceStateW1537.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
