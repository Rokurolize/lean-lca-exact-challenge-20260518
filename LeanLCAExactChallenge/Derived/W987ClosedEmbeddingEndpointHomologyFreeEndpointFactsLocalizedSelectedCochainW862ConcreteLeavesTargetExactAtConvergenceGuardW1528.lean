import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW863TargetHomologyZeroConvergenceGuardW1527

/-!
W1528 makes the W862 concrete-leaves target-ExactAt leg of the W863 route
explicit for the W1527 W987 surface. W1527 names the W839 target-homology-zero
data induced by the W1526 W843 surface; W1528 records the induced W861
concrete-leaves target-ExactAt data and the direct-calculus route through W862.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1528 reuses the W1527 W863 target-homology-zero convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527

/-- W1528 closed-map W861 data from the W1527 W839 branch. -/
def closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861 :=
  concreteLeavesTargetExactAtDataOfClosedMapTargetHomologyZeroW862
    (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1528 closed-embedding W861 data from the W1527 W839 branch. -/
def closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861 :=
  concreteLeavesTargetExactAtDataOfClosedEmbeddingTargetHomologyZeroW862
    (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1528 closed-map W861 concrete leaves are the W855 leaves of the W1521 branch. -/
theorem w1528ClosedMapConcreteLeavesFieldW855W861
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).concreteLeaves =
      closedMapConcreteLeavesOfComparisonBijectivityW855
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/--
W1528 closed-embedding W861 concrete leaves are the W855 leaves of the W1521
branch.
-/
theorem w1528ClosedEmbeddingConcreteLeavesFieldW855W861
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).concreteLeaves =
      closedEmbeddingConcreteLeavesOfComparisonBijectivityW855
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1528 closed-map W861 payload is the W839-to-W785 payload of the W1527 data. -/
theorem w1528ClosedMapTargetExactAtPayloadFieldW839W861
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      targetExactAtPayloadOfClosedMapTargetHomologyZeroW839
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) hT h₁ h₃ :=
  rfl

/--
W1528 closed-embedding W861 payload is the W839-to-W785 payload of the W1527
data.
-/
theorem w1528ClosedEmbeddingTargetExactAtPayloadFieldW839W861
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      targetExactAtPayloadOfClosedEmbeddingTargetHomologyZeroW839
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) hT h₁ h₃ :=
  rfl

/-- W1528 exposes the closed-map W863 direct route as the W862 direct route. -/
theorem w1528ClosedMapDirectCalculusRunsThroughW862W863
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1528 exposes the closed-embedding W863 direct route as the W862 direct route. -/
theorem w1528ClosedEmbeddingDirectCalculusRunsThroughW862W863
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1528 composes the closed-map W1519/W1527 direct path through W862. -/
theorem w1528ClosedMapDirectCalculusRunsThroughW862W1519W1527
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1527ClosedMapDirectCalculusRunsThroughW863W1519W1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1528ClosedMapDirectCalculusRunsThroughW862W863
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1528 composes the closed-embedding W1519/W1527 direct path through W862. -/
theorem w1528ClosedEmbeddingDirectCalculusRunsThroughW862W1519W1527
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1527ClosedEmbeddingDirectCalculusRunsThroughW863W1519W1526
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1528ClosedEmbeddingDirectCalculusRunsThroughW862W863
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1528 keeps the W1527 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527_count

/-- Current W1528 nonterminal W862 concrete-leaves target-ExactAt state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceStateW1528 :
    Type where
  seed : String
  declarations : List String
  concreteLeavesResult : String
  payloadResult : String
  w862Result : String
  remainingInputs : List String
  w862RemainingInputs : List String
  w861RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1528 records the W1527-to-W862 concrete-leaves target-ExactAt bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceStateW1528 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceStateW1528 where
  seed :=
    "w1528-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w862-concrete-leaves-target-exact-at-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528",
      "closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528",
      "closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528",
      "w1528ClosedMapConcreteLeavesFieldW855W861",
      "w1528ClosedEmbeddingConcreteLeavesFieldW855W861",
      "w1528ClosedMapTargetExactAtPayloadFieldW839W861",
      "w1528ClosedEmbeddingTargetExactAtPayloadFieldW839W861",
      "w1528ClosedMapDirectCalculusRunsThroughW862W863",
      "w1528ClosedEmbeddingDirectCalculusRunsThroughW862W863",
      "w1528ClosedMapDirectCalculusRunsThroughW862W1519W1527",
      "w1528ClosedEmbeddingDirectCalculusRunsThroughW862W1519W1527",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528_count"]
  concreteLeavesResult :=
    "proved: W1527 closed-map and closed-embedding W839 data assemble W861 \
      concrete leaves through W855 and W862"
  payloadResult :=
    "proved: W1527 W839 data supply the W861 target-ExactAt payload through W839"
  w862Result :=
    "proved: W1519/W1527 direct-calculus paths compose through W863 to W862 \
      on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528
  w862RemainingInputs :=
    targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862
  w861RemainingInputs :=
    concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861
  productSuccessClaimed := false

theorem currentW1528W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceStateW1528.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
