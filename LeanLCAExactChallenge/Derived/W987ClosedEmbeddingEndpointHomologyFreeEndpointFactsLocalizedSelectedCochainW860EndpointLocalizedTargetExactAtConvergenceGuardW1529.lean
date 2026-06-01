import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW862ConcreteLeavesTargetExactAtConvergenceGuardW1528

/-!
W1529 makes the W860 endpoint-localized target-ExactAt leg explicit for the
W1528 W987 surface. W1528 names the W861 concrete-leaves target-ExactAt data;
W1529 records the induced W860 data and the direct-calculus route through W860.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1529 reuses the W1528 W862 concrete-leaves target-ExactAt surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputW1528

/-- W1529 closed-map W860 data from the W1528 W861 branch. -/
def closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860 :=
  endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
    (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1529 closed-embedding W860 data from the W1528 W861 branch. -/
def closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860 :=
  endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
    (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1529 closed-map W860 closedness is projected from the W1528 W861 leaves. -/
theorem w1529ClosedMapClosednessFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).closednessData =
      (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).concreteLeaves.diagramAndMappedCokernelClosednessData :=
  rfl

/-- W1529 closed-embedding W860 closedness is projected from the W1528 W861 leaves. -/
theorem w1529ClosedEmbeddingClosednessFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).closednessData =
      (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).concreteLeaves.diagramAndMappedCokernelClosednessData :=
  rfl

/-- W1529 closed-map W860 endpoint/localized data is projected from W1528 W861. -/
theorem w1529ClosedMapEndpointLocalizedFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).endpointLocalizedRightAdjointData =
      endpointLocalizedRightAdjointData_of_concreteLeavesW733
        (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).concreteLeaves :=
  rfl

/--
W1529 closed-embedding W860 endpoint/localized data is projected from W1528
W861.
-/
theorem w1529ClosedEmbeddingEndpointLocalizedFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).endpointLocalizedRightAdjointData =
      endpointLocalizedRightAdjointData_of_concreteLeavesW733
        (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).concreteLeaves :=
  rfl

/-- W1529 closed-map W860 payload is the W1528 W861 payload. -/
theorem w1529ClosedMapTargetExactAtPayloadFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedMapConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1529 closed-embedding W860 payload is the W1528 W861 payload. -/
theorem w1529ClosedEmbeddingTargetExactAtPayloadFieldW861W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedEmbeddingConcreteLeavesTargetExactAtDataOfW862ConvergenceW1528
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1529 exposes the closed-map W862 direct route as the W860 direct route. -/
theorem w1529ClosedMapDirectCalculusRunsThroughW860W862
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1529 exposes the closed-embedding W862 direct route as the W860 direct route. -/
theorem w1529ClosedEmbeddingDirectCalculusRunsThroughW860W862
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1529 composes the closed-map W1519/W1528 direct path through W860. -/
theorem w1529ClosedMapDirectCalculusRunsThroughW860W1519W1528
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1528ClosedMapDirectCalculusRunsThroughW862W1519W1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1529ClosedMapDirectCalculusRunsThroughW860W862
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1529 composes the closed-embedding W1519/W1528 direct path through W860. -/
theorem w1529ClosedEmbeddingDirectCalculusRunsThroughW860W1519W1528
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1528ClosedEmbeddingDirectCalculusRunsThroughW862W1519W1527
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1529ClosedEmbeddingDirectCalculusRunsThroughW860W862
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1529 keeps the W1528 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W862ConcreteLeavesTargetExactAtConvergenceInputNamesW1528_count

/-- Current W1529 nonterminal W860 endpoint-localized target-ExactAt state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceStateW1529 :
    Type where
  seed : String
  declarations : List String
  endpointLocalizedResult : String
  payloadResult : String
  w860Result : String
  remainingInputs : List String
  w860RemainingInputs : List String
  w859RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1529 records the W1528-to-W860 endpoint-localized target-ExactAt bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceStateW1529 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceStateW1529 where
  seed :=
    "w1529-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w860-endpoint-localized-target-exact-at-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529",
      "closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529",
      "closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529",
      "w1529ClosedMapClosednessFieldW861W860",
      "w1529ClosedEmbeddingClosednessFieldW861W860",
      "w1529ClosedMapEndpointLocalizedFieldW861W860",
      "w1529ClosedEmbeddingEndpointLocalizedFieldW861W860",
      "w1529ClosedMapTargetExactAtPayloadFieldW861W860",
      "w1529ClosedEmbeddingTargetExactAtPayloadFieldW861W860",
      "w1529ClosedMapDirectCalculusRunsThroughW860W862",
      "w1529ClosedEmbeddingDirectCalculusRunsThroughW860W862",
      "w1529ClosedMapDirectCalculusRunsThroughW860W1519W1528",
      "w1529ClosedEmbeddingDirectCalculusRunsThroughW860W1519W1528",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529_count"]
  endpointLocalizedResult :=
    "proved: W1528 closed-map and closed-embedding W861 data assemble W860 \
      endpoint-localized target-ExactAt data"
  payloadResult :=
    "proved: W1528 W861 data supply the W860 target-ExactAt payload"
  w860Result :=
    "proved: W1519/W1528 direct-calculus paths compose through W862 to W860 \
      on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529
  w860RemainingInputs :=
    endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860
  w859RemainingInputs :=
    closednessBranchTargetExactAtStableRouteExpandedInputNamesW859
  productSuccessClaimed := false

theorem currentW1529W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceStateW1529.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
