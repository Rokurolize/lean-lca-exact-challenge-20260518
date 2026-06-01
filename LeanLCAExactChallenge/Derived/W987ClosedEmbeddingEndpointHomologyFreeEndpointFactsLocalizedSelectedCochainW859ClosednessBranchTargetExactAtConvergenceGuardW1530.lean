import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW860EndpointLocalizedTargetExactAtConvergenceGuardW1529

/-!
W1530 makes the W859 closedness-branch target-ExactAt leg explicit for the
W1529 W987 surface. W1529 names the W860 endpoint-localized target-ExactAt data;
W1530 records the induced W859 data, the W832 target-ExactAt data underneath it,
and the direct-calculus route through both surfaces.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1530 reuses the W1529 W860 endpoint-localized target-ExactAt surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputW1529

/-- W1530 closed-map W859 data from the W1529 W860 branch. -/
def closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859 :=
  closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
    (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1530 closed-embedding W859 data from the W1529 W860 branch. -/
def closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859 :=
  closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
    (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1530 closed-map W832 target-ExactAt data from the W859 branch. -/
def closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableTargetExactAtLeftCalculusDataW832 :=
  targetExactAtLeftCalculusDataOfClosednessBranchW859
    (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1530 closed-embedding W832 target-ExactAt data from the W859 branch. -/
def closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableTargetExactAtLeftCalculusDataW832 :=
  targetExactAtLeftCalculusDataOfClosednessBranchW859
    (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1530 closed-map W859 closedness is projected from W1529 W860. -/
theorem w1530ClosedMapClosednessFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).closednessData =
      (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).closednessData :=
  rfl

/-- W1530 closed-embedding W859 closedness is projected from W1529 W860. -/
theorem w1530ClosedEmbeddingClosednessFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).closednessData =
      (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).closednessData :=
  rfl

/-- W1530 closed-map W859 endpoint facts are induced by W1529 W860. -/
theorem w1530ClosedMapEndpointFactsFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).endpointExactAtTopologyFacts =
      endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).endpointLocalizedRightAdjointData :=
  rfl

/-- W1530 closed-embedding W859 endpoint facts are induced by W1529 W860. -/
theorem w1530ClosedEmbeddingEndpointFactsFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).endpointExactAtTopologyFacts =
      endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).endpointLocalizedRightAdjointData :=
  rfl

/-- W1530 closed-map W859 target-ExactAt payload is the W1529 W860 payload. -/
theorem w1530ClosedMapTargetExactAtPayloadFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1530 closed-embedding W859 target-ExactAt payload is the W1529 W860 payload. -/
theorem w1530ClosedEmbeddingTargetExactAtPayloadFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1530 closed-map W859 localized-right-adjoint data is induced by W1529 W860. -/
theorem w1530ClosedMapLocalizedRightAdjointFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).endpointLocalizedRightAdjointData :=
  rfl

/-- W1530 closed-embedding W859 localized-right-adjoint data is induced by W1529 W860. -/
theorem w1530ClosedEmbeddingLocalizedRightAdjointFieldW860W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).endpointLocalizedRightAdjointData :=
  rfl

/-- W1530 closed-map W832 closed-range endpoint topology is the W859 reconstruction. -/
theorem w1530ClosedMapW832ClosedRangeEndpointTopologyFieldW859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).closedRangeEndpointTopology =
      closedRangeEndpointTopologyOfClosednessBranchW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).closednessData
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).endpointExactAtTopologyFacts :=
  rfl

/-- W1530 closed-embedding W832 closed-range endpoint topology is the W859 reconstruction. -/
theorem w1530ClosedEmbeddingW832ClosedRangeEndpointTopologyFieldW859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).closedRangeEndpointTopology =
      closedRangeEndpointTopologyOfClosednessBranchW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).closednessData
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).endpointExactAtTopologyFacts :=
  rfl

/-- W1530 closed-map W860 direct route is the W859 direct route. -/
theorem w1530ClosedMapDirectCalculusRunsThroughW859W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1530 closed-embedding W860 direct route is the W859 direct route. -/
theorem w1530ClosedEmbeddingDirectCalculusRunsThroughW859W860
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1530 closed-map W859 direct route is the W832 direct route. -/
theorem w1530ClosedMapDirectCalculusRunsThroughW832W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1530 closed-embedding W859 direct route is the W832 direct route. -/
theorem w1530ClosedEmbeddingDirectCalculusRunsThroughW832W859
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1530 composes the closed-map W1519/W1529 direct path through W859. -/
theorem w1530ClosedMapDirectCalculusRunsThroughW859W1519W1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedMapEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1529ClosedMapDirectCalculusRunsThroughW860W1519W1528
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1530ClosedMapDirectCalculusRunsThroughW859W860
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1530 composes the closed-embedding W1519/W1529 direct path through W859. -/
theorem w1530ClosedEmbeddingDirectCalculusRunsThroughW859W1519W1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
        (closedEmbeddingEndpointLocalizedTargetExactAtDataOfW860ConvergenceW1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1529ClosedEmbeddingDirectCalculusRunsThroughW860W1519W1528
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1530ClosedEmbeddingDirectCalculusRunsThroughW859W860
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider

/-- W1530 composes the closed-map W1519/W1529 direct path through W832. -/
theorem w1530ClosedMapDirectCalculusRunsThroughW832W1519W1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1530ClosedMapDirectCalculusRunsThroughW859W1519W1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1530ClosedMapDirectCalculusRunsThroughW832W859
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1530 composes the closed-embedding W1519/W1529 direct path through W832. -/
theorem w1530ClosedEmbeddingDirectCalculusRunsThroughW832W1519W1529
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
        (closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1530ClosedEmbeddingDirectCalculusRunsThroughW859W1519W1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1530ClosedEmbeddingDirectCalculusRunsThroughW832W859
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider

/-- W1530 keeps the W1529 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W860EndpointLocalizedTargetExactAtConvergenceInputNamesW1529_count

/-- Current W1530 nonterminal W859 closedness-branch target-ExactAt state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceStateW1530 :
    Type where
  seed : String
  declarations : List String
  closednessBranchResult : String
  w832Result : String
  directCalculusResult : String
  remainingInputs : List String
  w859RemainingInputs : List String
  w832RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1530 records the W1529-to-W859 and W859-to-W832 bridges. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceStateW1530 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceStateW1530 where
  seed :=
    "w1530-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w859-closedness-branch-target-exact-at-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530",
      "closedMapClosednessBranchTargetExactAtDataOfW859ConvergenceW1530",
      "closedEmbeddingClosednessBranchTargetExactAtDataOfW859ConvergenceW1530",
      "closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530",
      "closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530",
      "w1530ClosedMapClosednessFieldW860W859",
      "w1530ClosedEmbeddingClosednessFieldW860W859",
      "w1530ClosedMapEndpointFactsFieldW860W859",
      "w1530ClosedEmbeddingEndpointFactsFieldW860W859",
      "w1530ClosedMapTargetExactAtPayloadFieldW860W859",
      "w1530ClosedEmbeddingTargetExactAtPayloadFieldW860W859",
      "w1530ClosedMapLocalizedRightAdjointFieldW860W859",
      "w1530ClosedEmbeddingLocalizedRightAdjointFieldW860W859",
      "w1530ClosedMapW832ClosedRangeEndpointTopologyFieldW859",
      "w1530ClosedEmbeddingW832ClosedRangeEndpointTopologyFieldW859",
      "w1530ClosedMapDirectCalculusRunsThroughW859W860",
      "w1530ClosedEmbeddingDirectCalculusRunsThroughW859W860",
      "w1530ClosedMapDirectCalculusRunsThroughW832W859",
      "w1530ClosedEmbeddingDirectCalculusRunsThroughW832W859",
      "w1530ClosedMapDirectCalculusRunsThroughW859W1519W1529",
      "w1530ClosedEmbeddingDirectCalculusRunsThroughW859W1519W1529",
      "w1530ClosedMapDirectCalculusRunsThroughW832W1519W1529",
      "w1530ClosedEmbeddingDirectCalculusRunsThroughW832W1519W1529",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530_count"]
  closednessBranchResult :=
    "proved: W1529 closed-map and closed-embedding W860 data assemble W859 \
      closedness-branch target-ExactAt data"
  w832Result :=
    "proved: W859 data expose the W832 target-ExactAt left-calculus data \
      underneath the W987 route"
  directCalculusResult :=
    "proved: W1519/W1529 direct-calculus paths compose through W859 and W832 \
      on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530
  w859RemainingInputs :=
    closednessBranchTargetExactAtStableRouteExpandedInputNamesW859
  w832RemainingInputs :=
    targetExactAtLeftCalculusExpandedRequiredFieldNamesW832
  productSuccessClaimed := false

theorem currentW1530W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceStateW1530.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
