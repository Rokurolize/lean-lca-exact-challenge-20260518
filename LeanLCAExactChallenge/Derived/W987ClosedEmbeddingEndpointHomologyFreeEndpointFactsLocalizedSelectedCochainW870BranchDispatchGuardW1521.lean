import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainConvergenceGuardW1520
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRouteDataHomologyFreeSelectedCochainStableConvergenceFieldSplitGuardW1373

/-!
W1521 specializes the W1520 W872 homology-free selected-cochain providers to
the W1373 W870 branch dispatch. W1520 reaches W872 on closed-map and
closed-embedding branches; W1521 names the corresponding W870 exact-input
branches and composes the W1519/W1520 route through W1373.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1521 reuses the W1520 endpoint-facts/localized selected-cochain surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520

/-- W1521 closed-map W870 exact inputs obtained from the W1520 W853 provider. -/
def closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedMapExactInputsOfHomologyFreeRouteDataW853
    (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)
    globalClosedMapComponents
    mappedCokernelClosedMapProvider

/-- W1521 closed-embedding W870 exact inputs obtained from the W1520 W853 provider. -/
def closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedEmbeddingExactInputsOfHomologyFreeRouteDataW853
    (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)
    globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider

/-- W1521 closed-map W870 exact inputs recover the W1519 W735 branch. -/
theorem w1521ClosedMapW870ExactInputsMatchW1519W735
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1521 closed-embedding W870 exact inputs recover the W1519 W735 branch. -/
theorem w1521ClosedEmbeddingW870ExactInputsMatchW1519W735
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1521 closed-map W853 provider carries the closed-map branch chosen by W1519. -/
theorem w1521ClosedMapHomologyFreeProviderClosednessBranchW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).diagramAndMappedCokernelClosednessData =
      .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1521 closed-embedding W853 provider carries the closed-embedding branch chosen by W1519. -/
theorem w1521ClosedEmbeddingHomologyFreeProviderClosednessBranchW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).diagramAndMappedCokernelClosednessData =
      .closedEmbedding globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1521 closed-map W872 direct calculus dispatches through W870. -/
theorem w1521ClosedMapDirectCalculusRunsThroughW870W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w872DirectCalculusRunsThroughW853BranchAndW870W1373
    (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1521 closed-embedding W872 direct calculus dispatches through W870. -/
theorem w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w872DirectCalculusRunsThroughW853BranchAndW870W1373
    (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1521 closed-map W872 stable package dispatches through W870. -/
theorem w1521ClosedMapStablePackageRunsThroughW870W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w872StablePackageRunsThroughW853BranchAndW870W1373
    (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1521 closed-embedding W872 stable package dispatches through W870. -/
theorem w1521ClosedEmbeddingStablePackageRunsThroughW870W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w872StablePackageRunsThroughW853BranchAndW870W1373
    (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1521 composes the closed-map W1519/W1520 direct calculus path through W870. -/
theorem w1521ClosedMapDirectCalculusRunsThroughW870W1519W1520W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapDirectCalculusRunsThroughW872W1519W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1521ClosedMapDirectCalculusRunsThroughW870W1373
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1521 composes the closed-embedding W1519/W1520 direct calculus path through W870. -/
theorem w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1519W1520W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1519W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1373
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1521 composes the closed-map W1519/W1520 stable path through W870. -/
theorem w1521ClosedMapStablePackageRunsThroughW870W1519W1520W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapStablePackageRunsThroughW872W1519W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1521ClosedMapStablePackageRunsThroughW870W1373
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1521 composes the closed-embedding W1519/W1520 stable path through W870. -/
theorem w1521ClosedEmbeddingStablePackageRunsThroughW870W1519W1520W1373
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingStablePackageRunsThroughW872W1519W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1521ClosedEmbeddingStablePackageRunsThroughW870W1373
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1521 keeps the W1520 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520_count

/-- Current W1521 nonterminal W870 branch-dispatch state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchStateW1521 :
    Type where
  seed : String
  declarations : List String
  branchDispatchResult : String
  stablePackageResult : String
  remainingInputs : List String
  w870RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1521 records the W1520-to-W1373 W870 branch-dispatch bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchStateW1521 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchStateW1521 where
  seed :=
    "w1521-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w870-branch-dispatch"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521",
      "closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521",
      "closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521",
      "w1521ClosedMapW870ExactInputsMatchW1519W735",
      "w1521ClosedEmbeddingW870ExactInputsMatchW1519W735",
      "w1521ClosedMapHomologyFreeProviderClosednessBranchW1520",
      "w1521ClosedEmbeddingHomologyFreeProviderClosednessBranchW1520",
      "w1521ClosedMapDirectCalculusRunsThroughW870W1373",
      "w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1373",
      "w1521ClosedMapStablePackageRunsThroughW870W1373",
      "w1521ClosedEmbeddingStablePackageRunsThroughW870W1373",
      "w1521ClosedMapDirectCalculusRunsThroughW870W1519W1520W1373",
      "w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1519W1520W1373",
      "w1521ClosedMapStablePackageRunsThroughW870W1519W1520W1373",
      "w1521ClosedEmbeddingStablePackageRunsThroughW870W1519W1520W1373",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521_count"]
  branchDispatchResult :=
    "proved: W1520 closed-map and closed-embedding W853 providers expose the \
      matching W870 exact-input branch through the W1373 W872 dispatch"
  stablePackageResult :=
    "proved: W1519/W1520 direct-calculus and stable-package routes compose \
      through W870 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521
  w870RemainingInputs :=
    comparisonSelectedCochainStableExactAtInputNamesW870
  productSuccessClaimed := false

theorem currentW1521W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatch_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchStateW1521.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
