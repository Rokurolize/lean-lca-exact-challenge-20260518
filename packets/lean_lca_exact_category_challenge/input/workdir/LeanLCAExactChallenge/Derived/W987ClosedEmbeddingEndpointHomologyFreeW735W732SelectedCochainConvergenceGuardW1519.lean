import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeSelectedCochainConcreteLeavesConvergenceGuardW1518
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW732W735SelectedCochainStableConvergenceFieldSplitGuardW1375

/-!
W1519 specializes the W1518 W987 selected-cochain concrete-leaves convergence
surface to the existing W1375 W735/W732 selected-cochain guard. W1518 reaches
the W877/W875 route through W733 concrete leaves; W1519 records the parallel
W876 W735-to-W732 route-data construction and the W875 W732-to-W874
endpoint-localized reconstruction on both closed-map and closed-embedding
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

/-- W1519 reuses the W1518 selected-cochain concrete-leaves convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceInputW1518

/-- W1519 exposes the same direct bounded left calculus proof as W1518. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceW1518
    input

/-- W1519 exposes the same bounded derived infinity-category package as W1518. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceW1518
    input

/-- W1519 closed-map W735 exact inputs from the W1518 branch surface. -/
def closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1519 closed-embedding W735 exact inputs from the W1518 branch surface. -/
def closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735 :=
  closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ComparisonConcreteLeavesConvergenceW1517
    input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1519 closed-map W876 route data from the W1518 W735 branch. -/
def routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapW735ForW876
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W876 route data from the W1518 W735 branch. -/
def routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedEmbeddingW735ForW876
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W875 endpoint-localized provider from W876 route data. -/
def endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874 :=
  routeDataProviderOfW732W875
    (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W875 endpoint-localized provider from W876 route data. -/
def endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874 :=
  routeDataProviderOfW732W875
    (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W876 route data agrees with the W1518 W877 concrete-leaf route. -/
theorem w1519ClosedMapW876RouteDataMatchesW1518ConcreteLeavesRoute
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      routeDataProviderOfConcreteLeavesW877
        (concreteLeavesOfClosedMapSelectedCochainOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceW1518
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1519 closed-embedding W876 route data agrees with the W1518 W877 concrete-leaf route. -/
theorem w1519ClosedEmbeddingW876RouteDataMatchesW1518ConcreteLeavesRoute
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      routeDataProviderOfConcreteLeavesW877
        (concreteLeavesOfClosedEmbeddingSelectedCochainOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceW1518
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1519 closed-map W876 route data runs through W855. -/
theorem w1519ClosedMapRouteDataRunsThroughW855W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      closedMapRouteDataProviderOfComparisonBijectivityW855
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w876ClosedMapRouteDataRunsThroughW855W1375
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W876 route data runs through W855. -/
theorem w1519ClosedEmbeddingRouteDataRunsThroughW855W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      closedEmbeddingRouteDataProviderOfComparisonBijectivityW855
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w876ClosedEmbeddingRouteDataRunsThroughW855W1375
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W876 direct calculus delegates to W875. -/
theorem w1519ClosedMapDirectCalculusRunsThroughW875W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapW735W732SelectedCochainStableExactAtW876
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w876ClosedMapDirectCalculusRunsThroughW875W1375
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W876 direct calculus delegates to W875. -/
theorem w1519ClosedEmbeddingDirectCalculusRunsThroughW875W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w876ClosedEmbeddingDirectCalculusRunsThroughW875W1375
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W876 stable package delegates to W875. -/
theorem w1519ClosedMapStablePackageRunsThroughW875W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapW735W732SelectedCochainStableExactAtW876
        (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w876ClosedMapStablePackageRunsThroughW875W1375
    (closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W876 stable package delegates to W875. -/
theorem w1519ClosedEmbeddingStablePackageRunsThroughW875W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
        (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w876ClosedEmbeddingStablePackageRunsThroughW875W1375
    (closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W875 direct calculus delegates to W874. -/
theorem w1519ClosedMapDirectCalculusRunsThroughW874W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w875DirectCalculusRunsThroughW874W1375
    (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W875 direct calculus delegates to W874. -/
theorem w1519ClosedEmbeddingDirectCalculusRunsThroughW874W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w875DirectCalculusRunsThroughW874W1375
    (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 closed-map W875 stable package delegates to W874. -/
theorem w1519ClosedMapStablePackageRunsThroughW874W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w875StablePackageRunsThroughW874W1375
    (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1519 closed-embedding W875 stable package delegates to W874. -/
theorem w1519ClosedEmbeddingStablePackageRunsThroughW874W1375
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w875StablePackageRunsThroughW874W1375
    (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1519 keeps the W1518 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceInputNamesW1518

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SelectedCochainConcreteLeavesConvergenceInputNamesW1518_count

/-- Current W1519 nonterminal W735/W732 selected-cochain convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceStateW1519 :
    Type where
  seed : String
  declarations : List String
  w876RouteDataResult : String
  w875EndpointLocalizedResult : String
  remainingInputs : List String
  w876RemainingInputs : List String
  w875RemainingInputs : List String
  w874RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1519 records the W1518-to-W1375 W735/W732 selected-cochain bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceStateW1519 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceStateW1519 where
  seed :=
    "w1519-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w735-w732-selected-cochain-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519",
      "closedMapExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519",
      "closedEmbeddingExactInputsOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceW1519",
      "routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519",
      "routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519",
      "endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519",
      "endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519",
      "w1519ClosedMapW876RouteDataMatchesW1518ConcreteLeavesRoute",
      "w1519ClosedEmbeddingW876RouteDataMatchesW1518ConcreteLeavesRoute",
      "w1519ClosedMapRouteDataRunsThroughW855W1375",
      "w1519ClosedEmbeddingRouteDataRunsThroughW855W1375",
      "w1519ClosedMapDirectCalculusRunsThroughW875W1375",
      "w1519ClosedEmbeddingDirectCalculusRunsThroughW875W1375",
      "w1519ClosedMapStablePackageRunsThroughW875W1375",
      "w1519ClosedEmbeddingStablePackageRunsThroughW875W1375",
      "w1519ClosedMapDirectCalculusRunsThroughW874W1375",
      "w1519ClosedEmbeddingDirectCalculusRunsThroughW874W1375",
      "w1519ClosedMapStablePackageRunsThroughW874W1375",
      "w1519ClosedEmbeddingStablePackageRunsThroughW874W1375",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519_count"]
  w876RouteDataResult :=
    "proved: W1519 closed-map and closed-embedding W735 branches construct W732 \
      route data through W855 and agree with the W1518 W877 concrete-leaf route"
  w875EndpointLocalizedResult :=
    "proved: W1519 branch W732 route data delegate direct calculus/stable \
      package through W875 to the W874 endpoint-localized selected-cochain route"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519
  w876RemainingInputs :=
    w735W732SelectedCochainStableExactAtInputNamesW876
  w875RemainingInputs :=
    w732SelectedCochainStableExactAtInputNamesW875
  w874RemainingInputs :=
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874
  productSuccessClaimed := false

theorem currentW1519W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceStateW1519.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
