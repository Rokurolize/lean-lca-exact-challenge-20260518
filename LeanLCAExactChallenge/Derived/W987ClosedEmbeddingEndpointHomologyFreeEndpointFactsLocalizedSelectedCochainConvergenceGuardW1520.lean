import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeW735W732SelectedCochainConvergenceGuardW1519
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointFactsLocalizedSelectedCochainStableConvergenceFieldSplitGuardW1374

/-!
W1520 specializes the W1519 W874 endpoint-localized selected-cochain surface to
the existing W1374 endpoint-facts/localized selected-cochain convergence guard.
W1519 reaches W874 through W735/W732; W1520 records the W874-to-W873
endpoint-facts projection and W873-to-W872 homology-free selected-cochain route
on both closed-map and closed-embedding branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1520 reuses the W1519 W735/W732 selected-cochain convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputW1519

/-- W1520 closed-map W856 endpoint-facts provider from the W1519 W874 surface. -/
def endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856 :=
  endpointFactsRouteDataProviderOfEndpointLocalizedW874
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W856 endpoint-facts provider from the W1519 W874 surface. -/
def endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856 :=
  endpointFactsRouteDataProviderOfEndpointLocalizedW874
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map W853 provider after the W1374 W873-to-W872 projection. -/
def homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W853 provider after the W1374 W873-to-W872 projection. -/
def homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map endpoint-facts provider preserves W1519 boundary data. -/
theorem w1520ClosedMapEndpointFactsProviderBoundaryFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedMapComponents mappedCokernelClosedMapProvider).boundaryData =
      (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
        input globalClosedMapComponents mappedCokernelClosedMapProvider).boundaryData :=
  w874EndpointFactsProviderBoundaryFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding endpoint-facts provider preserves W1519 boundary data. -/
theorem w1520ClosedEmbeddingEndpointFactsProviderBoundaryFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).boundaryData =
      (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).boundaryData :=
  w874EndpointFactsProviderBoundaryFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map endpoint-facts provider preserves W1519 closedness data. -/
theorem w1520ClosedMapEndpointFactsProviderClosednessFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedMapComponents mappedCokernelClosedMapProvider).diagramAndMappedCokernelClosednessData =
      (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
        input globalClosedMapComponents mappedCokernelClosedMapProvider).diagramAndMappedCokernelClosednessData :=
  w874EndpointFactsProviderClosednessFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding endpoint-facts provider preserves W1519 closedness data. -/
theorem w1520ClosedEmbeddingEndpointFactsProviderClosednessFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).diagramAndMappedCokernelClosednessData =
      (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).diagramAndMappedCokernelClosednessData :=
  w874EndpointFactsProviderClosednessFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map endpoint-facts provider builds W856 endpoint facts from W1519 W726 data. -/
theorem w1520ClosedMapEndpointFactsProviderEndpointFactsFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedMapComponents mappedCokernelClosedMapProvider).endpointTopologyFacts =
      endpointTopologyFactsOfEndpointLocalizedW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider).endpointLocalizedRightAdjointData :=
  w874EndpointFactsProviderEndpointFactsFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding endpoint-facts provider builds W856 endpoint facts from W1519 W726 data. -/
theorem w1520ClosedEmbeddingEndpointFactsProviderEndpointFactsFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).endpointTopologyFacts =
      endpointTopologyFactsOfEndpointLocalizedW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).endpointLocalizedRightAdjointData :=
  w874EndpointFactsProviderEndpointFactsFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map endpoint-facts provider projects W1519 W726 data to W721. -/
theorem w1520ClosedMapEndpointFactsProviderLocalizedFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedMapComponents mappedCokernelClosedMapProvider).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider).endpointLocalizedRightAdjointData :=
  w874EndpointFactsProviderLocalizedFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding endpoint-facts provider projects W1519 W726 data to W721. -/
theorem w1520ClosedEmbeddingEndpointFactsProviderLocalizedFieldW1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).endpointLocalizedRightAdjointData :=
  w874EndpointFactsProviderLocalizedFieldW1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map W874 direct calculus delegates to W873. -/
theorem w1520ClosedMapDirectCalculusRunsThroughW873W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w874DirectCalculusRunsThroughW873W1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W874 direct calculus delegates to W873. -/
theorem w1520ClosedEmbeddingDirectCalculusRunsThroughW873W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w874DirectCalculusRunsThroughW873W1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map W874 stable package delegates to W873. -/
theorem w1520ClosedMapStablePackageRunsThroughW873W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w874StablePackageRunsThroughW873W1374
    (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W874 stable package delegates to W873. -/
theorem w1520ClosedEmbeddingStablePackageRunsThroughW873W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w874StablePackageRunsThroughW873W1374
    (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map W873 direct calculus delegates to W872. -/
theorem w1520ClosedMapDirectCalculusRunsThroughW872W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w873DirectCalculusRunsThroughW856W872W1374
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W873 direct calculus delegates to W872. -/
theorem w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w873DirectCalculusRunsThroughW856W872W1374
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 closed-map W873 stable package delegates to W872. -/
theorem w1520ClosedMapStablePackageRunsThroughW872W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w873StablePackageRunsThroughW856W872W1374
    (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1520 closed-embedding W873 stable package delegates to W872. -/
theorem w1520ClosedEmbeddingStablePackageRunsThroughW872W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w873StablePackageRunsThroughW856W872W1374
    (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1520 composes the closed-map W1519 W875 path through W873 to W872. -/
theorem w1520ClosedMapDirectCalculusRunsThroughW872W1519W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1519ClosedMapDirectCalculusRunsThroughW874W1375
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapDirectCalculusRunsThroughW873W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapDirectCalculusRunsThroughW872W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1520 composes the closed-embedding W1519 W875 path through W873 to W872. -/
theorem w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1519W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1519ClosedEmbeddingDirectCalculusRunsThroughW874W1375
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingDirectCalculusRunsThroughW873W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1520 composes the closed-map W1519 stable path through W873 to W872. -/
theorem w1520ClosedMapStablePackageRunsThroughW872W1519W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1519ClosedMapStablePackageRunsThroughW874W1375
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapStablePackageRunsThroughW873W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1520ClosedMapStablePackageRunsThroughW872W1374
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1520 composes the closed-embedding W1519 stable path through W873 to W872. -/
theorem w1520ClosedEmbeddingStablePackageRunsThroughW872W1519W1374
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfEndpointLocalizedHomologyFreeSelectedCochainStableExactAtW874
        (endpointLocalizedRouteDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1519ClosedEmbeddingStablePackageRunsThroughW874W1375
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfEndpointFactsHomologyFreeSelectedCochainStableExactAtW873
        (endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingStablePackageRunsThroughW873W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainStableExactAtW872
        (homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1520ClosedEmbeddingStablePackageRunsThroughW872W1374
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1520 keeps the W1519 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W735W732SelectedCochainConvergenceInputNamesW1519_count

/-- Current W1520 nonterminal endpoint-facts/localized selected-cochain state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceStateW1520 :
    Type where
  seed : String
  declarations : List String
  endpointFactsResult : String
  homologyFreeResult : String
  remainingInputs : List String
  w874RemainingInputs : List String
  w873RemainingInputs : List String
  w872RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1520 records the W1519-to-W1374 endpoint-facts/localized bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceStateW1520 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceStateW1520 where
  seed :=
    "w1520-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-endpoint-facts-localized-selected-cochain-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputW1520",
      "endpointFactsRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520",
      "endpointFactsRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520",
      "homologyFreeRouteDataProviderOfClosedMapEndpointFactsLocalizedSelectedCochainConvergenceW1520",
      "homologyFreeRouteDataProviderOfClosedEmbeddingEndpointFactsLocalizedSelectedCochainConvergenceW1520",
      "w1520ClosedMapEndpointFactsProviderBoundaryFieldW1374",
      "w1520ClosedEmbeddingEndpointFactsProviderBoundaryFieldW1374",
      "w1520ClosedMapEndpointFactsProviderClosednessFieldW1374",
      "w1520ClosedEmbeddingEndpointFactsProviderClosednessFieldW1374",
      "w1520ClosedMapEndpointFactsProviderEndpointFactsFieldW1374",
      "w1520ClosedEmbeddingEndpointFactsProviderEndpointFactsFieldW1374",
      "w1520ClosedMapEndpointFactsProviderLocalizedFieldW1374",
      "w1520ClosedEmbeddingEndpointFactsProviderLocalizedFieldW1374",
      "w1520ClosedMapDirectCalculusRunsThroughW873W1374",
      "w1520ClosedEmbeddingDirectCalculusRunsThroughW873W1374",
      "w1520ClosedMapStablePackageRunsThroughW873W1374",
      "w1520ClosedEmbeddingStablePackageRunsThroughW873W1374",
      "w1520ClosedMapDirectCalculusRunsThroughW872W1374",
      "w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1374",
      "w1520ClosedMapStablePackageRunsThroughW872W1374",
      "w1520ClosedEmbeddingStablePackageRunsThroughW872W1374",
      "w1520ClosedMapDirectCalculusRunsThroughW872W1519W1374",
      "w1520ClosedEmbeddingDirectCalculusRunsThroughW872W1519W1374",
      "w1520ClosedMapStablePackageRunsThroughW872W1519W1374",
      "w1520ClosedEmbeddingStablePackageRunsThroughW872W1519W1374",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520_count"]
  endpointFactsResult :=
    "proved: W1519 closed-map and closed-embedding W874 endpoint-localized \
      providers project through W1374 to W856 endpoint-facts route data"
  homologyFreeResult :=
    "proved: W1520 branch endpoint-facts route data delegate direct calculus \
      and stable package through W873 to the W872 homology-free selected-cochain route"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceInputNamesW1520
  w874RemainingInputs :=
    endpointLocalizedHomologyFreeSelectedCochainStableExactAtInputNamesW874
  w873RemainingInputs :=
    endpointFactsHomologyFreeSelectedCochainStableExactAtInputNamesW873
  w872RemainingInputs :=
    homologyFreeSelectedCochainStableExactAtInputNamesW872
  productSuccessClaimed := false

theorem currentW1520W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3EndpointFactsLocalizedSelectedCochainConvergenceStateW1520.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
