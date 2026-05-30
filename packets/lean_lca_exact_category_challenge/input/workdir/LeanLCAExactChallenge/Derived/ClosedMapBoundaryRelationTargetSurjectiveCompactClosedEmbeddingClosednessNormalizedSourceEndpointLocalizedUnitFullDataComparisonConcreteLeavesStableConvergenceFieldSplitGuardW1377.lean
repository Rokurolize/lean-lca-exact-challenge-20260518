import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataConcreteLeavesSelectedCochainStableConvergenceFieldSplitGuardW1376
import LeanLCAExactChallenge.Derived.W732ComparisonConcreteLeavesStableExactAtRoute

/-!
W1377 records the definitional convergence of the W879/W880/W881/W882
comparison concrete-leaves stable ExactAt route into the selected-cochain and
endpoint-localized route constructors exposed by W1376.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W879 closed-map selected-cochain data is exactly the W851 constructor. -/
theorem w879ClosedMapSelectedCochainDataRunsThroughW851W1377
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    closedMapSelectedCochainDataOfComparisonW879 exactInputs =
      closedMapSelectedCochainDirectSourceDataOfComparisonW851 exactInputs :=
  rfl

/-- W879 closed-embedding selected-cochain data is exactly the W851 constructor. -/
theorem w879ClosedEmbeddingSelectedCochainDataRunsThroughW851W1377
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    closedEmbeddingSelectedCochainDataOfComparisonW879 exactInputs =
      closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851 exactInputs :=
  rfl

/-- W879 closed-map direct calculus delegates to W878 after W851 assembly. -/
theorem w879ClosedMapDirectCalculusRunsThroughW878W1377
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
        exactInputs =
      directBoundedLeftCalculusOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        (closedMapSelectedCochainDataOfComparisonW879 exactInputs) :=
  rfl

/-- W879 closed-embedding direct calculus delegates to W878 after W851 assembly. -/
theorem w879ClosedEmbeddingDirectCalculusRunsThroughW878W1377
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        exactInputs =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        (closedEmbeddingSelectedCochainDataOfComparisonW879 exactInputs) :=
  rfl

/-- W879 closed-map stable package delegates to W878 after W851 assembly. -/
theorem w879ClosedMapStablePackageRunsThroughW878W1377
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
        exactInputs =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainConcreteLeavesStableExactAtW878
        (closedMapSelectedCochainDataOfComparisonW879 exactInputs) :=
  rfl

/-- W879 closed-embedding stable package delegates to W878 after W851 assembly. -/
theorem w879ClosedEmbeddingStablePackageRunsThroughW878W1377
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
        exactInputs =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainConcreteLeavesStableExactAtW878
        (closedEmbeddingSelectedCochainDataOfComparisonW879 exactInputs) :=
  rfl

/-- W880 direct calculus branches through W879 from the W853 closedness branch. -/
theorem w880DirectCalculusRunsThroughW879W1377
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        routeData =
      match routeData.diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          directBoundedLeftCalculusOfClosedMapComparisonConcreteLeavesStableExactAtW879
            (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          directBoundedLeftCalculusOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W880 stable package branches through W879 from the W853 closedness branch. -/
theorem w880StablePackageRunsThroughW879W1377
    (routeData :
      MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853) :
    boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        routeData =
      match routeData.diagramAndMappedCokernelClosednessData with
      | .closedMap globalClosedMapComponents mappedCokernelClosedMapProvider =>
          boundedDerivedInfinityCategoryOfClosedMapComparisonConcreteLeavesStableExactAtW879
            (closedMapExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedMapComponents mappedCokernelClosedMapProvider)
      | .closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider =>
          boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonConcreteLeavesStableExactAtW879
            (closedEmbeddingExactInputsOfHomologyFreeRouteDataW853 routeData
              globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W881 restores W853 data from W874 through the existing endpoint-facts projection. -/
theorem w881HomologyFreeProviderRunsThroughW856W1377
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    homologyFreeRouteDataProviderOfEndpointLocalizedW881 routeData =
      homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
        (endpointFactsRouteDataProviderOfEndpointLocalizedW874 routeData) :=
  rfl

/-- W881 direct calculus delegates to W880 after W874-to-W853 projection. -/
theorem w881DirectCalculusRunsThroughW880W1377
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        routeData =
      directBoundedLeftCalculusOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        (homologyFreeRouteDataProviderOfEndpointLocalizedW881 routeData) :=
  rfl

/-- W881 stable package delegates to W880 after W874-to-W853 projection. -/
theorem w881StablePackageRunsThroughW880W1377
    (routeData :
      MetrizableEndpointLocalizedHomologyFreeSelectedCochainRouteDataProviderW874) :
    boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        routeData =
      boundedDerivedInfinityCategoryOfHomologyFreeComparisonConcreteLeavesStableExactAtW880
        (homologyFreeRouteDataProviderOfEndpointLocalizedW881 routeData) :=
  rfl

/-- W882 restores W874 data from W732 through the existing W875 projection. -/
theorem w882EndpointLocalizedProviderRunsThroughW875W1377
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    endpointLocalizedRouteDataProviderOfW732ForW882 routeData =
      routeDataProviderOfW732W875 routeData :=
  rfl

/-- W882 direct calculus delegates to W881 after W732-to-W874 projection. -/
theorem w882DirectCalculusRunsThroughW881W1377
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    directBoundedLeftCalculusOfW732ComparisonConcreteLeavesStableExactAtW882
        routeData =
      directBoundedLeftCalculusOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        (endpointLocalizedRouteDataProviderOfW732ForW882 routeData) :=
  rfl

/-- W882 stable package delegates to W881 after W732-to-W874 projection. -/
theorem w882StablePackageRunsThroughW881W1377
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    boundedDerivedInfinityCategoryOfW732ComparisonConcreteLeavesStableExactAtW882
        routeData =
      boundedDerivedInfinityCategoryOfEndpointLocalizedComparisonConcreteLeavesStableExactAtW881
        (endpointLocalizedRouteDataProviderOfW732ForW882 routeData) :=
  rfl

/-- W1377 keeps the W879 bundled input count visible. -/
theorem w1377ComparisonConcreteLeavesStableExactAtInputCountMatchesW879 :
    comparisonConcreteLeavesStableExactAtInputNamesW879.length = 1 :=
  comparisonConcreteLeavesStableExactAtInputNamesW879_count

/-- W1377 keeps the W879 expanded W735 branch count visible. -/
theorem w1377ComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW879 :
    comparisonConcreteLeavesStableExactAtExpandedInputNamesW879.length = 9 :=
  comparisonConcreteLeavesStableExactAtExpandedInputNamesW879_count

/-- W1377 keeps the W880 bundled input count visible. -/
theorem w1377HomologyFreeComparisonConcreteLeavesStableExactAtInputCountMatchesW880 :
    homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880.length = 1 :=
  homologyFreeComparisonConcreteLeavesStableExactAtInputNamesW880_count

/-- W1377 keeps the W880 expanded field count visible. -/
theorem w1377HomologyFreeComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW880 :
    homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880.length =
      8 :=
  homologyFreeComparisonConcreteLeavesStableExactAtExpandedInputNamesW880_count

/-- W1377 keeps the W881 bundled input count visible. -/
theorem w1377EndpointLocalizedComparisonConcreteLeavesStableExactAtInputCountMatchesW881 :
    endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881.length =
      1 :=
  endpointLocalizedComparisonConcreteLeavesStableExactAtInputNamesW881_count

/-- W1377 keeps the W881 expanded field count visible. -/
theorem w1377EndpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW881 :
    endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881.length =
      7 :=
  endpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputNamesW881_count

/-- W1377 keeps the W882 bundled input count visible. -/
theorem w1377W732ComparisonConcreteLeavesStableExactAtInputCountMatchesW882 :
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882.length = 1 :=
  w732ComparisonConcreteLeavesStableExactAtInputNamesW882_count

/-- W1377 keeps the W882 expanded input count visible. -/
theorem w1377W732ComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW882 :
    w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882.length = 1 :=
  w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882_count

/-- Current W1377 nonterminal state. -/
structure ComparisonConcreteLeavesStableConvergenceStateW1377 : Type where
  seed : String
  declarations : List String
  comparisonBranchResult : String
  homologyFreeBranchResult : String
  endpointLocalizedProjectionResult : String
  w732ProjectionResult : String
  remainingInputs : List String
  expandedRemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1377 records W879-W882 convergence into the comparison concrete-leaves route chain. -/
def currentComparisonConcreteLeavesStableConvergenceStateW1377 :
    ComparisonConcreteLeavesStableConvergenceStateW1377 where
  seed := "w1377-comparison-concrete-leaves-stable-convergence"
  declarations :=
    ["w879ClosedMapSelectedCochainDataRunsThroughW851W1377",
      "w879ClosedEmbeddingSelectedCochainDataRunsThroughW851W1377",
      "w879ClosedMapDirectCalculusRunsThroughW878W1377",
      "w879ClosedEmbeddingDirectCalculusRunsThroughW878W1377",
      "w879ClosedMapStablePackageRunsThroughW878W1377",
      "w879ClosedEmbeddingStablePackageRunsThroughW878W1377",
      "w880DirectCalculusRunsThroughW879W1377",
      "w880StablePackageRunsThroughW879W1377",
      "w881HomologyFreeProviderRunsThroughW856W1377",
      "w881DirectCalculusRunsThroughW880W1377",
      "w881StablePackageRunsThroughW880W1377",
      "w882EndpointLocalizedProviderRunsThroughW875W1377",
      "w882DirectCalculusRunsThroughW881W1377",
      "w882StablePackageRunsThroughW881W1377",
      "w1377ComparisonConcreteLeavesStableExactAtInputCountMatchesW879",
      "w1377ComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW879",
      "w1377HomologyFreeComparisonConcreteLeavesStableExactAtInputCountMatchesW880",
      "w1377HomologyFreeComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW880",
      "w1377EndpointLocalizedComparisonConcreteLeavesStableExactAtInputCountMatchesW881",
      "w1377EndpointLocalizedComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW881",
      "w1377W732ComparisonConcreteLeavesStableExactAtInputCountMatchesW882",
      "w1377W732ComparisonConcreteLeavesStableExactAtExpandedInputCountMatchesW882"]
  comparisonBranchResult :=
    "proved: W879 builds W847 selected-cochain data from W851 comparison \
      branches and delegates direct calculus/stable package to W878"
  homologyFreeBranchResult :=
    "proved: W880 branches W853 homology-free data into W879 closed-map and \
      closed-embedding comparison concrete-leaves routes"
  endpointLocalizedProjectionResult :=
    "proved: W881 projects W874 endpoint/localized data back to W853 and \
      delegates direct calculus/stable package to W880"
  w732ProjectionResult :=
    "proved: W882 projects W732 route data back to W874 and delegates direct \
      calculus/stable package to W881"
  remainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtInputNamesW882
  expandedRemainingInputs :=
    w732ComparisonConcreteLeavesStableExactAtExpandedInputNamesW882
  productSuccessClaimed := false

theorem currentW1377ComparisonConcreteLeavesStableConvergence_productSuccess :
    currentComparisonConcreteLeavesStableConvergenceStateW1377.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
