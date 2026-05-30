import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableRoute

/-!
W854 constructs the W853 homology-free selected-cochain provider from existing
route-data evidence instead of accepting it as an opaque input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W854 drops the category-homology payload from W733 concrete leaves while keeping
exactly the branch data consumed by W853.
-/
def homologyFreeSelectedCochainRouteDataProviderOfConcreteLeavesW854
    (leaves :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData :=
    sourceTriangulationData_of_sourceHomologicalTriangulationDataW724
      leaves.sourceHomologicalTriangulationData
  endpointStrictTopologyData := leaves.endpointStrictTopologyData
  localizedRightAdjointData := leaves.localizedRightAdjointData

/--
W854 constructs the W853 provider from one W732 route-data provider by first
projecting the W733 leaves through W763, then dropping the unused homology
payload.
-/
def homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 :=
  homologyFreeSelectedCochainRouteDataProviderOfConcreteLeavesW854
    (boundaryRelationTargetClosednessNormalizedConcreteLeaves_of_routeDataW763
      routeData)

/--
W854 routes W732 data through the constructed W853 provider to produce the
selected-cochain direct-source branch data.
-/
noncomputable def
    selectedCochainDirectSourceDataOfRouteDataViaHomologyFreeW854
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :=
  selectedCochainDirectSourceDataOfHomologyFreeRouteDataW853
    (homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854 routeData)

/-- W854 direct bounded left calculus from W732 data via the constructed W853 provider. -/
theorem directBoundedLeftCalculusOfRouteDataViaHomologyFreeW854
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainW853
    (homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854 routeData)

/--
W854 bounded derived infinity-category package from W732 data via the constructed
W853 provider.
-/
noncomputable def boundedDerivedInfinityCategoryOfRouteDataViaHomologyFreeW854
    (routeData :
      MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainW853
    (homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854 routeData)

def homologyFreeProviderFromRouteDataInputNamesW854 : List String :=
  ["one W732 boundary/relation target/closedness normalized source/endpoint\
      route-data provider"]

theorem homologyFreeProviderFromRouteDataInputNamesW854_count :
    homologyFreeProviderFromRouteDataInputNamesW854.length =
      1 :=
  rfl

structure MetrizableHomologyFreeProviderFromRouteDataStateW854 :
    Type where
  seed : String
  declarations : List String
  providerConstructionResult : String
  selectedCochainResult : String
  leftCalculusResult : String
  stablePackageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableHomologyFreeProviderFromRouteDataStateW854 :
    MetrizableHomologyFreeProviderFromRouteDataStateW854
    where
  seed := "w854-homology-free-provider-from-route-data"
  declarations :=
    ["Dbounded.homologyFreeSelectedCochainRouteDataProviderOfConcreteLeavesW854",
      "Dbounded.homologyFreeSelectedCochainRouteDataProviderOfRouteDataW854",
      "Dbounded.selectedCochainDirectSourceDataOfRouteDataViaHomologyFreeW854",
      "Dbounded.directBoundedLeftCalculusOfRouteDataViaHomologyFreeW854",
      "Dbounded.boundedDerivedInfinityCategoryOfRouteDataViaHomologyFreeW854",
      "Dbounded.homologyFreeProviderFromRouteDataInputNamesW854",
      "Dbounded.homologyFreeProviderFromRouteDataInputNamesW854_count"]
  providerConstructionResult :=
    "proved: W763-projected W733 leaves construct the W853 provider after\
      dropping the category-homology payload"
  selectedCochainResult :=
    "proved: one W732 route-data provider now feeds the W853 selected-cochain\
      direct-source branch data"
  leftCalculusResult :=
    "proved: one W732 route-data provider supplies direct bounded left calculus\
      through the constructed W853 provider"
  stablePackageResult :=
    "proved: one W732 route-data provider supplies the existing bounded derived\
      infinity-category package through the constructed W853 provider"
  remainingInputs :=
    ["construct a concrete W732 route-data provider",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW854HomologyFreeProviderFromRouteData_productSuccess :
    currentMetrizableHomologyFreeProviderFromRouteDataStateW854.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
