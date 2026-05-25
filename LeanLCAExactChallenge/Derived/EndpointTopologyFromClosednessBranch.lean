import LeanLCAExactChallenge.Derived.HomologyFreeSelectedCochainStableRoute

/-!
W856 derives the forgetful homology-preservation component of W720 endpoint data
from the already matched W519 mapped-cokernel closedness branch.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W856 endpoint facts after removing the forgetful homology-preservation subfield:
W519 closedness supplies that piece through the W694 closure-kernel route.
-/
structure MetrizableWppEndpointTopologyFactsProviderW856 :
    Type 2 where
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointEpiOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)

/-- W856 closed-map W519 data supply forgetful homology preservation. -/
@[reducible]
def endpointForgetPreservesHomologyOfClosedMapW856
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
  metrizableForgetfulPreservesHomology_of_closureKernelW694
    (closureKernelProvider_of_closedRangeProvider_w519
      (closedRangeProvider_of_closedMapProvider_w519
        mappedCokernelClosedMapProvider))

/-- W856 closed-embedding W519 data supply forgetful homology preservation. -/
@[reducible]
def endpointForgetPreservesHomologyOfClosedEmbeddingW856
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
  metrizableForgetfulPreservesHomology_of_closureKernelW694
    (closureKernelProvider_of_closedRangeProvider_w519
      (closedRangeProvider_of_closedEmbeddingProvider_w519
        mappedCokernelClosedEmbeddingProvider))

/--
W856 recovers W720's forgetful homology-preservation field from the same matched
closedness branch that W853 consumes.
-/
@[reducible]
def endpointForgetPreservesHomologyOfClosednessBranchW856
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
  match closednessData with
  | .closedMap _ mappedCokernelClosedMapProvider =>
      endpointForgetPreservesHomologyOfClosedMapW856
        mappedCokernelClosedMapProvider
  | .closedEmbedding _ mappedCokernelClosedEmbeddingProvider =>
      endpointForgetPreservesHomologyOfClosedEmbeddingW856
        mappedCokernelClosedEmbeddingProvider

/-- W856 reconstructs the full W720 endpoint data from W519 closedness plus three endpoint facts. -/
def endpointStrictTopologyDataOfClosednessBranchW856
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    MetrizableWppEndpointStrictTopologyDataProviderW720 where
  endpointForgetPreservesHomology :=
    endpointForgetPreservesHomologyOfClosednessBranchW856 closednessData
  endpointClosedEmbedding := endpointFacts.endpointClosedEmbedding
  endpointOpenMap := endpointFacts.endpointOpenMap
  endpointEpiOfExactAt := endpointFacts.endpointEpiOfExactAt

/--
W856 route-data provider with W720 weakened to endpoint topology facts. The
forgetful homology-preservation component is derived from the W519 branch.
-/
structure MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetSurjectiveCompactForTargetProvider :
    TargetSurjectiveCompactForTargetProviderW715
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointTopologyFacts :
    MetrizableWppEndpointTopologyFactsProviderW856
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W856 restores the W853 provider by deriving the W720 endpoint provider. -/
def homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    MetrizableWppHomologyFreeSelectedCochainRouteDataProviderW853 where
  boundaryData := routeData.boundaryData
  relationData := routeData.relationData
  targetSurjectiveCompactForTargetProvider :=
    routeData.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    routeData.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := routeData.normalizedFixedTargetData
  sourceTriangulationData := routeData.sourceTriangulationData
  endpointStrictTopologyData :=
    endpointStrictTopologyDataOfClosednessBranchW856
      routeData.diagramAndMappedCokernelClosednessData
      routeData.endpointTopologyFacts
  localizedRightAdjointData := routeData.localizedRightAdjointData

/-- W856 selected-cochain direct-source data from endpoint facts plus W519 closedness. -/
noncomputable def selectedCochainDirectSourceDataOfEndpointFactsW856
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    MetrizableHomologyFreeSelectedCochainDirectSourceDataW853 :=
  selectedCochainDirectSourceDataOfHomologyFreeRouteDataW853
    (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
      routeData)

/-- W856 direct bounded left calculus from endpoint facts plus W519 closedness. -/
theorem directBoundedLeftCalculusOfEndpointFactsW856
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfHomologyFreeComparisonSelectedCochainW853
    (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
      routeData)

/-- W856 bounded derived infinity-category package from endpoint facts plus W519 closedness. -/
noncomputable def boundedDerivedInfinityCategoryOfEndpointFactsW856
    (routeData : MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfHomologyFreeComparisonSelectedCochainW853
    (homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856
      routeData)

/-- Endpoint facts still required by W856 after W519 supplies forgetful homology preservation. -/
def endpointTopologyFactInputNamesW856 : List String :=
  ["endpoint closed-embedding facts for cochain short complexes",
    "endpoint open-map facts for cochain short complexes",
    "endpoint ExactAt-to-epi facts for cochain short complexes"]

theorem endpointTopologyFactInputNamesW856_count :
    endpointTopologyFactInputNamesW856.length = 3 :=
  rfl

/-- W856 input names after W519 closes the W720 forgetful homology-preservation subfield. -/
def endpointFactsHomologyFreeRouteDataInputNamesW856 : List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation ordinary relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "source triangulation and triangle-completion data provider",
    "endpoint topology facts excluding forgetful homology preservation",
    "bounded homotopy localized-right-adjoint data provider"]

theorem endpointFactsHomologyFreeRouteDataInputNamesW856_count :
    endpointFactsHomologyFreeRouteDataInputNamesW856.length = 8 :=
  rfl

/-- Current checked W856 state for deriving W720 forgetful homology preservation from W519. -/
structure MetrizableEndpointFactsHomologyFreeRouteDataStateW856 :
    Type where
  seed : String
  declarations : List String
  forgetPreservesHomologyResult : String
  endpointProviderResult : String
  routeResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current W856 nonterminal state. -/
def currentMetrizableEndpointFactsHomologyFreeRouteDataStateW856 :
    MetrizableEndpointFactsHomologyFreeRouteDataStateW856
    where
  seed :=
    "w856-endpoint-forgetful-homology-from-mapped-cokernel-closedness"
  declarations :=
    ["MetrizableWppEndpointTopologyFactsProviderW856",
      "endpointForgetPreservesHomologyOfClosedMapW856",
      "endpointForgetPreservesHomologyOfClosedEmbeddingW856",
      "endpointForgetPreservesHomologyOfClosednessBranchW856",
      "endpointStrictTopologyDataOfClosednessBranchW856",
      "MetrizableWppEndpointFactsHomologyFreeRouteDataProviderW856",
      "homologyFreeSelectedCochainRouteDataProviderOfEndpointFactsW856",
      "selectedCochainDirectSourceDataOfEndpointFactsW856",
      "directBoundedLeftCalculusOfEndpointFactsW856",
      "boundedDerivedInfinityCategoryOfEndpointFactsW856",
      "endpointTopologyFactInputNamesW856",
      "endpointTopologyFactInputNamesW856_count",
      "endpointFactsHomologyFreeRouteDataInputNamesW856",
      "endpointFactsHomologyFreeRouteDataInputNamesW856_count"]
  forgetPreservesHomologyResult :=
    "proved: the W519 closed-map or closed-embedding mapped-cokernel branch supplies \
      W720 forgetful homology preservation through W503/W694"
  endpointProviderResult :=
    "proved: full W720 endpoint strict-topology data is reconstructed from W519 \
      closedness and the three non-homology endpoint topology facts"
  routeResult :=
    "proved: the W853 homology-free selected-cochain route consumes the weakened \
      endpoint-facts provider after W856 reconstructs W720"
  replacedInputs :=
    ["separate endpoint forgetful homology-preservation field inside W720",
      "separate selected-difference component and W519 mapped-cokernel branch inputs"]
  remainingInputs :=
    endpointFactsHomologyFreeRouteDataInputNamesW856
  productSuccessClaimed := false

theorem currentW856EndpointFactsHomologyFreeRouteData_productSuccess :
    currentMetrizableEndpointFactsHomologyFreeRouteDataStateW856.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
