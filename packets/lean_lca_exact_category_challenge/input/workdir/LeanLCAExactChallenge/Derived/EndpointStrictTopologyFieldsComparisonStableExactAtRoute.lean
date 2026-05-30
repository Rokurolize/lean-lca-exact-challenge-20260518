import LeanLCAExactChallenge.Derived.SourceTriangulationFieldsComparisonStableExactAtRoute

/-!
W886 feeds the W885 source-triangulation-fields comparison stable-ExactAt route
from explicit endpoint strict-topology fields.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W886 replaces the bundled W720 endpoint strict-topology provider by its four
explicit endpoint fields.
-/
structure MetrizableWppEndpointStrictTopologyFieldLeavesW886 :
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
  sourcePretriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    Pretriangulated (BoundedComplexCategory MetrizableLCA.{0})
  sourceTriangulated :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    IsTriangulated (BoundedComplexCategory MetrizableLCA.{0})
  triangleCompletion :
    letI : ∀ n : ℤ,
        (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
      inferInstance
    letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
      sourcePretriangulated
    MetrizableBoundedExactWeakEquivalenceTriangleCompletionInputW654
  endpointForgetPreservesHomology :
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointEpiOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W886 assembles the W720 endpoint strict-topology provider from fields. -/
def endpointStrictTopologyDataOfFieldsW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    MetrizableWppEndpointStrictTopologyDataProviderW720
    where
  endpointForgetPreservesHomology := leaves.endpointForgetPreservesHomology
  endpointClosedEmbedding := leaves.endpointClosedEmbedding
  endpointOpenMap := leaves.endpointOpenMap
  endpointEpiOfExactAt := leaves.endpointEpiOfExactAt

/-- W886 assembles the W885 leaves from explicit endpoint fields. -/
def sourceTriangulationFieldLeavesOfEndpointFieldsW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    MetrizableWppSourceTriangulationFieldComparisonLeavesW885
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetSurjectiveCompactForTargetProvider :=
    leaves.targetSurjectiveCompactForTargetProvider
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourcePretriangulated := leaves.sourcePretriangulated
  sourceTriangulated := leaves.sourceTriangulated
  triangleCompletion := leaves.triangleCompletion
  endpointStrictTopologyData := endpointStrictTopologyDataOfFieldsW886 leaves
  localizedRightAdjointData := leaves.localizedRightAdjointData

/-- W886 W733 concrete leaves from explicit endpoint fields. -/
def concreteLeavesOfEndpointFieldsComparisonW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfSourceTriangulationFieldsComparisonW885
    (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves)

/-- W886 W732 route data from explicit endpoint fields. -/
def routeDataProviderOfEndpointFieldsComparisonW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfSourceTriangulationFieldsComparisonW885
    (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves)

/--
W886 direct bounded left calculus through the latest W885 comparison stable
ExactAt route.
-/
theorem directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfSourceTriangulationFieldsComparisonStableExactAtW885
    (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves)

/--
W886 bounded derived infinity-category package through the latest W885
comparison stable ExactAt route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886
    (leaves : MetrizableWppEndpointStrictTopologyFieldLeavesW886) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfSourceTriangulationFieldsComparisonStableExactAtW885
    (sourceTriangulationFieldLeavesOfEndpointFieldsW886 leaves)

/-- W886 exposes endpoint strict-topology fields needed by W885. -/
def endpointFieldsComparisonStableExactAtInputNamesW886 :
    List String :=
  ["bundled WPP right-open quotient-cover and source-pi-zero boundary data",
    "bundled closed natural transformation relation data",
    "target-only target-difference surjectivity plus target-codomain compactness provider",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "normalized fixed-target data provider",
    "Pretriangulated structure on BoundedComplexCategory MetrizableLCA",
    "IsTriangulated structure on BoundedComplexCategory MetrizableLCA",
    "bounded exact weak equivalence source-side triangle-completion data",
    "forgetful functor preserves homology for MetrizableLCA",
    "endpoint ExactAt incoming maps are closed embeddings",
    "endpoint ExactAt outgoing maps are open",
    "endpoint ExactAt outgoing maps are epis",
    "bounded homotopy localized-right-adjoint data provider"]

theorem endpointFieldsComparisonStableExactAtInputNamesW886_count :
    endpointFieldsComparisonStableExactAtInputNamesW886.length =
      13 :=
  rfl

/-- Current checked W886 state. -/
structure MetrizableEndpointFieldsComparisonStableExactAtRouteStateW886 :
    Type where
  seed : String
  declarations : List String
  endpointAssemblyResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointFieldsComparisonStableExactAtRouteStateW886 :
    MetrizableEndpointFieldsComparisonStableExactAtRouteStateW886
    where
  seed := "w886-endpoint-strict-topology-fields-comparison-stable-exact-at"
  declarations :=
    ["MetrizableWppEndpointStrictTopologyFieldLeavesW886",
      "endpointStrictTopologyDataOfFieldsW886",
      "sourceTriangulationFieldLeavesOfEndpointFieldsW886",
      "concreteLeavesOfEndpointFieldsComparisonW886",
      "routeDataProviderOfEndpointFieldsComparisonW886",
      "directBoundedLeftCalculusOfEndpointFieldsComparisonStableExactAtW886",
      "boundedDerivedInfinityCategoryOfEndpointFieldsComparisonStableExactAtW886",
      "endpointFieldsComparisonStableExactAtInputNamesW886",
      "endpointFieldsComparisonStableExactAtInputNamesW886_count"]
  endpointAssemblyResult :=
    "proved: explicit endpoint strict-topology fields assemble the W720 provider\
      consumed by the W885 comparison stable ExactAt route"
  exactAtResult :=
    "proved: explicit endpoint strict-topology fields feed the W885 stable\
      ExactAt route"
  replacedInputs :=
    ["W720 endpoint strict-topology data provider"]
  remainingInputs :=
    endpointFieldsComparisonStableExactAtInputNamesW886
  productSuccessClaimed := false

theorem currentW886EndpointFieldsComparisonStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointFieldsComparisonStableExactAtRouteStateW886;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
