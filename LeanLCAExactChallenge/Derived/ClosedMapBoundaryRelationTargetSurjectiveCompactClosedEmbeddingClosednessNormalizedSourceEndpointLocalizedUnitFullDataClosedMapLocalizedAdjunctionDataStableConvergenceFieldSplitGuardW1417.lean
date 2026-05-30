import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapEndpointKernelCokernelTopDataStableConvergenceFieldSplitGuardW1416
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W1417 records definitional convergence for the W975 localized-adjunction data
bridge: W975 projects the localized-adjunction provider into the right adjoint
and adjunction fields before delegating into the W974 endpoint-data route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W975 constructs W974 leaves after unpacking localized-adjunction data. -/
theorem w975W974LeavesRunThroughLocalizedAdjunctionDataW1417
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
        leaves =
      w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
        leaves :=
  rfl

/-- W975 endpoint strict exactness delegates through W974. -/
theorem w975EndpointStrictExactRunsThroughW974W1417
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    endpointStrictExactOfLocalizedAdjunctionDataW975 leaves =
      endpointStrictExactOfEndpointKernelCokernelTopDataW974
        (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
          leaves) :=
  rfl

/-- W975 unit algebraic exactness delegates through W974. -/
theorem w975UnitAlgebraicExactRunsThroughW974W1417
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    unitMappingConeAlgebraicExactOfLocalizedAdjunctionDataW975 leaves =
      unitMappingConeAlgebraicExactOfUnitKernelEqualityW974
        (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
          leaves) :=
  rfl

/-- W975 direct calculus delegates to W974 after unpacking localized-adjunction data. -/
theorem w975DirectCalculusRunsThroughW974W1417
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    directBoundedLeftCalculusOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
        leaves =
      directBoundedLeftCalculusOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
          leaves) :=
  rfl

/-- W975 stable package delegates to W974 after unpacking localized-adjunction data. -/
theorem w975StablePackageRunsThroughW974W1417
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    boundedDerivedInfinityCategoryOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
        leaves =
      boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
        (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
          leaves) :=
  rfl

/-- W1417 keeps the W975 localized-adjunction-data input count visible. -/
theorem w1417ClosedMapLocalizedAdjunctionDataInputCount :
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975.length =
      12 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975_count

/-- Current W1417 nonterminal state. -/
structure ClosedMapLocalizedAdjunctionDataStableConvergenceStateW1417 :
    Type where
  seed : String
  declarations : List String
  localizedAdjunctionDataBridgeResult : String
  localizedAdjunctionDataUnpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1417 records W975 convergence into the closed-map stable route. -/
def currentClosedMapLocalizedAdjunctionDataStableConvergenceStateW1417 :
    ClosedMapLocalizedAdjunctionDataStableConvergenceStateW1417 where
  seed := "w1417-closed-map-localized-adjunction-data-stable-convergence"
  declarations :=
    ["w975W974LeavesRunThroughLocalizedAdjunctionDataW1417",
      "w975EndpointStrictExactRunsThroughW974W1417",
      "w975UnitAlgebraicExactRunsThroughW974W1417",
      "w975DirectCalculusRunsThroughW974W1417",
      "w975StablePackageRunsThroughW974W1417",
      "w1417ClosedMapLocalizedAdjunctionDataInputCount"]
  localizedAdjunctionDataBridgeResult :=
    "proved: W975 localized-adjunction-data leaves delegate into W974"
  localizedAdjunctionDataUnpackResult :=
    "proved: W975 replaces localized right-adjoint and adjunction fields by\
      one bounded-homotopy localized-adjunction data provider"
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975
  productSuccessClaimed := false

theorem currentW1417ClosedMapLocalizedAdjunctionDataStableConvergence_productSuccess :
    currentClosedMapLocalizedAdjunctionDataStableConvergenceStateW1417.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
