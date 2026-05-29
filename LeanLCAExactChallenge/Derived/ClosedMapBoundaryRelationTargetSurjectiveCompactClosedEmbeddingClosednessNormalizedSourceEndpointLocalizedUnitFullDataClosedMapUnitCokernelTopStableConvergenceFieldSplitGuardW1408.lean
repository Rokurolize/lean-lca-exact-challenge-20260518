import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapEndpointKernelCokernelTopStableConvergenceFieldSplitGuardW1407
import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitCokernelTopComponentFieldsRoute

/-!
W1408 records definitional convergence for the W966 unit cokernel-top bridge:
W966 derives unit mapping-cone surjectivity from unit cokernel-top plus unit
open-map witnesses and then delegates into the W965 endpoint kernel/cokernel-top
route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W966 constructs W965 leaves before entering the endpoint kernel/cokernel-top route. -/
theorem w966W965LeavesRunThroughEndpointKernelCokernelTopW1408
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves =
      w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves :=
  rfl

/-- W966 constructs W964 leaves by delegating through W965. -/
theorem w966W964LeavesRunThroughW965W1408
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves =
      w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
          leaves) :=
  rfl

/-- W966 constructs W962 leaves by delegating through W965. -/
theorem w966W962LeavesRunThroughW965W1408
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves =
      w962LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
          leaves) :=
  rfl

/-- W966 direct calculus delegates to W965 after deriving unit surjectivity. -/
theorem w966DirectCalculusRunsThroughW965W1408
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves =
      directBoundedLeftCalculusOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
          leaves) :=
  rfl

/-- W966 stable package delegates to W965 after deriving unit surjectivity. -/
theorem w966StablePackageRunsThroughW965W1408
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldLeavesW966) :
    boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        leaves =
      boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        (w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
          leaves) :=
  rfl

/-- W1408 keeps the W966 unit cokernel-top field input count visible. -/
theorem w1408ClosedMapUnitCokernelTopInputCount :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966.length =
      26 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966_count

/-- Current W1408 nonterminal state. -/
structure ClosedMapUnitCokernelTopStableConvergenceStateW1408 :
    Type where
  seed : String
  declarations : List String
  unitCokernelTopBridgeResult : String
  unitSurjectivityResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1408 records W966 convergence into the closed-map stable route. -/
def currentClosedMapUnitCokernelTopStableConvergenceStateW1408 :
    ClosedMapUnitCokernelTopStableConvergenceStateW1408 where
  seed := "w1408-closed-map-unit-cokernel-top-stable-convergence"
  declarations :=
    ["w966W965LeavesRunThroughEndpointKernelCokernelTopW1408",
      "w966W964LeavesRunThroughW965W1408",
      "w966W962LeavesRunThroughW965W1408",
      "w966DirectCalculusRunsThroughW965W1408",
      "w966StablePackageRunsThroughW965W1408",
      "w1408ClosedMapUnitCokernelTopInputCount"]
  unitCokernelTopBridgeResult :=
    "proved: W966 unit cokernel-top leaves delegate into W965"
  unitSurjectivityResult :=
    "proved: W966 replaces unit mapping-cone surjectivity by unit cokernel-top plus open-map witnesses"
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitCokernelTopComponentFieldsInputNamesW966
  productSuccessClaimed := false

theorem currentW1408ClosedMapUnitCokernelTopStableConvergence_productSuccess :
    currentClosedMapUnitCokernelTopStableConvergenceStateW1408.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
