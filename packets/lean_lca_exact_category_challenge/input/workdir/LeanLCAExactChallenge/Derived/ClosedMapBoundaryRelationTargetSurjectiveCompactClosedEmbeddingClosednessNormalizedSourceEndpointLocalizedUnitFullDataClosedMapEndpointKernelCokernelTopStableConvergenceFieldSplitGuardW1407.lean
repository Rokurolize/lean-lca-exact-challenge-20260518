import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapEndpointCokernelTopStableConvergenceFieldSplitGuardW1406
import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitWitnessComponentFieldsRoute

/-!
W1407 records definitional convergence for the W965 endpoint kernel/cokernel-top
bridge: W965 derives endpoint algebraic exactness from endpoint kernel equality
and then delegates into the W964 endpoint cokernel-top route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W965 constructs W963 leaves by delegating through W964. -/
theorem w965W963LeavesRunThroughW964W1407
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    w963LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        leaves =
      w963LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
        (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
          leaves) :=
  rfl

/-- W965 constructs W962 leaves by delegating through W964. -/
theorem w965W962LeavesRunThroughW964W1407
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    w962LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        leaves =
      w962LeavesOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
        (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
          leaves) :=
  rfl

/-- W965 direct calculus delegates to W964 after deriving endpoint exactness. -/
theorem w965DirectCalculusRunsThroughW964W1407
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    directBoundedLeftCalculusOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        leaves =
      directBoundedLeftCalculusOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
        (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
          leaves) :=
  rfl

/-- W965 stable package delegates to W964 after deriving endpoint exactness. -/
theorem w965StablePackageRunsThroughW964W1407
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldLeavesW965) :
    boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
        leaves =
      boundedDerivedInfinityCategoryOfEndpointCokernelTopAndUnitMappingConeComponentFieldsW964
        (w964LeavesOfEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsW965
          leaves) :=
  rfl

/-- W1407 keeps the W965 endpoint kernel/cokernel-top field input count visible. -/
theorem w1407ClosedMapEndpointKernelCokernelTopInputCount :
    closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965.length =
      26 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965_count

/-- Current W1407 nonterminal state. -/
structure ClosedMapEndpointKernelCokernelTopStableConvergenceStateW1407 :
    Type where
  seed : String
  declarations : List String
  endpointKernelCokernelTopBridgeResult : String
  endpointAlgebraicExactResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1407 records W965 convergence into the closed-map stable route. -/
def currentClosedMapEndpointKernelCokernelTopStableConvergenceStateW1407 :
    ClosedMapEndpointKernelCokernelTopStableConvergenceStateW1407 where
  seed := "w1407-closed-map-endpoint-kernel-cokernel-top-stable-convergence"
  declarations :=
    ["w965W963LeavesRunThroughW964W1407",
      "w965W962LeavesRunThroughW964W1407",
      "w965DirectCalculusRunsThroughW964W1407",
      "w965StablePackageRunsThroughW964W1407",
      "w1407ClosedMapEndpointKernelCokernelTopInputCount"]
  endpointKernelCokernelTopBridgeResult :=
    "proved: W965 endpoint kernel/cokernel-top leaves delegate into W964"
  endpointAlgebraicExactResult :=
    "proved: W965 replaces endpoint algebraic exactness by endpoint kernel equality"
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopAndUnitMappingConeComponentFieldsInputNamesW965
  productSuccessClaimed := false

theorem currentW1407ClosedMapEndpointKernelCokernelTopStableConvergence_productSuccess :
    currentClosedMapEndpointKernelCokernelTopStableConvergenceStateW1407.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
