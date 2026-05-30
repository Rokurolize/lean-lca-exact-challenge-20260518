import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapUnitCokernelTopStableConvergenceFieldSplitGuardW1408
import LeanLCAExactChallenge.Derived.ClosedMapRawBoundaryRelationFieldsNormalizedFixedTargetFieldsSourceTriangulationFieldsClosedEmbeddingClosednessFieldsSplitTargetNoUnivClosednessNormalizedEndpointKernelCokernelTopAndUnitKernelCokernelTopComponentFieldsRoute

/-!
W1409 records definitional convergence for the W967 unit kernel/cokernel-top
bridge: W967 derives unit mapping-cone algebraic exactness from unit kernel
equality and then delegates into the W966 unit cokernel-top route.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W967 constructs W965 leaves by delegating through W966. -/
theorem w967W965LeavesRunThroughW966W1409
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967) :
    w965LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
        leaves =
      w965LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
          leaves) :=
  rfl

/-- W967 constructs W964 leaves by delegating through W966. -/
theorem w967W964LeavesRunThroughW966W1409
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967) :
    w964LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
        leaves =
      w964LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
          leaves) :=
  rfl

/-- W967 constructs W962 leaves by delegating through W966. -/
theorem w967W962LeavesRunThroughW966W1409
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967) :
    w962LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
        leaves =
      w962LeavesOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
          leaves) :=
  rfl

/-- W967 direct calculus delegates to W966 after deriving unit exactness. -/
theorem w967DirectCalculusRunsThroughW966W1409
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967) :
    directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
        leaves =
      directBoundedLeftCalculusOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
          leaves) :=
  rfl

/-- W967 stable package delegates to W966 after deriving unit exactness. -/
theorem w967StablePackageRunsThroughW966W1409
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldLeavesW967) :
    boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
        leaves =
      boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopUnitCokernelTopComponentFieldsW966
        (w966LeavesOfEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsW967
          leaves) :=
  rfl

/-- W1409 keeps the W967 unit kernel/cokernel-top field input count visible. -/
theorem w1409ClosedMapUnitKernelCokernelTopInputCount :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsInputNamesW967.length =
      26 :=
  closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsInputNamesW967_count

/-- Current W1409 nonterminal state. -/
structure ClosedMapUnitKernelCokernelTopStableConvergenceStateW1409 :
    Type where
  seed : String
  declarations : List String
  unitKernelCokernelTopBridgeResult : String
  unitAlgebraicExactResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1409 records W967 convergence into the closed-map stable route. -/
def currentClosedMapUnitKernelCokernelTopStableConvergenceStateW1409 :
    ClosedMapUnitKernelCokernelTopStableConvergenceStateW1409 where
  seed := "w1409-closed-map-unit-kernel-cokernel-top-stable-convergence"
  declarations :=
    ["w967W965LeavesRunThroughW966W1409",
      "w967W964LeavesRunThroughW966W1409",
      "w967W962LeavesRunThroughW966W1409",
      "w967DirectCalculusRunsThroughW966W1409",
      "w967StablePackageRunsThroughW966W1409",
      "w1409ClosedMapUnitKernelCokernelTopInputCount"]
  unitKernelCokernelTopBridgeResult :=
    "proved: W967 unit kernel/cokernel-top leaves delegate into W966"
  unitAlgebraicExactResult :=
    "proved: W967 replaces unit mapping-cone algebraic exactness by unit kernel equality"
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopComponentFieldsInputNamesW967
  productSuccessClaimed := false

theorem currentW1409ClosedMapUnitKernelCokernelTopStableConvergence_productSuccess :
    currentClosedMapUnitKernelCokernelTopStableConvergenceStateW1409.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
