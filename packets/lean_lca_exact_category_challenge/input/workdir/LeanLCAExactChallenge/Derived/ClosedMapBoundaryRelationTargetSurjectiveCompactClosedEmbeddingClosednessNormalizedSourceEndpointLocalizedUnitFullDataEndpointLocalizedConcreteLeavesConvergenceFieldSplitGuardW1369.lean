import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosednessBranchEndpointExactAtConvergenceFieldSplitGuardW1368
import LeanLCAExactChallenge.Derived.TargetExactAtConcreteLeavesFromClosednessBranch

/-!
W1369 records the definitional convergence from W726 endpoint/localized data
and W733 concrete leaves into the W859/W1368 closedness-branch target-ExactAt
route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W860 closed-embedding-of-ExactAt facts are projected from W726's W720 field. -/
theorem w860EndpointExactAtClosedEmbeddingUsesW726EndpointFieldW1369
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        endpointLocalizedData).closedEmbedding_of_exactAt =
      fun K i _hExact =>
        endpointClosedEmbedding_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i :=
  rfl

/-- W860 open-map-of-ExactAt facts are projected from W726's W720 field. -/
theorem w860EndpointExactAtOpenMapUsesW726EndpointFieldW1369
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        endpointLocalizedData).openMap_of_exactAt =
      fun K i _hExact =>
        endpointOpenMap_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i :=
  rfl

/-- W860 epi-of-ExactAt facts are projected from W726's W720 field. -/
theorem w860EndpointExactAtEpiUsesW726EndpointFieldW1369
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    (endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        endpointLocalizedData).epi_of_exactAt =
      fun K i hExact =>
        endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
          (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
            endpointLocalizedData) K i hExact :=
  rfl

/-- W860 preserves the W725 closedness branch when building W859 data. -/
theorem w860ClosednessBranchDataFieldPreservedW1369
    (data :
      MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860) :
    (closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
        data).closednessData =
      data.closednessData :=
  rfl

/-- W860 supplies W859 endpoint facts from the W726 endpoint/localized field. -/
theorem w860EndpointFactsFieldUsesW726W1369
    (data :
      MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860) :
    (closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
        data).endpointExactAtTopologyFacts =
      endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
        data.endpointLocalizedRightAdjointData :=
  rfl

/-- W860 supplies W859 localized-right-adjoint data from W726. -/
theorem w860LocalizedRightAdjointFieldUsesW726W1369
    (data :
      MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860) :
    (closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
        data).localizedRightAdjointData =
      localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
        data.endpointLocalizedRightAdjointData :=
  rfl

/-- W861 projects W725 closedness from W733 concrete leaves into W860 data. -/
theorem w861ConcreteLeavesClosednessFieldFeedsW860W1369
    (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861) :
    (endpointLocalizedTargetExactAtDataOfConcreteLeavesW861 data).closednessData =
      data.concreteLeaves.diagramAndMappedCokernelClosednessData :=
  rfl

/-- W861 assembles W726 endpoint/localized data from W733 concrete leaves. -/
theorem w861ConcreteLeavesEndpointLocalizedFieldFeedsW860W1369
    (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861) :
    (endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
        data).endpointLocalizedRightAdjointData =
      endpointLocalizedRightAdjointData_of_concreteLeavesW733
        data.concreteLeaves :=
  rfl

/--
W1369 exposes the composed W733-to-W859 closedness field used by the W861 route.
-/
theorem w1369ConcreteLeavesToW859ClosednessFieldMatchesW733 :
    ∀ (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861),
      (closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
          (endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
            data)).closednessData =
        data.concreteLeaves.diagramAndMappedCokernelClosednessData :=
  fun _ => rfl

/--
W1369 exposes the composed W733-to-W859 localized-right-adjoint field used by
the W861 route.
-/
theorem w1369ConcreteLeavesToW859LocalizedFieldMatchesW733 :
    ∀ (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861),
      (closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
          (endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
            data)).localizedRightAdjointData =
        localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
          (endpointLocalizedRightAdjointData_of_concreteLeavesW733
            data.concreteLeaves) :=
  fun _ => rfl

/-- W1369 keeps the W860 direct-left-calculus input count visible. -/
theorem w1369EndpointLocalizedTargetExactAtInputCountMatchesW860 :
    endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860.length =
      3 :=
  endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860_count

/-- W1369 keeps the W861 concrete-leaves input count visible. -/
theorem w1369ConcreteLeavesTargetExactAtInputCountMatchesW861 :
    concreteLeavesTargetExactAtLeftCalculusInputNamesW861.length = 2 :=
  concreteLeavesTargetExactAtLeftCalculusInputNamesW861_count

/-- Current W1369 nonterminal state. -/
structure EndpointLocalizedConcreteLeavesConvergenceStateW1369 : Type where
  seed : String
  declarations : List String
  endpointLocalizedResult : String
  concreteLeavesResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1369 records W726/W733 convergence into the W1368-checked W859 branch. -/
def currentEndpointLocalizedConcreteLeavesConvergenceStateW1369 :
    EndpointLocalizedConcreteLeavesConvergenceStateW1369 where
  seed := "w1369-endpoint-localized-concrete-leaves-convergence"
  declarations :=
    ["w860EndpointExactAtClosedEmbeddingUsesW726EndpointFieldW1369",
      "w860EndpointExactAtOpenMapUsesW726EndpointFieldW1369",
      "w860EndpointExactAtEpiUsesW726EndpointFieldW1369",
      "w860ClosednessBranchDataFieldPreservedW1369",
      "w860EndpointFactsFieldUsesW726W1369",
      "w860LocalizedRightAdjointFieldUsesW726W1369",
      "w861ConcreteLeavesClosednessFieldFeedsW860W1369",
      "w861ConcreteLeavesEndpointLocalizedFieldFeedsW860W1369",
      "w1369ConcreteLeavesToW859ClosednessFieldMatchesW733",
      "w1369ConcreteLeavesToW859LocalizedFieldMatchesW733",
      "w1369EndpointLocalizedTargetExactAtInputCountMatchesW860",
      "w1369ConcreteLeavesTargetExactAtInputCountMatchesW861"]
  endpointLocalizedResult :=
    "proved: W860 sends W726 endpoint/localized data into W859 while preserving \
      the W725 branch and W785 payload"
  concreteLeavesResult :=
    "proved: W861 sends W733 concrete leaves through W860 into the same W859 \
      closedness branch checked by W1368"
  remainingInputs :=
    concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861
  productSuccessClaimed := false

theorem currentW1369EndpointLocalizedConcreteLeavesConvergence_productSuccess :
    currentEndpointLocalizedConcreteLeavesConvergenceStateW1369.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
