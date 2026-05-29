import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSinglePreservationSelectedColimitFieldSplitGuardW1345
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1346 records the W519 closed-range mapped-cokernel preservation split. W519
turns closed-map or closed-embedding evidence for mapped explicit cokernel
inputs into closed-range evidence, then supplies both mapped explicit cokernel
cofork colimits and W503 closure-kernel preservation. This still requires
compact-target relation data plus mapped-cokernel closed-range evidence, so it
does not close the current W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpCompactTargetRelationPreservationExitsV370SupportW518
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

def canonicalW519MappedCokernelProviderRoutesW1346 : List String :=
  ["mapped explicit cokernel closed-range provider",
    "mapped explicit cokernel closed-map provider",
    "mapped explicit cokernel closed-embedding provider"]

theorem canonicalW519MappedCokernelProviderRoutesW1346_count :
    canonicalW519MappedCokernelProviderRoutesW1346.length = 3 :=
  rfl

theorem canonicalW519MappedCokernelRoutesExpandCurrentSurfaceW1346 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW519MappedCokernelProviderRoutesW1346.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW519MappedCokernelProviderRoutesW1346_count]
  norm_num

theorem w519ClosedMapProviderRunsThroughClosedRangeW1346
    (hMap : MappedExplicitCokernelClosedMapProviderW519) :
    closedRangeProvider_of_closedMapProvider_w519 hMap =
      { isClosedRange := by
          intro X Y f
          simpa [Set.image_univ] using hMap.isClosedMap f Set.univ isClosed_univ } :=
  rfl

theorem w519ClosedEmbeddingProviderRunsThroughClosedRangeW1346
    (hEmbedding : MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedRangeProvider_of_closedEmbeddingProvider_w519 hEmbedding =
      { isClosedRange := by
          intro X Y f
          exact (hEmbedding.isClosedEmbedding f).isClosed_range } :=
  rfl

theorem w519ClosedRangeClosureKernelEvaluatesW1346
    (hRange : MappedExplicitCokernelClosedRangeProviderW519)
    (X Y : MetrizableLCA.{0}) (f : X ⟶ Y) :
    (closureKernelProvider_of_closedRangeProvider_w519 hRange).closureKernel f =
      MetrizableLCA.closureKernelInput_of_cokernelSubgroup_eq_forgottenAlgebraicRange f
        (MetrizableLCA.cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range
          f (hRange.isClosedRange f)) :=
  rfl

theorem w519CompactTargetClosedRangeEndpointRunsThroughW518W1346
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hRange : MappedExplicitCokernelClosedRangeProviderW519) :
    exactAcyclic_of_compactTargetRelation_and_closedRangeMappedCokernels_w519
        hinputs hRange =
      exactAcyclic_of_compactTargetRelation_and_mappedExplicitCokernelCoforks_w518
        hinputs (mappedExplicitCokernelCoforks_of_closedRangeProvider_w519 hRange) :=
  rfl

theorem w519CompactTargetClosedMapEndpointRunsThroughClosedRangeW1346
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hMap : MappedExplicitCokernelClosedMapProviderW519) :
    exactAcyclic_of_compactTargetRelation_and_closedMapMappedCokernels_w519
        hinputs hMap =
      exactAcyclic_of_compactTargetRelation_and_closedRangeMappedCokernels_w519
        hinputs (closedRangeProvider_of_closedMapProvider_w519 hMap) :=
  rfl

theorem w519CompactTargetClosedEmbeddingEndpointRunsThroughClosedRangeW1346
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hEmbedding : MappedExplicitCokernelClosedEmbeddingProviderW519) :
    exactAcyclic_of_compactTargetRelation_and_closedEmbeddingMappedCokernels_w519
        hinputs hEmbedding =
      exactAcyclic_of_compactTargetRelation_and_closedRangeMappedCokernels_w519
        hinputs (closedRangeProvider_of_closedEmbeddingProvider_w519 hEmbedding) :=
  rfl

theorem w519CompactTargetClosureKernelEndpointRunsThroughW518W1346
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hRange : MappedExplicitCokernelClosedRangeProviderW519) :
    exactAcyclic_of_compactTargetRelation_and_closedRangeClosureKernel_w519
        hinputs hRange =
      exactAcyclic_of_compactTargetRelation_and_closureKernelProvider_w518
        hinputs (closureKernelProvider_of_closedRangeProvider_w519 hRange) :=
  rfl

structure MetrizableClosedRangeMappedCokernelFieldSplitGuardStateW1346 : Type where
  seed : String
  inspectedBoundary : String
  providerRouteCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedRangeMappedCokernelFieldSplitGuardStateW1346 :
    MetrizableClosedRangeMappedCokernelFieldSplitGuardStateW1346 where
  seed := "w1346-closed-range-mapped-cokernel-field-split-guard"
  inspectedBoundary :=
    "W519 field split from mapped explicit cokernel closed-range, closed-map,\
      and closed-embedding providers into mapped-cokernel and closure-kernel\
      exact-acyclic routes"
  providerRouteCount :=
    canonicalW519MappedCokernelProviderRoutesW1346.length
  providerSearchResult :=
    "proved: W519 converts closed-map and closed-embedding providers into\
      closed-range providers, converts closed range into both mapped explicit\
      cokernel cofork colimits and W503 closure-kernel preservation, and\
      delegates compact-target exact-acyclic endpoints through W518; this still\
      requires compact-target relation data plus mapped-cokernel closed-range\
      evidence and does not discharge the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1346ClosedRangeMappedCokernelFieldSplitGuard_productSuccess :
    (let state := currentMetrizableClosedRangeMappedCokernelFieldSplitGuardStateW1346;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
