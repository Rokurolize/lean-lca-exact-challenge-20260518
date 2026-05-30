import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSplitCompactTargetGlobalClosedEmbeddingFieldSplitGuardW1351
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1352 records the W595/W596 split compact-target endpoint field splits. W595
routes split W593 compact-target fields plus one global W525 provider to the
W525 exact-acyclic endpoints. W596 routes the same split surface through the
W581 row-provider narrowing and into the W535 colimit-stability endpoints. The
shared endpoint surface still has three inputs and therefore does not close the
current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpSelectedDifferenceClosedMapClosedRangeOnlyV370SupportW525
open WppOpRowAwareClosedRangeOnlyProjectionV370SupportW526
open WppOpW535FiniteShapeTransferConcreteRowsV370SupportW535

namespace Dbounded

def canonicalW595SplitCompactTargetEndpointInputNamesW1352 :
    List String :=
  metrizableWppSplitCompactTargetExactAcyclicEndpointInputNamesW595

theorem canonicalW595SplitCompactTargetEndpointInputNamesW1352_count :
    canonicalW595SplitCompactTargetEndpointInputNamesW1352.length =
      3 :=
  metrizableWppSplitCompactTargetExactAcyclicEndpointInputNamesW595_count

def canonicalW596SplitCompactTargetEndpointInputNamesW1352 :
    List String :=
  metrizableWppSplitCompactTargetColimitStabilityInputNamesW596

theorem canonicalW596SplitCompactTargetEndpointInputNamesW1352_count :
    canonicalW596SplitCompactTargetEndpointInputNamesW1352.length =
      3 :=
  metrizableWppSplitCompactTargetColimitStabilityInputNamesW596_count

theorem canonicalW595SplitCompactTargetEndpointExpandsCurrentSurfaceW1352 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW595SplitCompactTargetEndpointInputNamesW1352.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW595SplitCompactTargetEndpointInputNamesW1352_count]
  norm_num

theorem canonicalW596SplitCompactTargetEndpointExpandsCurrentSurfaceW1352 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW596SplitCompactTargetEndpointInputNamesW1352.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW596SplitCompactTargetEndpointInputNamesW1352_count]
  norm_num

theorem w595ClosedMapEndpointRunsThroughW525W1352
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    exactAcyclic_of_splitCompactTargetRelation_closedMap_w595
        hpullback hcompact hclosedMap =
      exactAcyclic_of_compactTargetRelation_closedMap_w525
        (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact)
        hclosedMap :=
  rfl

theorem w595ClosedEmbeddingEndpointRunsThroughW525W1352
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    exactAcyclic_of_splitCompactTargetRelation_closedEmbedding_w595
        hpullback hcompact hclosedEmbedding =
      exactAcyclic_of_compactTargetRelation_closedEmbedding_w525
        (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact)
        hclosedEmbedding :=
  rfl

theorem w596ClosedMapEndpointRunsThroughW535W1352
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    walkingParallelPairColimitStability_of_splitCompactTargetRelation_globalClosedMap_w596
        hpullback hcompact hclosedMap =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedMapRows_w535
        (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact)
        (componentwiseClosedMapRowsProvider_of_globalClosedMapProvider_w581
          hclosedMap) :=
  rfl

theorem w596ClosedEmbeddingEndpointRunsThroughW535W1352
    (hpullback : ClosedNatTransOrdinaryRelationPullbackProviderW593)
    (hcompact : ClosedNatTransOrdinaryTargetRelationCompactProviderW593)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    walkingParallelPairColimitStability_of_splitCompactTargetRelation_globalClosedEmbedding_w596
        hpullback hcompact hclosedEmbedding =
      walkingParallelPairColimitStability_of_compactTargetRelation_and_closedEmbeddingRows_w535
        (compactTargetRelationProvider_of_splitFields_w593 hpullback hcompact)
        (componentwiseClosedEmbeddingRowsProvider_of_globalClosedEmbeddingProvider_w581
          hclosedEmbedding) :=
  rfl

theorem w596ClosedMapRowsNarrowingIgnoresRowsW1352
    (hclosedMap : ComponentwiseClosedMapProviderW525)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs)
    (hRows : StrictRowInputsForSelectedDifferenceW526 S) :
    componentwiseClosedMapRowsProvider_of_globalClosedMapProvider_w581
        hclosedMap S cs hcs hRows =
      hclosedMap S cs hcs :=
  rfl

theorem w596ClosedEmbeddingRowsNarrowingIgnoresRowsW1352
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs)
    (hRows : StrictRowInputsForSelectedDifferenceW526 S) :
    componentwiseClosedEmbeddingRowsProvider_of_globalClosedEmbeddingProvider_w581
        hclosedEmbedding S cs hcs hRows =
      hclosedEmbedding S cs hcs :=
  rfl

structure MetrizableSplitCompactTargetEndpointsFieldSplitGuardStateW1352 :
    Type where
  seed : String
  inspectedBoundary : String
  exactAcyclicEndpointCount : Nat
  colimitStabilityEndpointCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSplitCompactTargetEndpointsFieldSplitGuardStateW1352 :
    MetrizableSplitCompactTargetEndpointsFieldSplitGuardStateW1352 where
  seed := "w1352-split-compact-target-endpoints-field-split-guard"
  inspectedBoundary :=
    "W595/W596 endpoint split from relation-pullback, target-relation\
      compactness, and one global W525 provider into exact-acyclic and\
      colimit-stability endpoints"
  exactAcyclicEndpointCount :=
    canonicalW595SplitCompactTargetEndpointInputNamesW1352.length
  colimitStabilityEndpointCount :=
    canonicalW596SplitCompactTargetEndpointInputNamesW1352.length
  providerSearchResult :=
    "proved: W595 delegates closed-map and closed-embedding exact-acyclic\
      endpoints through W525, while W596 delegates closed-map and\
      closed-embedding colimit-stability endpoints through W535 after W581\
      row-provider narrowing; both endpoint surfaces still have three inputs\
      and expand the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1352SplitCompactTargetEndpointsFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableSplitCompactTargetEndpointsFieldSplitGuardStateW1352;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
