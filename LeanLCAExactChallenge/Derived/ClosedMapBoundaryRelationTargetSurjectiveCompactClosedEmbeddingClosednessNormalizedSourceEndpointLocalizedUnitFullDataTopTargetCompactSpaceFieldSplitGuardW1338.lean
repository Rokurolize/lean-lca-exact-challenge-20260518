import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSplitTopTargetCompactSpaceFieldSplitGuardW1337
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1338 records the W597 top-target compact-space field split. W597 projects the
relation-pullback half out of W516 top-target data, combines W516 target-top
data with compact target spaces to rebuild W593 compact-target data, and then
feeds W595/W596 endpoints. The route still exposes three inputs and therefore
does not close the current one-input W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpTopTargetRelationRepresentativeImageV370SupportW516
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519
open WppOpSelectedDifferenceClosedMapClosedRangeOnlyV370SupportW525

namespace Dbounded

def canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338 :
    List String :=
  metrizableWppTopTargetCompactSpaceSplitCompactTargetInputNamesW597

theorem canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338_count :
    canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338.length =
      3 :=
  metrizableWppTopTargetCompactSpaceSplitCompactTargetInputNamesW597_count

theorem canonicalW597TopTargetCompactSpaceFieldSplitExpandsCurrentSurfaceW1338 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338_count]
  norm_num

theorem w597RelationPullbackProjectionW1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    relationPullbackProvider_of_topTargetRelation_w597 htop X Y α hclosed =
      (htop X Y α hclosed).relation_pullback :=
  rfl

theorem w597CompactTargetRunsThroughW593W1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597) :
    compactTargetRelationProvider_of_topTargetRelation_targetCompactSpace_w597
        htop hcompactSpace =
      compactTargetRelationProvider_of_splitFields_w593
        (relationPullbackProvider_of_topTargetRelation_w597 htop)
        (targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
          htop hcompactSpace) :=
  rfl

theorem w597ExactAcyclicClosedMapRunsThroughW595W1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    exactAcyclic_of_topTargetRelation_targetCompactSpace_closedMap_w597
        htop hcompactSpace hclosedMap =
      exactAcyclic_of_splitCompactTargetRelation_closedMap_w595
        (relationPullbackProvider_of_topTargetRelation_w597 htop)
        (targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
          htop hcompactSpace)
        hclosedMap :=
  rfl

theorem w597ExactAcyclicClosedEmbeddingRunsThroughW595W1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    exactAcyclic_of_topTargetRelation_targetCompactSpace_closedEmbedding_w597
        htop hcompactSpace hclosedEmbedding =
      exactAcyclic_of_splitCompactTargetRelation_closedEmbedding_w595
        (relationPullbackProvider_of_topTargetRelation_w597 htop)
        (targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
          htop hcompactSpace)
        hclosedEmbedding :=
  rfl

theorem w597ColimitClosedMapRunsThroughW596W1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    walkingParallelPairColimitStability_of_topTargetRelation_targetCompactSpace_globalClosedMap_w597
        htop hcompactSpace hclosedMap =
      walkingParallelPairColimitStability_of_splitCompactTargetRelation_globalClosedMap_w596
        (relationPullbackProvider_of_topTargetRelation_w597 htop)
        (targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
          htop hcompactSpace)
        hclosedMap :=
  rfl

theorem w597ColimitClosedEmbeddingRunsThroughW596W1338
    (htop : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcompactSpace : ClosedNatTransOrdinaryTargetCompactSpaceProviderW597)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    walkingParallelPairColimitStability_of_topTargetRelation_targetCompactSpace_globalClosedEmbedding_w597
        htop hcompactSpace hclosedEmbedding =
      walkingParallelPairColimitStability_of_splitCompactTargetRelation_globalClosedEmbedding_w596
        (relationPullbackProvider_of_topTargetRelation_w597 htop)
        (targetRelationCompactProvider_of_topTargetRelation_targetCompactSpace_w597
          htop hcompactSpace)
        hclosedEmbedding :=
  rfl

structure MetrizableTopTargetCompactSpaceFieldSplitGuardStateW1338 :
    Type where
  seed : String
  inspectedBoundary : String
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTopTargetCompactSpaceFieldSplitGuardStateW1338 :
    MetrizableTopTargetCompactSpaceFieldSplitGuardStateW1338 where
  seed := "w1338-top-target-compact-space-field-split-guard"
  inspectedBoundary :=
    "W597 field split from W516 top-target and compact target-space data into\
      W593/W595/W596 compact-target routes"
  routeSurfaceCount :=
    canonicalW597TopTargetCompactSpaceFieldSplitInputNamesW1338.length
  providerSearchResult :=
    "proved: W597 projects relation-pullback data out of W516 top-target data,\
      reconstructs compact-target data through W593, and routes exact-acyclic\
      and colimit-stability endpoints through W595/W596, but its route surface\
      still has three inputs and expands the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1338TopTargetCompactSpaceFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableTopTargetCompactSpaceFieldSplitGuardStateW1338;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
