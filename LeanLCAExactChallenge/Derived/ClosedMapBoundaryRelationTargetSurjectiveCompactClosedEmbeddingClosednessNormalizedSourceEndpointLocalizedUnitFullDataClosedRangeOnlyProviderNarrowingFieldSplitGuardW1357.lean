import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedRangeOnlyPreservationBridgeFieldSplitGuardW1356
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1357 records the W523/W524/W525 provider-narrowing chain into the
closed-range-only bridge. It exposes how ordinary closed-nat-trans data,
representative/top/compact relation data, and selected closed-map or
closed-embedding component data reduce to the W522 bridge surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpSelectedW461PointIdentificationRouteV370SupportW500
open WppOpSelectedW461TargetLegRouteV370SupportW504
open WppOpSelectedW461PointIsoTargetLegRouteV370SupportW505
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpSelectedW461TransportedTargetLegV370SupportW507
open WppOpSelectedW461ClosedNatTransOrdinaryPackageV370SupportW509
open WppOpClosedNatTransOrdinaryDescendedQuotientV370SupportW510
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpTopTargetRelationRepresentativeImageV370SupportW516
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpClosedRangeOnlyProjectionBridgeV370SupportW522
open WppOpClosedNatTransSelectedProviderClosedRangeOnlyProjectionV370SupportW523
open WppOpRepresentativeImageSelectedProviderClosedRangeOnlyProjectionV370SupportW524
open WppOpSelectedDifferenceClosedMapClosedRangeOnlyV370SupportW525

namespace Dbounded

def canonicalW523W524W525ProviderNarrowingInputNamesW1357 : List String :=
  ["ordinary/relation/representative/top/compact provider",
    "selected closed-map or closed-embedding component provider"]

theorem canonicalW523W524W525ProviderNarrowingInputNamesW1357_count :
    canonicalW523W524W525ProviderNarrowingInputNamesW1357.length = 2 :=
  rfl

theorem canonicalW523W524W525ProviderNarrowingExpandsCurrentSurfaceW1357 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW523W524W525ProviderNarrowingInputNamesW1357.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW523W524W525ProviderNarrowingInputNamesW1357_count]
  norm_num

theorem w523TopologyFactsProviderRunsThroughPackageW1357
    (hfacts : ClosedNatTransOrdinaryTopologyFactsProviderW510) :
    selectedW461Provider_of_topologyFacts_w523 hfacts =
      selectedW461Provider_of_closedNatTransPackage_w523
        (closedNatTransOrdinaryPackageProvider_of_topologyFacts_w510 hfacts) :=
  rfl

theorem w523RelationTopologyProviderRunsThroughTopologyFactsW1357
    (hinputs : ClosedNatTransOrdinaryRelationTopologyProviderW511) :
    selectedW461Provider_of_relationTopology_w523 hinputs =
      selectedW461Provider_of_topologyFacts_w523
        (closedNatTransOrdinaryTopologyFactsProvider_of_relationTopology_w511
          hinputs) :=
  rfl

theorem w523RelationFieldsProviderRunsThroughTopologyFactsW1357
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512) :
    selectedW461Provider_of_relationFields_w523 hinputs =
      selectedW461Provider_of_topologyFacts_w523
        (closedNatTransOrdinaryTopologyFactsProvider_of_relationFields_w512
          hinputs) :=
  rfl

theorem w523PackageEndpointRunsThroughW522W1357
    (hpkg : ClosedNatTransOrdinaryPackageProviderW509)
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484) :
    exactAcyclic_of_closedNatTransPackage_and_closedRangeOnlyProjection_w523
        hpkg hclosedOnly =
      exactAcyclic_of_selectedW461Provider_and_closedRangeOnlyProjection_w522
        (selectedW461Provider_of_closedNatTransPackage_w523 hpkg)
        hclosedOnly :=
  rfl

theorem w523RelationFieldsEndpointRunsThroughTopologyFactsW1357
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484) :
    exactAcyclic_of_relationFields_and_closedRangeOnlyProjection_w523
        hinputs hclosedOnly =
      exactAcyclic_of_topologyFacts_and_closedRangeOnlyProjection_w523
        (closedNatTransOrdinaryTopologyFactsProvider_of_relationFields_w512
          hinputs)
        hclosedOnly :=
  rfl

theorem w524TopTargetProviderRunsThroughRepresentativeImageW1357
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516) :
    selectedW461Provider_of_topTargetRelation_w524 hinputs =
      selectedW461Provider_of_representativeImage_w524
        (representativeImageProvider_of_topTargetRelation_w516 hinputs) :=
  rfl

theorem w524CompactTargetProviderRunsThroughRepresentativeImageW1357
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    selectedW461Provider_of_compactTargetRelation_w524 hinputs =
      selectedW461Provider_of_representativeImage_w524
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs) :=
  rfl

theorem w524RepresentativeImageEndpointRunsThroughW523W1357
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484) :
    exactAcyclic_of_representativeImage_and_closedRangeOnlyProjection_w524
        hinputs hclosedOnly =
      exactAcyclic_of_relationTopology_and_closedRangeOnlyProjection_w523
        (closedNatTransOrdinaryRelationTopologyProvider_of_representativeImage_w515
          hinputs)
        hclosedOnly :=
  rfl

theorem w524CompactTargetEndpointRunsThroughRepresentativeImageW1357
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484) :
    exactAcyclic_of_compactTargetRelation_and_closedRangeOnlyProjection_w524
        hinputs hclosedOnly =
      exactAcyclic_of_representativeImage_and_closedRangeOnlyProjection_w524
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs)
        hclosedOnly :=
  rfl

theorem w525ClosedMapProviderEvaluatesClosedRangeOnlyW1357
    (hclosedMap : ComponentwiseClosedMapProviderW525)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs) :
    closedRangeOnlyProvider_of_closedMap_w525 hclosedMap S cs hcs =
      closedRangeOnlyInputs_of_closedMap_w525 (hclosedMap S cs hcs) :=
  rfl

theorem w525ClosedEmbeddingProviderEvaluatesClosedRangeOnlyW1357
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs) :
    closedRangeOnlyProvider_of_closedEmbedding_w525 hclosedEmbedding S cs hcs =
      closedRangeOnlyInputs_of_closedEmbedding_w525
        (hclosedEmbedding S cs hcs) :=
  rfl

theorem w525RepresentativeImageClosedMapEndpointRunsThroughW524W1357
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    exactAcyclic_of_representativeImage_closedMap_w525 hinputs hclosedMap =
      exactAcyclic_of_representativeImage_and_closedRangeOnlyProjection_w524
        hinputs (closedRangeOnlyProvider_of_closedMap_w525 hclosedMap) :=
  rfl

theorem w525TopTargetClosedEmbeddingEndpointRunsThroughW524W1357
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    exactAcyclic_of_topTargetRelation_closedEmbedding_w525
        hinputs hclosedEmbedding =
      exactAcyclic_of_topTargetRelation_and_closedRangeOnlyProjection_w524
        hinputs
        (closedRangeOnlyProvider_of_closedEmbedding_w525 hclosedEmbedding) :=
  rfl

theorem w525CompactTargetClosedMapEndpointRunsThroughW524W1357
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hclosedMap : ComponentwiseClosedMapProviderW525) :
    exactAcyclic_of_compactTargetRelation_closedMap_w525 hinputs hclosedMap =
      exactAcyclic_of_compactTargetRelation_and_closedRangeOnlyProjection_w524
        hinputs (closedRangeOnlyProvider_of_closedMap_w525 hclosedMap) :=
  rfl

theorem w525CompactTargetClosedEmbeddingEndpointRunsThroughW524W1357
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hclosedEmbedding : ComponentwiseClosedEmbeddingProviderW525) :
    exactAcyclic_of_compactTargetRelation_closedEmbedding_w525
        hinputs hclosedEmbedding =
      exactAcyclic_of_compactTargetRelation_and_closedRangeOnlyProjection_w524
        hinputs
        (closedRangeOnlyProvider_of_closedEmbedding_w525 hclosedEmbedding) :=
  rfl

structure MetrizableClosedRangeOnlyProviderNarrowingFieldSplitGuardStateW1357 :
    Type where
  seed : String
  inspectedBoundary : String
  inputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedRangeOnlyProviderNarrowingFieldSplitGuardStateW1357 :
    MetrizableClosedRangeOnlyProviderNarrowingFieldSplitGuardStateW1357 where
  seed := "w1357-closed-range-only-provider-narrowing-field-split-guard"
  inspectedBoundary :=
    "W523/W524/W525 provider narrowing from closed-nat-trans and relation\
      providers plus selected closed maps or embeddings into the W522 bridge"
  inputCount :=
    canonicalW523W524W525ProviderNarrowingInputNamesW1357.length
  providerSearchResult :=
    "proved: W523 relation data narrows through topology/package adapters,\
      W524 representative/top/compact relation data narrows through W523, and\
      W525 closed-map or closed-embedding providers narrow to W484\
      closed-range-only inputs before delegating exact-acyclic endpoints\
      through W524; this remains a two-input surface"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1357ClosedRangeOnlyProviderNarrowingFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableClosedRangeOnlyProviderNarrowingFieldSplitGuardStateW1357;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
