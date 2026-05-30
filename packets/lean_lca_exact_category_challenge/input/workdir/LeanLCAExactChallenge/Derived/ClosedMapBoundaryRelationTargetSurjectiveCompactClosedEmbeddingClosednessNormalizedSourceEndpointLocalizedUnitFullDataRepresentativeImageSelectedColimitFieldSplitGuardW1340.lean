import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTopTargetRepresentativeImageFieldSplitGuardW1339
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1340 records the W515 representative-image selected-colimit field split. W515
turns relation-pullback and representative-image closedness inputs into W511
relation-topology inputs, then delegates exact-acyclic endpoints through the
selected cokernel-colimit route. The local boundary still exposes the
representative-image provider and one selected preservation provider, so it
does not close the current W987 obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportW489
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryDescendedQuotientV370SupportW510
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpSelectedCokernelColimitFromClosedRangeQuotientIdentificationV370SupportW514
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515

namespace Dbounded

def canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340 :
    List String :=
  ["relation-pullback condition for closed ordinary natural transformations",
    "representative-image closedness condition for the descended quotient map"]

theorem canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340_count :
    canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340.length =
      2 :=
  rfl

theorem canonicalW515RepresentativeImageSelectedColimitInnerExpandsCurrentSurfaceW1340 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340_count]
  norm_num

theorem w515RelationTopologyKeepsRelationPullbackW1340
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageInputsW515 α) :
    (closedNatTransOrdinaryRelationTopologyInputs_of_representativeImage_w515
        hclosed hinputs).relation_pullback =
      hinputs.relation_pullback :=
  rfl

theorem w515RelationTopologyClosedMapUsesRepresentativeImageW1340
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageInputsW515 α) :
    (closedNatTransOrdinaryRelationTopologyInputs_of_representativeImage_w515
        hclosed hinputs).descended_closedMap =
      MetrizableLCA.descendedQuotientMap_isClosedMap_of_representativeImageClosedW512
        ((ordinaryMapOfWppOpNatTransW506 α).app WalkingParallelPair.one)
        (ordinaryDescendedOfWppOpNatTransW510 α)
        (ordinaryDescendedOfWppOpNatTrans_quotient_compat_w510 α)
        hinputs.representative_image_closed :=
  rfl

theorem w515ProviderRunsThroughRelationTopologyInputsW1340
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    closedNatTransOrdinaryRelationTopologyProvider_of_representativeImage_w515
        hinputs X Y α hclosed =
      closedNatTransOrdinaryRelationTopologyInputs_of_representativeImage_w515
        hclosed (hinputs X Y α hclosed) :=
  rfl

theorem w515SelectedColimitEndpointRunsThroughW511W1340
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515
        hinputs hselected =
      exactAcyclic_of_relationTopology_and_selectedCokernelColimit_w511
        (closedNatTransOrdinaryRelationTopologyProvider_of_representativeImage_w515
          hinputs)
        hselected :=
  rfl

theorem w515QuotientIdentificationEndpointRunsThroughSelectedColimitW1340
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hquot : QuotientIdentificationProjectionProviderW485) :
    exactAcyclic_of_representativeImage_and_quotientIdentification_w515
        hinputs hquot =
      exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515 hinputs
        (selectedCokernelColimitProvider_of_quotientIdentification_w514 hquot) :=
  rfl

theorem w515ClosedRangeEndpointRunsThroughSelectedColimitW1340
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_of_representativeImage_and_closedRangeQuotientIdentification_w515
        hinputs hclosed =
      exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515 hinputs
        (selectedCokernelColimitProvider_of_closedRangeQuotientIdentification_w514
          hclosed) :=
  rfl

theorem w515ComponentwiseProjectionEndpointRunsThroughSelectedColimitW1340
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_of_representativeImage_and_componentwiseProjection_w515
        hinputs hcomponentwise =
      exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515 hinputs
        (selectedCokernelColimitProvider_of_componentwiseProjection_w514
          hcomponentwise) :=
  rfl

structure MetrizableRepresentativeImageSelectedColimitFieldSplitGuardStateW1340 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableRepresentativeImageSelectedColimitFieldSplitGuardStateW1340 :
    MetrizableRepresentativeImageSelectedColimitFieldSplitGuardStateW1340 where
  seed := "w1340-representative-image-selected-colimit-field-split-guard"
  inspectedBoundary :=
    "W515 field split from representative-image data into W511\
      relation-topology and selected colimit endpoints"
  innerSurfaceCount :=
    canonicalW515RepresentativeImageSelectedColimitInnerInputNamesW1340.length
  providerSearchResult :=
    "proved: W515 preserves relation-pullback data, converts\
      representative-image closedness into W511 descended-closed-map data, and\
      delegates selected exact-acyclic endpoints through W511/W514, but the\
      local boundary still exposes two inner fields plus a selected preservation\
      provider and does not discharge the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1340RepresentativeImageSelectedColimitFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableRepresentativeImageSelectedColimitFieldSplitGuardStateW1340;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
