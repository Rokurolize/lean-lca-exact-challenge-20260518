import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataTopTargetCompactSpaceFieldSplitGuardW1338
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1339 records the W516 top-target representative-image field split. W516
packages relation-pullback and target-relation-top data into W515
representative-image inputs, then delegates exact-acyclic endpoints through W515.
The local provider boundary still has two inner fields and the selected route
still needs one preservation provider, so it does not close the current W987
obligation.
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
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpTopTargetRelationRepresentativeImageV370SupportW516

namespace Dbounded

def canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339 :
    List String :=
  ["relation-pullback condition for closed ordinary natural transformations",
    "target-relation-top condition for the ordinary target quotient"]

theorem canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339_count :
    canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339.length =
      2 :=
  rfl

theorem canonicalW516TopTargetRepresentativeImageInnerExpandsCurrentSurfaceW1339 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339_count]
  norm_num

theorem w516RepresentativeImageKeepsRelationPullbackW1339
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (H : ClosedNatTransOrdinaryTopTargetRelationInputsW516 α) :
    (representativeImageInputs_of_topTargetRelation_w516 H).relation_pullback =
      H.relation_pullback :=
  rfl

theorem w516RepresentativeImageClosedUsesTargetTopW1339
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (H : ClosedNatTransOrdinaryTopTargetRelationInputsW516 α) :
    (representativeImageInputs_of_topTargetRelation_w516
        H).representative_image_closed =
      MetrizableLCA.quotientRepresentativeImageClosed_of_targetRelationTopW516
        ((ordinaryMapOfWppOpNatTransW506 α).app WalkingParallelPair.one)
        H.target_relation_top :=
  rfl

theorem w516ProviderRunsThroughRepresentativeImageInputsW1339
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    representativeImageProvider_of_topTargetRelation_w516 hinputs X Y α hclosed =
      representativeImageInputs_of_topTargetRelation_w516
        (hinputs X Y α hclosed) :=
  rfl

theorem w516ClosedRangeQuotientEndpointRunsThroughW515W1339
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_of_topTargetRelation_and_closedRangeQuotientIdentification_w516
        hinputs hclosed =
      exactAcyclic_of_representativeImage_and_closedRangeQuotientIdentification_w515
        (representativeImageProvider_of_topTargetRelation_w516 hinputs)
        hclosed :=
  rfl

theorem w516ComponentwiseProjectionEndpointRunsThroughW515W1339
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_of_topTargetRelation_and_componentwiseProjection_w516
        hinputs hcomponentwise =
      exactAcyclic_of_representativeImage_and_componentwiseProjection_w515
        (representativeImageProvider_of_topTargetRelation_w516 hinputs)
        hcomponentwise :=
  rfl

structure MetrizableTopTargetRepresentativeImageFieldSplitGuardStateW1339 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTopTargetRepresentativeImageFieldSplitGuardStateW1339 :
    MetrizableTopTargetRepresentativeImageFieldSplitGuardStateW1339 where
  seed := "w1339-top-target-representative-image-field-split-guard"
  inspectedBoundary :=
    "W516 field split from relation-pullback and target-top data into W515\
      representative-image routes"
  innerSurfaceCount :=
    canonicalW516TopTargetRepresentativeImageInnerInputNamesW1339.length
  providerSearchResult :=
    "proved: W516 preserves relation-pullback data, converts target-top data\
      into the W515 representative-image closedness condition, and delegates\
      selected exact-acyclic endpoints through W515, but the local boundary\
      still exposes two inner fields plus a selected preservation provider and\
      does not discharge the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1339TopTargetRepresentativeImageFieldSplitGuard_productSuccess :
    (let state :=
        currentMetrizableTopTargetRepresentativeImageFieldSplitGuardStateW1339;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
