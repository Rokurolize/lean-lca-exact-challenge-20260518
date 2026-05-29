import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCompactTargetPreservationExitsFieldSplitGuardW1348
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1349 records the W516 top-target relation representative-image split. W516
uses relation-pullback plus the target relation being top to produce W515
representative-image inputs. This avoids the W512 target-lift field, but still
requires top-target relation data and selected preservation data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpSelectedCokernelColimitFromClosedRangeQuotientIdentificationV370SupportW514
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpTopTargetRelationRepresentativeImageV370SupportW516

namespace Dbounded

def canonicalW516TopTargetRelationInputNamesW1349 : List String :=
  ["relation-pullback condition for the ordinary descended quotient map",
    "target relation subgroup is top"]

theorem canonicalW516TopTargetRelationInputNamesW1349_count :
    canonicalW516TopTargetRelationInputNamesW1349.length = 2 :=
  rfl

theorem canonicalW516TopTargetRelationExpandsCurrentSurfaceW1349 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW516TopTargetRelationInputNamesW1349.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW516TopTargetRelationInputNamesW1349_count]
  norm_num

theorem w516RepresentativeImageInputPreservesPullbackW1349
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (H : ClosedNatTransOrdinaryTopTargetRelationInputsW516 α) :
    (representativeImageInputs_of_topTargetRelation_w516 H).relation_pullback =
      H.relation_pullback :=
  rfl

theorem w516RepresentativeImageProviderRunsThroughInputsW1349
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    representativeImageProvider_of_topTargetRelation_w516
        hinputs X Y α hclosed =
      representativeImageInputs_of_topTargetRelation_w516
        (hinputs X Y α hclosed) :=
  rfl

theorem w516ClosedRangeEndpointRunsThroughW515W1349
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_of_topTargetRelation_and_closedRangeQuotientIdentification_w516
        hinputs hclosed =
      exactAcyclic_of_representativeImage_and_closedRangeQuotientIdentification_w515
        (representativeImageProvider_of_topTargetRelation_w516 hinputs)
        hclosed :=
  rfl

theorem w516ComponentwiseEndpointRunsThroughW515W1349
    (hinputs : ClosedNatTransOrdinaryTopTargetRelationProviderW516)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_of_topTargetRelation_and_componentwiseProjection_w516
        hinputs hcomponentwise =
      exactAcyclic_of_representativeImage_and_componentwiseProjection_w515
        (representativeImageProvider_of_topTargetRelation_w516 hinputs)
        hcomponentwise :=
  rfl

theorem w516GenericTopRelationClosednessRouteW1349
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (htop : MetrizableLCA.cokernelSubgroup (f' - g') = ⊤) :
    MetrizableLCA.quotientRepresentativeImageClosedConditionW512 f g f' g' iB :=
  MetrizableLCA.quotientRepresentativeImageClosed_of_targetRelationTopW516 iB htop

structure MetrizableTopTargetRelationRepresentativeImageFieldSplitGuardStateW1349 :
    Type where
  seed : String
  inspectedBoundary : String
  topTargetInputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTopTargetRelationRepresentativeImageFieldSplitGuardStateW1349 :
    MetrizableTopTargetRelationRepresentativeImageFieldSplitGuardStateW1349 where
  seed := "w1349-top-target-relation-representative-image-field-split-guard"
  inspectedBoundary :=
    "W516 field split from relation-pullback and top target relation into W515\
      representative-image routes"
  topTargetInputCount :=
    canonicalW516TopTargetRelationInputNamesW1349.length
  providerSearchResult :=
    "proved: W516 preserves the relation-pullback field, uses top target\
      relation to produce representative-image closedness, and delegates\
      selected closed-range and componentwise projection exact-acyclic endpoints\
      through W515; this still requires top-target relation data plus selected\
      preservation data and does not discharge the current one-input W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1349TopTargetRelationRepresentativeImageFieldSplitGuard_productSuccess :
    (let state :=
      currentMetrizableTopTargetRelationRepresentativeImageFieldSplitGuardStateW1349;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
