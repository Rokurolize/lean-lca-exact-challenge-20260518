import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataCompactTargetRepresentativeImageFieldSplitGuardW1347
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1348 records the W518 compact-target preservation-exits split. W518 exposes
W517 compact-target relation data through W515 selected-preservation exits and
through W511 mapped-explicit and closure-kernel exits. This remains a routing
boundary: it still requires a compact-target relation provider and one selected
or global preservation input.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpCompactTargetRelationPreservationExitsV370SupportW518

namespace Dbounded

def canonicalW518CompactTargetExitNamesW1348 : List String :=
  ["selected cokernel-colimit provider exit",
    "quotient-identification selected provider exit",
    "mapped explicit cokernel coforks exit",
    "closure-kernel provider exit"]

theorem canonicalW518CompactTargetExitNamesW1348_count :
    canonicalW518CompactTargetExitNamesW1348.length = 4 :=
  rfl

theorem canonicalW518CompactTargetExitsExpandCurrentSurfaceW1348 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW518CompactTargetExitNamesW1348.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW518CompactTargetExitNamesW1348_count]
  norm_num

theorem w518RelationTopologyProviderRunsThroughW515W1348
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517) :
    relationTopologyProvider_of_compactTargetRelation_w518 hinputs =
      closedNatTransOrdinaryRelationTopologyProvider_of_representativeImage_w515
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs) :=
  rfl

theorem w518SelectedColimitExitRunsThroughW515W1348
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_of_compactTargetRelation_and_selectedCokernelColimit_w518
        hinputs hselected =
      exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs)
        hselected :=
  rfl

theorem w518QuotientIdentificationExitRunsThroughW515W1348
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hquot : QuotientIdentificationProjectionProviderW485) :
    exactAcyclic_of_compactTargetRelation_and_quotientIdentification_w518
        hinputs hquot =
      exactAcyclic_of_representativeImage_and_quotientIdentification_w515
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs)
        hquot :=
  rfl

theorem w518MappedExplicitExitRunsThroughW511W1348
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_of_compactTargetRelation_and_mappedExplicitCokernelCoforks_w518
        hinputs hMapped =
      exactAcyclic_of_relationTopology_and_mappedExplicitCokernelCoforks_w511
        (relationTopologyProvider_of_compactTargetRelation_w518 hinputs) hMapped :=
  rfl

theorem w518ClosureKernelExitRunsThroughW511W1348
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hClosure : MappedExplicitCokernelClosureKernelProviderW503) :
    exactAcyclic_of_compactTargetRelation_and_closureKernelProvider_w518
        hinputs hClosure =
      exactAcyclic_of_relationTopology_and_closureKernelProvider_w511
        (relationTopologyProvider_of_compactTargetRelation_w518 hinputs) hClosure :=
  rfl

structure MetrizableCompactTargetPreservationExitsFieldSplitGuardStateW1348 :
    Type where
  seed : String
  inspectedBoundary : String
  exitCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCompactTargetPreservationExitsFieldSplitGuardStateW1348 :
    MetrizableCompactTargetPreservationExitsFieldSplitGuardStateW1348 where
  seed := "w1348-compact-target-preservation-exits-field-split-guard"
  inspectedBoundary :=
    "W518 field split from compact-target relation data into selected,\
      quotient-identification, mapped-explicit, and closure-kernel exits"
  exitCount := canonicalW518CompactTargetExitNamesW1348.length
  providerSearchResult :=
    "proved: W518 routes compact-target relation data through W515 for selected\
      preservation exits and through W511 for mapped-explicit and closure-kernel\
      exits; this still requires compact-target relation data plus one\
      preservation provider and does not discharge the current one-input W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1348CompactTargetPreservationExitsFieldSplitGuard_productSuccess :
    (let state :=
      currentMetrizableCompactTargetPreservationExitsFieldSplitGuardStateW1348;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
