import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSelectedColimitQuotientIdentificationFieldSplitGuardW1344
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1345 records the W520 single-preservation selected-colimit split. W520 turns
an original WPP-op colimit into the selected target cokernel colimit and then
uses one selected short-complex difference-cokernel preservation provider to
obtain W492's selected forgotten-target cokernel colimit. The route still
requires representative-image or compact-target relation data plus that
selected preservation provider, so it is nonterminal.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpRepresentativeImageClosedSelectedCokernelColimitV370SupportW515
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517
open WppOpCompactTargetRelationPreservationExitsV370SupportW518
open WppOpSelectedCokernelColimitFromSinglePreservationV370SupportW520

namespace Dbounded

def canonicalW520SinglePreservationInputNamesW1345 : List String :=
  ["representative-image or compact-target relation provider",
    "selected short-complex difference-cokernel preservation provider"]

theorem canonicalW520SinglePreservationInputNamesW1345_count :
    canonicalW520SinglePreservationInputNamesW1345.length = 2 :=
  rfl

theorem canonicalW520SinglePreservationExpandsCurrentSurfaceW1345 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW520SinglePreservationInputNamesW1345.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW520SinglePreservationInputNamesW1345_count]
  norm_num

theorem w520SinglePreservationProviderEvaluatesSelectedColimitW1345
    (hpres : SelectedShortComplexDifferenceCokernelPreservationProviderW520)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs) :
    selectedCokernelColimitProvider_of_singleDifferencePreservation_w520
        hpres S cs hcs =
      letI :
          PreservesColimit
            (parallelPair (selectedMetrizableLeft S - selectedMetrizableRight S) 0)
            forgottenShortComplexFunctor :=
        hpres S cs hcs
      selectedForgottenTargetCokernelColimitOfOriginalSinglePreservation_w520 S cs hcs :=
  rfl

theorem w520RepresentativeImageEndpointRunsThroughW515W1345
    (hinputs : ClosedNatTransOrdinaryRepresentativeImageProviderW515)
    (hpres : SelectedShortComplexDifferenceCokernelPreservationProviderW520) :
    exactAcyclic_of_representativeImage_and_singleDifferencePreservation_w520
        hinputs hpres =
      exactAcyclic_of_representativeImage_and_selectedCokernelColimit_w515 hinputs
        (selectedCokernelColimitProvider_of_singleDifferencePreservation_w520
          hpres) :=
  rfl

theorem w520CompactTargetEndpointRunsThroughW518W1345
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hpres : SelectedShortComplexDifferenceCokernelPreservationProviderW520) :
    exactAcyclic_of_compactTargetRelation_and_singleDifferencePreservation_w520
        hinputs hpres =
      exactAcyclic_of_compactTargetRelation_and_selectedCokernelColimit_w518
        hinputs
        (selectedCokernelColimitProvider_of_singleDifferencePreservation_w520
          hpres) :=
  rfl

theorem w520OriginalColimitFeedsSelectedCokernelW1345
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (hcs : IsColimit cs) :
    Nonempty (IsColimit (selectedMetrizableTargetCokernelCofork S cs)) :=
  ⟨selectedMetrizableTargetCokernelColimitOfOriginal_w520 S cs hcs⟩

structure MetrizableSinglePreservationSelectedColimitFieldSplitGuardStateW1345 :
    Type where
  seed : String
  inspectedBoundary : String
  inputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSinglePreservationSelectedColimitFieldSplitGuardStateW1345 :
    MetrizableSinglePreservationSelectedColimitFieldSplitGuardStateW1345 where
  seed := "w1345-single-preservation-selected-colimit-field-split-guard"
  inspectedBoundary :=
    "W520 field split from original WPP-op colimit data and one selected\
      short-complex difference-cokernel preservation provider into W492\
      selected cokernel-colimit routes"
  inputCount :=
    canonicalW520SinglePreservationInputNamesW1345.length
  providerSearchResult :=
    "proved: W520 converts original WPP-op colimit data to the selected target\
      cokernel colimit, evaluates one selected difference-cokernel preservation\
      provider into W492, and delegates representative-image and compact-target\
      exact-acyclic endpoints through W515/W518; this remains a two-input\
      provider surface and does not discharge the current one-input W987\
      obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1345SinglePreservationSelectedColimitFieldSplitGuard_productSuccess :
    (let state :=
      currentMetrizableSinglePreservationSelectedColimitFieldSplitGuardStateW1345;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
