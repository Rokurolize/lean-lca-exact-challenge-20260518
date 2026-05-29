import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataDescendedQuotientTopologyFactsFieldSplitGuardW1342
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1343 records the W512 relation-fields closed-map split. W512 replaces W511's
descended closed-map input by a target-relation lift field plus the existing
relation-pullback field, using closedness of the natural-transformation
component to obtain the descended closed-map fact. The local surface remains a
two-field relation package plus a preservation provider, so it does not close
the current W987 one-input obligation.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryDescendedQuotientV370SupportW510
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpClosedNatTransOrdinaryRelationFieldObstructionV370SupportW513

namespace Dbounded

def canonicalW512RelationFieldsInputNamesW1343 : List String :=
  ["relation-pullback condition for the ordinary descended quotient map",
    "target relation lifts through the ordinary codomain component"]

theorem canonicalW512RelationFieldsInputNamesW1343_count :
    canonicalW512RelationFieldsInputNamesW1343.length = 2 :=
  rfl

theorem canonicalW512RelationFieldsExpandsCurrentSurfaceW1343 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW512RelationFieldsInputNamesW1343.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW512RelationFieldsInputNamesW1343_count]
  norm_num

theorem w512RelationTopologyInputPreservesPullbackW1343
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hinputs : ClosedNatTransOrdinaryRelationFieldsInputsW512 α) :
    (closedNatTransOrdinaryRelationTopologyInputs_of_relationFields_w512
        hclosed hinputs).relation_pullback =
      hinputs.relation_pullback :=
  rfl

theorem w512ProviderRunsThroughRelationTopologyW1343
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    closedNatTransOrdinaryRelationTopologyProvider_of_relationFields_w512
        hinputs X Y α hclosed =
      closedNatTransOrdinaryRelationTopologyInputs_of_relationFields_w512
        hclosed (hinputs X Y α hclosed) :=
  rfl

theorem w512TopologyFactsProviderRunsThroughW511W1343
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512) :
    closedNatTransOrdinaryTopologyFactsProvider_of_relationFields_w512 hinputs =
      closedNatTransOrdinaryTopologyFactsProvider_of_relationTopology_w511
        (closedNatTransOrdinaryRelationTopologyProvider_of_relationFields_w512
          hinputs) :=
  rfl

theorem w512SelectedColimitEndpointRunsThroughW511W1343
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_of_relationFields_and_selectedCokernelColimit_w512
        hinputs hselected =
      exactAcyclic_of_relationTopology_and_selectedCokernelColimit_w511
        (closedNatTransOrdinaryRelationTopologyProvider_of_relationFields_w512
          hinputs)
        hselected :=
  rfl

theorem w512MappedExplicitEndpointRunsThroughW511W1343
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_of_relationFields_and_mappedExplicitCokernelCoforks_w512
        hinputs hMapped =
      exactAcyclic_of_relationTopology_and_mappedExplicitCokernelCoforks_w511
        (closedNatTransOrdinaryRelationTopologyProvider_of_relationFields_w512
          hinputs)
        hMapped :=
  rfl

theorem w512ClosureKernelEndpointRunsThroughW511W1343
    (hinputs : ClosedNatTransOrdinaryRelationFieldsProviderW512)
    (hClosure : MappedExplicitCokernelClosureKernelProviderW503) :
    exactAcyclic_of_relationFields_and_closureKernelProvider_w512
        hinputs hClosure =
      exactAcyclic_of_relationTopology_and_closureKernelProvider_w511
        (closedNatTransOrdinaryRelationTopologyProvider_of_relationFields_w512
          hinputs)
        hClosure :=
  rfl

theorem w512TopRelationLiftFieldImpliesSurjectivityW1343
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hfields : ClosedNatTransOrdinaryRelationFieldsInputsW512 α)
    (htop :
      MetrizableLCA.cokernelSubgroup (wppOpLeftW441 Y - wppOpRightW441 Y) = ⊤) :
    Function.Surjective
      (((ordinaryMapOfWppOpNatTransW506 α).app WalkingParallelPair.one) :
        wppOpCodomainW441 X → wppOpCodomainW441 Y) :=
  (closedNatTransOrdinaryRelationFields_topRelationConsequences_w513
    hfields htop).1

structure MetrizableRelationFieldsClosedMapFieldSplitGuardStateW1343 : Type where
  seed : String
  inspectedBoundary : String
  relationFieldCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableRelationFieldsClosedMapFieldSplitGuardStateW1343 :
    MetrizableRelationFieldsClosedMapFieldSplitGuardStateW1343 where
  seed := "w1343-relation-fields-closed-map-field-split-guard"
  inspectedBoundary :=
    "W512 field split from relation-pullback and target-relation-lift data into\
      W511 relation-topology routes"
  relationFieldCount :=
    canonicalW512RelationFieldsInputNamesW1343.length
  providerSearchResult :=
    "proved: W512 preserves the relation-pullback field, derives W511\
      relation-topology inputs from closed component maps plus target-relation\
      lifts, delegates selected, mapped-explicit, and closure-kernel\
      exact-acyclic endpoints through W511, and W513 shows the target-relation\
      lift can be surjectivity-level in the top-relation case; this does not\
      discharge the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1343RelationFieldsClosedMapFieldSplitGuard_productSuccess :
    (let state := currentMetrizableRelationFieldsClosedMapFieldSplitGuardStateW1343;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
