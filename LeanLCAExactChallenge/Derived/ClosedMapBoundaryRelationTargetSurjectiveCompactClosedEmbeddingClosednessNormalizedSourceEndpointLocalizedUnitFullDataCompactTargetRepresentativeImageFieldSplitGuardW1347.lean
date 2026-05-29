import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedRangeMappedCokernelFieldSplitGuardW1346
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W1347 records the W517 compact-target representative-image split. W517 uses a
relation-pullback field and compactness of the target relation, together with
the closed component map from the closed natural transformation, to produce
W515 representative-image inputs. The route still requires a compact-target
relation provider and selected preservation data, so it remains nonterminal.
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
open WppOpCompactTargetRelationRepresentativeImageV370SupportW517

namespace Dbounded

def canonicalW517CompactTargetRelationInputNamesW1347 : List String :=
  ["relation-pullback condition for the ordinary descended quotient map",
    "compactness of the target relation subgroup"]

theorem canonicalW517CompactTargetRelationInputNamesW1347_count :
    canonicalW517CompactTargetRelationInputNamesW1347.length = 2 :=
  rfl

theorem canonicalW517CompactTargetRelationExpandsCurrentSurfaceW1347 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW517CompactTargetRelationInputNamesW1347.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW517CompactTargetRelationInputNamesW1347_count]
  norm_num

theorem w517RepresentativeImageInputPreservesPullbackW1347
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (H : ClosedNatTransOrdinaryCompactTargetRelationInputsW517 α) :
    (representativeImageInputs_of_compactTargetRelation_w517
        hclosed H).relation_pullback =
      H.relation_pullback :=
  rfl

theorem w517RepresentativeImageProviderRunsThroughInputsW1347
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (hclosed :
      ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) :
    representativeImageProvider_of_compactTargetRelation_w517
        hinputs X Y α hclosed =
      representativeImageInputs_of_compactTargetRelation_w517
        hclosed (hinputs X Y α hclosed) :=
  rfl

theorem w517ClosedRangeEndpointRunsThroughW515W1347
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_of_compactTargetRelation_and_closedRangeQuotientIdentification_w517
        hinputs hclosed =
      exactAcyclic_of_representativeImage_and_closedRangeQuotientIdentification_w515
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs)
        hclosed :=
  rfl

theorem w517ComponentwiseEndpointRunsThroughW515W1347
    (hinputs : ClosedNatTransOrdinaryCompactTargetRelationProviderW517)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_of_compactTargetRelation_and_componentwiseProjection_w517
        hinputs hcomponentwise =
      exactAcyclic_of_representativeImage_and_componentwiseProjection_w515
        (representativeImageProvider_of_compactTargetRelation_w517 hinputs)
        hcomponentwise :=
  rfl

theorem w517GenericClosednessRouteUsesTargetCompactW1347
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') (hcomponent : IsClosedMap (iB : B → B'))
    (hcompact : IsCompact (MetrizableLCA.cokernelSubgroup (f' - g') : Set B')) :
    MetrizableLCA.quotientRepresentativeImageClosedConditionW512 f g f' g' iB :=
  MetrizableLCA.quotientRepresentativeImageClosed_of_componentClosed_targetCompactW517
    iB hcomponent hcompact

structure MetrizableCompactTargetRepresentativeImageFieldSplitGuardStateW1347 :
    Type where
  seed : String
  inspectedBoundary : String
  compactTargetInputCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableCompactTargetRepresentativeImageFieldSplitGuardStateW1347 :
    MetrizableCompactTargetRepresentativeImageFieldSplitGuardStateW1347 where
  seed := "w1347-compact-target-representative-image-field-split-guard"
  inspectedBoundary :=
    "W517 field split from relation-pullback and target-relation compactness\
      into W515 representative-image routes"
  compactTargetInputCount :=
    canonicalW517CompactTargetRelationInputNamesW1347.length
  providerSearchResult :=
    "proved: W517 preserves the relation-pullback field, uses compactness of\
      the target relation plus the closed component map to produce\
      representative-image closedness, and delegates selected closed-range and\
      componentwise projection exact-acyclic endpoints through W515; this still\
      requires a compact-target relation provider plus selected preservation\
      data and does not discharge the current one-input W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1347CompactTargetRepresentativeImageFieldSplitGuard_productSuccess :
    (let state :=
      currentMetrizableCompactTargetRepresentativeImageFieldSplitGuardStateW1347;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
