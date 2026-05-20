import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W411: representative-image closedness support for the ordinary descended map.

This standalone audit file mirrors W408's representative-image set shape and
closes it from two local inputs:

* the ordinary component on codomains is a closed map;
* the resulting representative image is saturated for the target quotient map.

This proves the closed-saturated-set reduction needed by W408 without claiming
the remaining target-saturation input.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaRepresentativeImageClosednessV370SupportW411

universe u

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW411 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- For any quotient map, closed saturated sets have closed images. -/
theorem image_closed_of_isQuotientMap_and_saturatedW411
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsQuotientMap q) {S : Set α}
    (hS : IsClosed S) (hsaturated : IsSaturatedForW411 q S) :
    IsClosed (q '' S) := by
  have hpre_eq : q ⁻¹' (q '' S) = S := by
    apply le_antisymm hsaturated
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hpre_closed : IsClosed (q ⁻¹' (q '' S)) := by
    simpa [hpre_eq] using hS
  exact hq.1.isClosed_preimage.mp hpre_closed

/-- The local quotient map is a topological quotient map. -/
theorem quotientMap_isQuotientMapW411
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X)) :
    IsQuotientMap (MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) := by
  change IsQuotientMap (QuotientAddGroup.mk' N : X → X ⧸ N)
  exact QuotientAddGroup.isQuotientMap_mk N

/-- The quotient projection closes closed saturated representative sets. -/
theorem quotientMap_image_closed_of_closed_saturatedW411
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X} (hS : IsClosed S)
    (hsaturated :
      IsSaturatedForW411
        (MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) S) :
    IsClosed ((MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) '' S) := by
  exact image_closed_of_isQuotientMap_and_saturatedW411
    (quotientMap_isQuotientMapW411 X N hN) hS hsaturated

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagram (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeft (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRight (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.right

/-- The ordinary quotient point used by W408's concrete descended map. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/--
W408's representative-image closedness condition, repeated here because
`audit/blockers` scripts are not Lake-importable modules.
-/
abbrev ordinaryDescendedRepresentativeImageClosedConditionW411
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ C : Set (wppOpOrdinaryQuotientPoint X), IsClosed C →
    IsClosed
      ((MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) :
          wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y) ''
        (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
          ((MetrizableLCA.quotientMap (wppOpCodomain X)
              (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
              (AddSubgroup.isClosed_topologicalClosure _) :
              wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C)))

/--
Minimal remaining input: for every closed source quotient set, its mapped
representative image is saturated for the target quotient projection.
-/
abbrev ordinaryDescendedRepresentativeImageSaturatedConditionW411
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ C : Set (wppOpOrdinaryQuotientPoint X), IsClosed C →
    IsSaturatedForW411
      (MetrizableLCA.quotientMap (wppOpCodomain Y)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
        (AddSubgroup.isClosed_topologicalClosure _) :
        wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y)
      (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
        ((MetrizableLCA.quotientMap (wppOpCodomain X)
            (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
            (AddSubgroup.isClosed_topologicalClosure _) :
            wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C))

/--
Closed component map plus target saturation proves W408's representative-image
closedness condition.
-/
theorem ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW411
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hcomponent :
      IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
        wppOpCodomain X → wppOpCodomain Y))
    (hsaturated :
      ordinaryDescendedRepresentativeImageSaturatedConditionW411 ordinaryMap) :
    ordinaryDescendedRepresentativeImageClosedConditionW411 ordinaryMap := by
  intro C hC
  let qsource :
      wppOpCodomain X → wppOpOrdinaryQuotientPoint X :=
    MetrizableLCA.quotientMap (wppOpCodomain X)
      (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
      (AddSubgroup.isClosed_topologicalClosure _)
  let qtarget :
      wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y :=
    MetrizableLCA.quotientMap (wppOpCodomain Y)
      (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
      (AddSubgroup.isClosed_topologicalClosure _)
  let representativeImage : Set (wppOpCodomain Y) :=
    ((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
      (qsource ⁻¹' C)
  have hpre_closed : IsClosed (qsource ⁻¹' C) := by
    exact hC.preimage
      (MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.continuous
  have hrep_closed : IsClosed representativeImage := by
    exact hcomponent (qsource ⁻¹' C) hpre_closed
  have hrep_saturated : IsSaturatedForW411 qtarget representativeImage := by
    exact hsaturated C hC
  exact quotientMap_image_closed_of_closed_saturatedW411
    (wppOpCodomain Y)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
    (AddSubgroup.isClosed_topologicalClosure _)
    hrep_closed hrep_saturated

/--
Closed embedding is a sufficient source of the component closed-map input.
-/
theorem ordinaryDescendedRepresentativeImageClosed_of_componentClosedEmbedding_targetSaturatedW411
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hcomponent :
      IsClosedEmbedding ((ordinaryMap.app WalkingParallelPair.one) :
        wppOpCodomain X → wppOpCodomain Y))
    (hsaturated :
      ordinaryDescendedRepresentativeImageSaturatedConditionW411 ordinaryMap) :
    ordinaryDescendedRepresentativeImageClosedConditionW411 ordinaryMap :=
  ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW411
    ordinaryMap hcomponent.isClosedMap hsaturated

/--
Checked consumer shape for W408: a caller with W408's representative-image
consumer can combine it with the W411 bridge to obtain the desired closed-map
field.
-/
theorem ordinaryDescendedClosedMap_consumer_of_componentClosed_targetSaturatedW411
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (hcomponent :
      IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
        wppOpCodomain X → wppOpCodomain Y))
    (hsaturated :
      ordinaryDescendedRepresentativeImageSaturatedConditionW411 ordinaryMap)
    (consume :
      ordinaryDescendedRepresentativeImageClosedConditionW411 ordinaryMap →
        IsClosedMap (ordinaryDescended :
          wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)) :
    IsClosedMap (ordinaryDescended :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) :=
  consume
    (ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW411
      ordinaryMap hcomponent hsaturated)

/-- Remaining inputs after W411 closes representative-image closedness from saturation. -/
def remainingRepresentativeImageClosednessInputsW411 : List String :=
  ["component closed-map or closed-embedding field for the ordinary codomain component",
    "target representative-image saturation for each closed source quotient set"]

theorem remainingRepresentativeImageClosednessInputsW411_count :
    remainingRepresentativeImageClosednessInputsW411.length = 2 := rfl

/-- Declaration names exported by this W411 support layer. -/
def w411SupportDeclarationNames : List String :=
  ["IsSaturatedForW411",
    "image_closed_of_isQuotientMap_and_saturatedW411",
    "quotientMap_isQuotientMapW411",
    "quotientMap_image_closed_of_closed_saturatedW411",
    "ordinaryDescendedRepresentativeImageClosedConditionW411",
    "ordinaryDescendedRepresentativeImageSaturatedConditionW411",
    "ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW411",
    "ordinaryDescendedRepresentativeImageClosed_of_componentClosedEmbedding_targetSaturatedW411",
    "ordinaryDescendedClosedMap_consumer_of_componentClosed_targetSaturatedW411",
    "remainingRepresentativeImageClosednessInputsW411"]

theorem w411SupportDeclarationNames_count :
    w411SupportDeclarationNames.length = 10 := rfl

structure WppOpLeftLcaRepresentativeImageClosednessV370StateW411 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  representativeImageClosednessResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaRepresentativeImageClosednessV370StateW411 :
    WppOpLeftLcaRepresentativeImageClosednessV370StateW411 where
  seed := "CbiijIwM93rDzwLuLsAvltJb"
  checkedFacts :=
    ["proved closed saturated sets have closed image under the target quotient projection",
      "matched W408's ordinary representative-image set shape",
      "proved component closed-map plus target representative-image saturation implies representative-image closedness",
      "provided a checked consumer shape for W408's representative-image closedness consumer"]
  remainingInputs := remainingRepresentativeImageClosednessInputsW411
  representativeImageClosednessResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaRepresentativeImageClosednessV370StateW411_productSuccess :
    currentWppOpLeftLcaRepresentativeImageClosednessV370StateW411.productSuccessClaimed = false := rfl

section Checks

#check IsSaturatedForW411
#check image_closed_of_isQuotientMap_and_saturatedW411
#check quotientMap_isQuotientMapW411
#check quotientMap_image_closed_of_closed_saturatedW411
#check ordinaryDescendedRepresentativeImageClosedConditionW411
#check ordinaryDescendedRepresentativeImageSaturatedConditionW411
#check ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW411
#check ordinaryDescendedRepresentativeImageClosed_of_componentClosedEmbedding_targetSaturatedW411
#check ordinaryDescendedClosedMap_consumer_of_componentClosed_targetSaturatedW411
#check remainingRepresentativeImageClosednessInputsW411
#check remainingRepresentativeImageClosednessInputsW411_count
#check w411SupportDeclarationNames
#check w411SupportDeclarationNames_count
#check currentWppOpLeftLcaRepresentativeImageClosednessV370StateW411
#check currentWppOpLeftLcaRepresentativeImageClosednessV370StateW411_productSuccess

end Checks

end WppOpLeftLcaRepresentativeImageClosednessV370SupportW411

end LeanLCAExactChallenge
