import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W414: representative-image saturation support for W411.

This standalone audit file proves W411's remaining saturation input from the
two algebraic relation fields:

* relation-pullback equality for the source and target cokernel relations;
* target-relation lifting through the ordinary codomain component.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaRepresentativeImageSaturationV370SupportW414

universe u

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW414 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

namespace ConcreteMetrizableLCA

open LeanLCAExactChallenge.MetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- W414 spelling of relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW414
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W414 spelling of the target-relation lift input. -/
abbrev targetRelationLiftsThroughComponentW414
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
Adding a source-relation element does not change the source quotient class.
This is the small quotient lemma isolated by the W414 task.
-/
theorem quotientMap_add_relation_eqW414
    {f g : A ⟶ B} {x d : B}
    (hd : d ∈ cokernelSubgroup (f - g)) :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) (x + d) =
      quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) x := by
  change ((x + d : B) : B ⧸ cokernelSubgroup (f - g)) =
    ((x : B) : B ⧸ cokernelSubgroup (f - g))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa [add_sub_cancel_left] using hd

/--
The image of source representatives is saturated for the target quotient when
target relation elements lift through `iB` and the lifted elements are exactly
the source relation by pullback equality.
-/
theorem representativeImageSaturated_of_relationPullback_targetLiftsW414
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW414 f g f' g' iB)
    (htarget : targetRelationLiftsThroughComponentW414 f' g' iB)
    (C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _))) :
    IsSaturatedForW414
      (quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :
        B' → quotientObj B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))
      (((iB : B → B') ''
        ((quotientMap B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) :
          B → quotientObj B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C))) := by
  intro y hy
  rcases hy with ⟨z, hz, hqyz⟩
  rcases hz with ⟨x, hxC, rfl⟩
  have hrel_target : y - iB x ∈ cokernelSubgroup (f' - g') := by
    change ((iB x : B') : B' ⧸ cokernelSubgroup (f' - g')) =
      ((y : B') : B' ⧸ cokernelSubgroup (f' - g')) at hqyz
    exact QuotientAddGroup.eq_iff_sub_mem.mp hqyz.symm
  rcases htarget (y - iB x) hrel_target with ⟨d, hd_image⟩
  have hd_target : iB d ∈ cokernelSubgroup (f' - g') := by
    simpa [hd_image] using hrel_target
  have hd_source : d ∈ cokernelSubgroup (f - g) := by
    have hd_comap :
        d ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) :=
      hd_target
    simpa [relationPreimagePullbackConditionW414] using (hpullback ▸ hd_comap)
  refine ⟨x + d, ?_, ?_⟩
  · change quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) (x + d) ∈ C
    rw [quotientMap_add_relation_eqW414 (f := f) (g := g) (x := x) (d := d) hd_source]
    exact hxC
  · calc
      iB (x + d) = iB x + iB d := by
        exact map_add iB.hom.toAddMonoidHom x d
      _ = iB x + (y - iB x) := by rw [hd_image]
      _ = y := by abel

end ConcreteMetrizableLCA

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

/-- The ordinary quotient point used by W408/W411's concrete descended map. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W414 WPP-op relation-pullback equality. -/
abbrev relationPreimagePullbackConditionW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ConcreteMetrizableLCA.relationPreimagePullbackConditionW414
    (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)

/-- W414 WPP-op target-relation lift input. -/
abbrev targetRelationLiftsThroughComponentW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ConcreteMetrizableLCA.targetRelationLiftsThroughComponentW414
    (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)

/--
W411's representative-image saturation condition, repeated here because
`audit/blockers` scripts are standalone Lean files.
-/
abbrev ordinaryDescendedRepresentativeImageSaturatedConditionW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ C : Set (wppOpOrdinaryQuotientPoint X), IsClosed C →
    IsSaturatedForW414
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
Relation-pullback equality plus target-relation lifting proves W411's remaining
representative-image saturation condition.
-/
theorem ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hpullback : relationPreimagePullbackConditionW414 ordinaryMap)
    (htarget : targetRelationLiftsThroughComponentW414 ordinaryMap) :
    ordinaryDescendedRepresentativeImageSaturatedConditionW414 ordinaryMap := by
  intro C _hC
  exact ConcreteMetrizableLCA.representativeImageSaturated_of_relationPullback_targetLiftsW414
    (ordinaryMap.app WalkingParallelPair.one) hpullback htarget C

/-- W401-shaped relation-field package sufficient for representative-image saturation. -/
structure RepresentativeImageSaturationRelationFieldsW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  relation_pullback : relationPreimagePullbackConditionW414 ordinaryMap
  target_relation_lifts : targetRelationLiftsThroughComponentW414 ordinaryMap

/-- W401-shaped fields prove W411's target-saturation input. -/
theorem ordinaryDescendedRepresentativeImageSaturated_of_relationFieldsW414
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : RepresentativeImageSaturationRelationFieldsW414 ordinaryMap) :
    ordinaryDescendedRepresentativeImageSaturatedConditionW414 ordinaryMap :=
  ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW414
    ordinaryMap h.relation_pullback h.target_relation_lifts

/-- Remaining inputs after W414 closes representative-image saturation. -/
def remainingRepresentativeImageSaturationInputsW414 : List String :=
  ["for callers: relation-pullback equality for source and target cokernel relations",
    "for callers: target-relation lifting through the ordinary codomain component"]

theorem remainingRepresentativeImageSaturationInputsW414_count :
    remainingRepresentativeImageSaturationInputsW414.length = 2 := rfl

/-- Declaration names exported by this W414 support layer. -/
def w414SupportDeclarationNames : List String :=
  ["IsSaturatedForW414",
    "ConcreteMetrizableLCA.quotientMap_add_relation_eqW414",
    "ConcreteMetrizableLCA.representativeImageSaturated_of_relationPullback_targetLiftsW414",
    "ordinaryDescendedRepresentativeImageSaturatedConditionW414",
    "ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW414",
    "RepresentativeImageSaturationRelationFieldsW414",
    "ordinaryDescendedRepresentativeImageSaturated_of_relationFieldsW414",
    "remainingRepresentativeImageSaturationInputsW414"]

theorem w414SupportDeclarationNames_count :
    w414SupportDeclarationNames.length = 8 := rfl

structure WppOpLeftLcaRepresentativeImageSaturationV370StateW414 : Type where
  seed : String
  checkedFacts : List String
  representativeImageSaturationResult : String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaRepresentativeImageSaturationV370StateW414 :
    WppOpLeftLcaRepresentativeImageSaturationV370StateW414 where
  seed := "saffron-lattice-4938"
  checkedFacts :=
    ["proved adding a source-relation element does not change the source quotient class",
      "proved target quotient equality plus target-relation lifting rewrites a target representative as iB (x + d)",
      "used relation-pullback equality to show the lifted d is a source-relation element",
      "proved W411-shaped representative-image saturation from relation-pullback equality and target-relation lifting"]
  representativeImageSaturationResult := "proved"
  remainingInputs := remainingRepresentativeImageSaturationInputsW414
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaRepresentativeImageSaturationV370StateW414_productSuccess :
    currentWppOpLeftLcaRepresentativeImageSaturationV370StateW414.productSuccessClaimed = false := rfl

section Checks

#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.IsSaturatedForW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.ConcreteMetrizableLCA.quotientMap_add_relation_eqW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.ConcreteMetrizableLCA.representativeImageSaturated_of_relationPullback_targetLiftsW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.ordinaryDescendedRepresentativeImageSaturatedConditionW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.RepresentativeImageSaturationRelationFieldsW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.ordinaryDescendedRepresentativeImageSaturated_of_relationFieldsW414
#check WppOpLeftLcaRepresentativeImageSaturationV370SupportW414.currentWppOpLeftLcaRepresentativeImageSaturationV370StateW414_productSuccess

end Checks

end WppOpLeftLcaRepresentativeImageSaturationV370SupportW414

end LeanLCAExactChallenge
