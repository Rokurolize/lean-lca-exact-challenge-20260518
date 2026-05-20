import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W417: closed-map composer from relation fields.

This standalone audit file composes the W411 and W414 support shapes into a
W408-shaped closed-map consumer.  The final relation-field package contains the
three concrete fields needed for the ordinary descended map:

* the ordinary codomain component is a closed map;
* the target relation pulls back to the source relation;
* every target relation element lifts through the ordinary codomain component.

The file repeats the minimal W408/W411/W414 definitions locally because
`audit/blockers` files are checked as standalone Lean scripts.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417

universe u

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

/-- The ordinary quotient point used by the concrete descended map. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W408/W414 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  AddSubgroup.comap (ordinaryMap.app WalkingParallelPair.one).hom.toAddMonoidHom
      (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y)) =
    MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X)

/-- W414 target-relation lift input. -/
abbrev targetRelationLiftsThroughComponentW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ n : wppOpCodomain Y, n ∈ MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y) →
    ∃ d : wppOpCodomain X, ordinaryMap.app WalkingParallelPair.one d = n

/-- W401/W395-shaped package for the closed-map composer. -/
structure ClosedMapRelationFieldsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  component_closedMap :
    IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
      wppOpCodomain X → wppOpCodomain Y)
  relation_pullback : relationPreimagePullbackConditionW417 ordinaryMap
  target_relation_lifts : targetRelationLiftsThroughComponentW417 ordinaryMap

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW417 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- For any quotient map, closed saturated sets have closed images. -/
theorem image_closed_of_isQuotientMap_and_saturatedW417
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsQuotientMap q) {S : Set α}
    (hS : IsClosed S) (hsaturated : IsSaturatedForW417 q S) :
    IsClosed (q '' S) := by
  have hpre_eq : q ⁻¹' (q '' S) = S := by
    apply le_antisymm hsaturated
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hpre_closed : IsClosed (q ⁻¹' (q '' S)) := by
    simpa [hpre_eq] using hS
  exact hq.1.isClosed_preimage.mp hpre_closed

/-- The local quotient map is a topological quotient map. -/
theorem quotientMap_isQuotientMapW417
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X)) :
    IsQuotientMap (MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) := by
  change IsQuotientMap (QuotientAddGroup.mk' N : X → X ⧸ N)
  exact QuotientAddGroup.isQuotientMap_mk N

/-- The quotient projection closes closed saturated representative sets. -/
theorem quotientMap_image_closed_of_closed_saturatedW417
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X} (hS : IsClosed S)
    (hsaturated :
      IsSaturatedForW417
        (MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) S) :
    IsClosed ((MetrizableLCA.quotientMap X N hN : X → MetrizableLCA.quotientObj X N hN) '' S) := by
  exact image_closed_of_isQuotientMap_and_saturatedW417
    (quotientMap_isQuotientMapW417 X N hN) hS hsaturated

/-- Adding a source-relation element does not change the source quotient class. -/
theorem quotientMap_add_relation_eqW417
    {A B : MetrizableLCA.{0}} {f g : A ⟶ B} {x d : B}
    (hd : d ∈ MetrizableLCA.cokernelSubgroup (f - g)) :
    MetrizableLCA.quotientMap B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) (x + d) =
      MetrizableLCA.quotientMap B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) x := by
  change ((x + d : B) : B ⧸ MetrizableLCA.cokernelSubgroup (f - g)) =
    ((x : B) : B ⧸ MetrizableLCA.cokernelSubgroup (f - g))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa [add_sub_cancel_left] using hd

/--
Relation-pullback equality plus target-relation lifting proves saturation of
the target representative image.
-/
theorem representativeImageSaturated_of_relationPullback_targetLiftsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hpullback : relationPreimagePullbackConditionW417 ordinaryMap)
    (htarget : targetRelationLiftsThroughComponentW417 ordinaryMap)
    (C : Set (wppOpOrdinaryQuotientPoint X)) :
    IsSaturatedForW417
      (MetrizableLCA.quotientMap (wppOpCodomain Y)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
        (AddSubgroup.isClosed_topologicalClosure _) :
        wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y)
      (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
        ((MetrizableLCA.quotientMap (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) :
          wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C)) := by
  intro y hy
  rcases hy with ⟨z, hz, hqyz⟩
  rcases hz with ⟨x, hxC, rfl⟩
  have hrel_target : y - ordinaryMap.app WalkingParallelPair.one x ∈
      MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y) := by
    change ((ordinaryMap.app WalkingParallelPair.one x : wppOpCodomain Y) :
        wppOpCodomain Y ⧸ MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y)) =
      ((y : wppOpCodomain Y) :
        wppOpCodomain Y ⧸ MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y)) at hqyz
    exact QuotientAddGroup.eq_iff_sub_mem.mp hqyz.symm
  rcases htarget (y - ordinaryMap.app WalkingParallelPair.one x) hrel_target with ⟨d, hd_image⟩
  have hd_target : ordinaryMap.app WalkingParallelPair.one d ∈
      MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y) := by
    rw [hd_image]
    exact hrel_target
  have hd_source : d ∈ MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X) := by
    have hd_comap :
        d ∈ AddSubgroup.comap (ordinaryMap.app WalkingParallelPair.one).hom.toAddMonoidHom
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y)) :=
      hd_target
    simpa [relationPreimagePullbackConditionW417] using (hpullback ▸ hd_comap)
  refine ⟨x + d, ?_, ?_⟩
  · change MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) (x + d) ∈ C
    rw [quotientMap_add_relation_eqW417
      (f := wppOpLeft X) (g := wppOpRight X) (x := x) (d := d) hd_source]
    exact hxC
  · calc
      ordinaryMap.app WalkingParallelPair.one (x + d) =
          ordinaryMap.app WalkingParallelPair.one x + ordinaryMap.app WalkingParallelPair.one d := by
        exact map_add (ordinaryMap.app WalkingParallelPair.one).hom.toAddMonoidHom x d
      _ = ordinaryMap.app WalkingParallelPair.one x + (y - ordinaryMap.app WalkingParallelPair.one x) := by
        rw [hd_image]
      _ = y := by abel

/--
For every closed source quotient set, relation fields make the mapped
representative image saturated for the target quotient.
-/
abbrev ordinaryDescendedRepresentativeImageSaturatedConditionW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ C : Set (wppOpOrdinaryQuotientPoint X), IsClosed C →
    IsSaturatedForW417
      (MetrizableLCA.quotientMap (wppOpCodomain Y)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
        (AddSubgroup.isClosed_topologicalClosure _) :
        wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y)
      (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
        ((MetrizableLCA.quotientMap (wppOpCodomain X)
            (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
            (AddSubgroup.isClosed_topologicalClosure _) :
            wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C))

/-- W414-shaped result: relation-pullback plus target-lift fields prove saturation. -/
theorem ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hpullback : relationPreimagePullbackConditionW417 ordinaryMap)
    (htarget : targetRelationLiftsThroughComponentW417 ordinaryMap) :
    ordinaryDescendedRepresentativeImageSaturatedConditionW417 ordinaryMap := by
  intro C _hC
  exact representativeImageSaturated_of_relationPullback_targetLiftsW417
    ordinaryMap hpullback htarget C

/-- W408/W411 representative-image closedness condition. -/
abbrev ordinaryDescendedRepresentativeImageClosedConditionW417
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

/-- W411-shaped result: component closed-map plus target saturation proves closed representative images. -/
theorem ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (hcomponent :
      IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
        wppOpCodomain X → wppOpCodomain Y))
    (hsaturated :
      ordinaryDescendedRepresentativeImageSaturatedConditionW417 ordinaryMap) :
    ordinaryDescendedRepresentativeImageClosedConditionW417 ordinaryMap := by
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
  have hrep_saturated : IsSaturatedForW417 qtarget representativeImage := by
    exact hsaturated C hC
  exact quotientMap_image_closed_of_closed_saturatedW417
    (wppOpCodomain Y)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
    (AddSubgroup.isClosed_topologicalClosure _)
    hrep_closed hrep_saturated

/-- W417 composition: relation fields prove the W408 representative-image closedness condition. -/
theorem ordinaryDescendedRepresentativeImageClosed_of_relationFieldsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : ClosedMapRelationFieldsW417 ordinaryMap) :
    ordinaryDescendedRepresentativeImageClosedConditionW417 ordinaryMap :=
  ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW417
    ordinaryMap h.component_closedMap
    (ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW417
      ordinaryMap h.relation_pullback h.target_relation_lifts)

/-- Naturality square for the ordinary left leg. -/
theorem ordinarySquareLeftW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpLeft X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simpa [wppOpLeft] using ordinaryMap.naturality WalkingParallelPairHom.left

/-- Naturality square for the ordinary right leg. -/
theorem ordinarySquareRightW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpRight X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simpa [wppOpRight] using ordinaryMap.naturality WalkingParallelPairHom.right

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem relationPreimageForwardOfSquaresW417
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    ∀ b : B, b ∈ MetrizableLCA.cokernelSubgroup (f - g) →
      iB b ∈ MetrizableLCA.cokernelSubgroup (f' - g') := by
  intro b hb
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom (MetrizableLCA.cokernelSubgroup (f' - g'))
  have hrange_le :
      AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤
        targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ MetrizableLCA.cokernelSubgroup (f' - g')
    have hleft : iB (f a) = f' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_left
    have hright : iB (g a) = g' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_right
    have hval : iB ((f - g) a) = (f' - g') (iA a) := by
      calc
        iB ((f - g) a) = iB (f a - g a) := by rfl
        _ = iB (f a) - iB (g a) := by
          exact map_sub iB.hom.toAddMonoidHom (f a) (g a)
        _ = f' (iA a) - g' (iA a) := by rw [hleft, hright]
        _ = (f' - g') (iA a) := by rfl
    rw [hval]
    exact MetrizableLCA.map_mem_cokernelSubgroup (f' - g') (iA a)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed
      ((fun b : B => iB b) ⁻¹' (MetrizableLCA.cokernelSubgroup (f' - g') : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  have hclosure_le : MetrizableLCA.cokernelSubgroup (f - g) ≤ targetPreimage :=
    AddSubgroup.topologicalClosure_minimal
      (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A))
      hrange_le htargetPreimage_closed
  exact hclosure_le hb

/-- Kernel condition needed to descend the ordinary component map through quotient objects. -/
theorem ordinaryDescendedTargetKernel_leW417
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    MetrizableLCA.cokernelSubgroup (f - g) ≤
      (iB ≫ MetrizableLCA.quotientMap B'
        (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ MetrizableLCA.cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact relationPreimageForwardOfSquaresW417 iA iB hsquare_left hsquare_right b hb

/-- The ordinary descended quotient map induced by the ordinary component map. -/
def ordinaryDescendedOfOrdinaryMapW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y :=
  MetrizableLCA.quotientLift (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)
    (ordinaryMap.app WalkingParallelPair.one ≫
      MetrizableLCA.quotientMap (wppOpCodomain Y)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
        (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW417
      (ordinaryMap.app WalkingParallelPair.zero)
      (ordinaryMap.app WalkingParallelPair.one)
      (ordinarySquareLeftW417 ordinaryMap)
      (ordinarySquareRightW417 ordinaryMap))

/-- W405-style quotient compatibility for the W417 local descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_quotient_compatW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedOfOrdinaryMapW417 ordinaryMap =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) := by
  change
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        MetrizableLCA.quotientLift (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _)
          (ordinaryMap.app WalkingParallelPair.one ≫
            MetrizableLCA.quotientMap (wppOpCodomain Y)
              (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
              (AddSubgroup.isClosed_topologicalClosure _))
          (ordinaryDescendedTargetKernel_leW417
            (ordinaryMap.app WalkingParallelPair.zero)
            (ordinaryMap.app WalkingParallelPair.one)
            (ordinarySquareLeftW417 ordinaryMap)
            (ordinarySquareRightW417 ordinaryMap)) =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  exact MetrizableLCA.quotientLift_quotientMap (wppOpCodomain X)
      (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
      (AddSubgroup.isClosed_topologicalClosure _)
      (ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _))
      (ordinaryDescendedTargetKernel_leW417
        (ordinaryMap.app WalkingParallelPair.zero)
        (ordinaryMap.app WalkingParallelPair.one)
        (ordinarySquareLeftW417 ordinaryMap)
        (ordinarySquareRightW417 ordinaryMap))

/-- The representative-image certificate proves `IsClosedMap` for the ordinary descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (hclosed : ordinaryDescendedRepresentativeImageClosedConditionW417 ordinaryMap) :
    IsClosedMap (ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) := by
  intro C hC
  have himage_eq :
      ((ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
          wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) '' C) =
        ((MetrizableLCA.quotientMap (wppOpCodomain Y)
            (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
            (AddSubgroup.isClosed_topologicalClosure _) :
            wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y) ''
          (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
            ((MetrizableLCA.quotientMap (wppOpCodomain X)
                (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
                (AddSubgroup.isClosed_topologicalClosure _) :
                wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C))) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hxC, rfl⟩
      rcases MetrizableLCA.quotientMap_surjective (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) x with ⟨b, rfl⟩
      refine ⟨ordinaryMap.app WalkingParallelPair.one b, ?_, ?_⟩
      · exact ⟨b, hxC, rfl⟩
      · exact (congrArg
          (fun q : wppOpCodomain X ⟶ wppOpOrdinaryQuotientPoint Y => q b)
          (ordinaryDescendedOfOrdinaryMap_quotient_compatW417 ordinaryMap)).symm
    · intro hy
      rcases hy with ⟨b', hb', rfl⟩
      rcases hb' with ⟨b, hbC, rfl⟩
      refine ⟨MetrizableLCA.quotientMap (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) b, hbC, ?_⟩
      exact congrArg
        (fun q : wppOpCodomain X ⟶ wppOpOrdinaryQuotientPoint Y => q b)
        (ordinaryDescendedOfOrdinaryMap_quotient_compatW417 ordinaryMap)
  rw [himage_eq]
  exact hclosed C hC

/-- W408-shaped closed-map certificate for the W417 descended quotient map. -/
structure OrdinaryDescendedClosedMapCertificateW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  closed_image_preimage :
    ordinaryDescendedRepresentativeImageClosedConditionW417 ordinaryMap

/-- Relation fields build the W408-shaped representative-image closed-map certificate. -/
theorem OrdinaryDescendedClosedMapCertificateW417.of_relationFields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : ClosedMapRelationFieldsW417 ordinaryMap) :
    OrdinaryDescendedClosedMapCertificateW417 ordinaryMap where
  closed_image_preimage :=
    ordinaryDescendedRepresentativeImageClosed_of_relationFieldsW417 h

/-- Extract the closed-map field from the W417 certificate. -/
theorem OrdinaryDescendedClosedMapCertificateW417.closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : OrdinaryDescendedClosedMapCertificateW417 ordinaryMap) :
    IsClosedMap (ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) :=
  ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW417
    h.closed_image_preimage

/-- Primary W417 result: relation fields imply `IsClosedMap ordinaryDescended`. -/
theorem ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : ClosedMapRelationFieldsW417 ordinaryMap) :
    IsClosedMap (ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) :=
  (OrdinaryDescendedClosedMapCertificateW417.of_relationFields h).closedMap

/-- W402-shaped ordinary concrete input package, specialized to the W417 map. -/
structure OrdinaryDescendedConcreteInputsW417
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop where
  relation_pullback : relationPreimagePullbackConditionW417 ordinaryMap
  quotient_compat :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)

/-- Feed the relation-field closed-map composer into a W408-style consumer package. -/
def ordinaryConcreteInputsW417_of_relationFields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : ClosedMapRelationFieldsW417 ordinaryMap) :
    OrdinaryDescendedConcreteInputsW417 ordinaryMap
      (ordinaryDescendedOfOrdinaryMapW417 ordinaryMap) where
  relation_pullback := h.relation_pullback
  quotient_compat := ordinaryDescendedOfOrdinaryMap_quotient_compatW417 ordinaryMap
  descended_closedMap := ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417 h

/-- Remaining inputs after W417 closes the ordinary descended closed-map field. -/
def remainingClosedMapFromRelationFieldsInputsW417 : List String :=
  ["none for the W408-shaped closed-map field after component_closedMap, relation_pullback, and target_relation_lifts are supplied",
    "external callers still need to provide those three relation fields"]

theorem remainingClosedMapFromRelationFieldsInputsW417_count :
    remainingClosedMapFromRelationFieldsInputsW417.length = 2 := rfl

/-- Declaration names exported by this W417 support layer. -/
def w417SupportDeclarationNames : List String :=
  ["ClosedMapRelationFieldsW417",
    "ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW417",
    "ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW417",
    "ordinaryDescendedRepresentativeImageClosed_of_relationFieldsW417",
    "ordinaryDescendedOfOrdinaryMapW417",
    "ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417",
    "ordinaryConcreteInputsW417_of_relationFields",
    "remainingClosedMapFromRelationFieldsInputsW417"]

theorem w417SupportDeclarationNames_count :
    w417SupportDeclarationNames.length = 8 := rfl

/-- Worker-state summary for parent audit tooling. -/
structure WppOpLeftLcaClosedMapFromRelationFieldsV370StateW417 : Type where
  declarations : List String
  remainingInputs : List String
  closedMapFromRelationFieldsResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

/-- Current state: the local W417 closed-map composer is checked, with no product claim. -/
def currentWppOpLeftLcaClosedMapFromRelationFieldsV370StateW417 :
    WppOpLeftLcaClosedMapFromRelationFieldsV370StateW417 where
  declarations := w417SupportDeclarationNames
  remainingInputs := remainingClosedMapFromRelationFieldsInputsW417
  closedMapFromRelationFieldsResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaClosedMapFromRelationFieldsV370StateW417_productSuccess :
    currentWppOpLeftLcaClosedMapFromRelationFieldsV370StateW417.productSuccessClaimed = false := rfl

#check ClosedMapRelationFieldsW417
#check ordinaryDescendedRepresentativeImageSaturated_of_relationPullback_targetLiftsW417
#check ordinaryDescendedRepresentativeImageClosed_of_componentClosed_targetSaturatedW417
#check ordinaryDescendedRepresentativeImageClosed_of_relationFieldsW417
#check OrdinaryDescendedClosedMapCertificateW417.of_relationFields
#check OrdinaryDescendedClosedMapCertificateW417.closedMap
#check ordinaryDescendedOfOrdinaryMapW417
#check ordinaryDescendedOfOrdinaryMap_quotient_compatW417
#check ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417
#check ordinaryConcreteInputsW417_of_relationFields
#check currentWppOpLeftLcaClosedMapFromRelationFieldsV370StateW417
#check currentWppOpLeftLcaClosedMapFromRelationFieldsV370StateW417_productSuccess

end WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417

end LeanLCAExactChallenge
