import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W420: closed-map composer from certificate packages.

This standalone audit file carries the W417 closed-map consumer layer and adds
a W401/W395-shaped certificate adapter.  The final relation-field package
contains the three concrete fields needed for the ordinary descended map:

* the ordinary codomain component is a closed map;
* the target relation pulls back to the source relation;
* every target relation element lifts through the ordinary codomain component.

The file repeats the minimal W408/W411/W414/W417 definitions locally because
`audit/blockers` files are checked as standalone Lean scripts and are not Lean
import modules. Porting note: in an integrated module layout, replace the local
W417 block below with imports of the W417 support layer and keep the W420
adapter declarations at the end of this file.
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

namespace WppOpLeftLcaClosedMapFromCertificatesV370SupportW420

/-- W401/W380-style component closed-map certificate for the ordinary codomain map. -/
structure ComponentClosedMapCertificateW380
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y) : Prop where
  component_closedMap :
    IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
      WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain X → WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain Y)

/-- Closed embeddings still supply the W380 component closed-map certificate. -/
theorem ComponentClosedMapCertificateW380.of_closedEmbedding
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (hclosed :
      IsClosedEmbedding ((ordinaryMap.app WalkingParallelPair.one) :
        WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain X → WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain Y)) :
    ComponentClosedMapCertificateW380 ordinaryMap where
  component_closedMap := hclosed.isClosedMap

/-- W401/W389-style relation-pullback equality certificate. -/
structure RelationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y) : Prop where
  relation_pullback : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.relationPreimagePullbackConditionW417 ordinaryMap

/-- W401/W392/W386-style target-relation lift certificate. -/
structure TargetRelationLiftCertificateW386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y) : Prop where
  target_relation_lifts : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.targetRelationLiftsThroughComponentW417 ordinaryMap

/-- W395-shaped certificate package specialized to W417's ordinary-map input. -/
structure CertificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y) : Prop where
  component_closedMap :
    IsClosedMap ((ordinaryMap.app WalkingParallelPair.one) :
      WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain X → WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpCodomain Y)
  relation_pullback : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.relationPreimagePullbackConditionW417 ordinaryMap
  target_relation_lifts : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.targetRelationLiftsThroughComponentW417 ordinaryMap

/-- Compose the W380, W389, and W386 certificate shapes into W395 relation fields. -/
theorem certificateRelationFieldsW395_of_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (hclosed : ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback : RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget : TargetRelationLiftCertificateW386 ordinaryMap) :
    CertificateRelationFieldsW395 ordinaryMap where
  component_closedMap := hclosed.component_closedMap
  relation_pullback := hpullback.relation_pullback
  target_relation_lifts := htarget.target_relation_lifts

/-- Adapter from W395 certificate fields to W417's `ClosedMapRelationFieldsW417`. -/
def closedMapRelationFieldsW417_of_certificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (h : CertificateRelationFieldsW395 ordinaryMap) :
    WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ClosedMapRelationFieldsW417 ordinaryMap where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts

/-- Direct adapter from separate W401-style certificates to W417 relation fields. -/
def closedMapRelationFieldsW417_of_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (hclosed : ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback : RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget : TargetRelationLiftCertificateW386 ordinaryMap) :
    WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ClosedMapRelationFieldsW417 ordinaryMap :=
  closedMapRelationFieldsW417_of_certificateRelationFieldsW395
    (certificateRelationFieldsW395_of_w380_w389_w386 hclosed hpullback htarget)

/-- Certificate packages feed W417's primary closed-map consumer. -/
theorem ordinaryDescendedOfOrdinaryMap_isClosedMap_of_certificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (h : CertificateRelationFieldsW395 ordinaryMap) :
    IsClosedMap (WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
      WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryQuotientPoint X → WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryQuotientPoint Y) :=
  WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417
    (closedMapRelationFieldsW417_of_certificateRelationFieldsW395 h)

/-- Certificate packages feed W417's concrete-input consumer. -/
def ordinaryConcreteInputsW417_of_certificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (h : CertificateRelationFieldsW395 ordinaryMap) :
    WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.OrdinaryDescendedConcreteInputsW417 ordinaryMap
      (WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417 ordinaryMap) :=
  WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryConcreteInputsW417_of_relationFields
    (closedMapRelationFieldsW417_of_certificateRelationFieldsW395 h)

/-- Separate W401-style certificates feed W417's primary closed-map consumer. -/
theorem ordinaryDescendedOfOrdinaryMap_isClosedMap_of_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (hclosed : ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback : RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget : TargetRelationLiftCertificateW386 ordinaryMap) :
    IsClosedMap (WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417 ordinaryMap :
      WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryQuotientPoint X → WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryQuotientPoint Y) :=
  WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMap_isClosedMap_of_relationFieldsW417
    (closedMapRelationFieldsW417_of_w380_w389_w386 hclosed hpullback htarget)

/-- Separate W401-style certificates feed W417's concrete-input consumer. -/
def ordinaryConcreteInputsW417_of_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram X ⟶ WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.wppOpOrdinaryDiagram Y}
    (hclosed : ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback : RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget : TargetRelationLiftCertificateW386 ordinaryMap) :
    WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.OrdinaryDescendedConcreteInputsW417 ordinaryMap
      (WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417 ordinaryMap) :=
  WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryConcreteInputsW417_of_relationFields
    (closedMapRelationFieldsW417_of_w380_w389_w386 hclosed hpullback htarget)

/-- Porting notes for replacing the duplicated standalone W417 block with module imports. -/
def portingNotesW420 : List String :=
  ["audit/blockers files are standalone scripts, so W417 cannot be imported as a module here",
    "when W417 is promoted to a Lean module, keep the W420 certificate adapter declarations and replace the duplicated W417 block with an import",
    "the adapter preserves exactly the three W417 fields: component_closedMap, relation_pullback, target_relation_lifts"]

/-- Declaration names exported by this W420 certificate adapter. -/
def w420SupportDeclarationNames : List String :=
  ["ComponentClosedMapCertificateW380",
    "RelationPullbackEqualityCertificateW389",
    "TargetRelationLiftCertificateW386",
    "CertificateRelationFieldsW395",
    "certificateRelationFieldsW395_of_w380_w389_w386",
    "closedMapRelationFieldsW417_of_certificateRelationFieldsW395",
    "closedMapRelationFieldsW417_of_w380_w389_w386",
    "ordinaryDescendedOfOrdinaryMap_isClosedMap_of_certificateRelationFieldsW395",
    "ordinaryConcreteInputsW417_of_certificateRelationFieldsW395",
    "ordinaryDescendedOfOrdinaryMap_isClosedMap_of_w380_w389_w386",
    "ordinaryConcreteInputsW417_of_w380_w389_w386",
    "portingNotesW420"]

/-- Remaining input summary for parent audit tooling. -/
def remainingClosedMapFromCertificatesInputsW420 : List String :=
  ["for callers: W380/component closed-map certificate or closed-embedding source",
    "for callers: W389 relation-pullback equality certificate",
    "for callers: W386/W392 target-relation lift certificate",
    "no W411/W414 proof restatement is needed by callers; W417 consumes the adapted fields"]

theorem w420SupportDeclarationNames_count :
    w420SupportDeclarationNames.length = 12 := rfl

theorem remainingClosedMapFromCertificatesInputsW420_count :
    remainingClosedMapFromCertificatesInputsW420.length = 4 := rfl

/-- Worker-state summary for parent audit tooling. -/
structure WppOpLeftLcaClosedMapFromCertificatesV370StateW420 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  closedMapFromCertificatesResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

/-- Current state: W401/W395-style certificates are adapted to the W417 consumers. -/
def currentWppOpLeftLcaClosedMapFromCertificatesV370StateW420 :
    WppOpLeftLcaClosedMapFromCertificatesV370StateW420 where
  seed := "2ec243a4e0dafe2cde032448d42bba1b"
  declarations := w420SupportDeclarationNames
  remainingInputs := remainingClosedMapFromCertificatesInputsW420
  closedMapFromCertificatesResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaClosedMapFromCertificatesV370StateW420_productSuccess :
    currentWppOpLeftLcaClosedMapFromCertificatesV370StateW420.productSuccessClaimed = false := rfl

#check ComponentClosedMapCertificateW380
#check ComponentClosedMapCertificateW380.of_closedEmbedding
#check RelationPullbackEqualityCertificateW389
#check TargetRelationLiftCertificateW386
#check CertificateRelationFieldsW395
#check certificateRelationFieldsW395_of_w380_w389_w386
#check closedMapRelationFieldsW417_of_certificateRelationFieldsW395
#check closedMapRelationFieldsW417_of_w380_w389_w386
#check ordinaryDescendedOfOrdinaryMap_isClosedMap_of_certificateRelationFieldsW395
#check ordinaryConcreteInputsW417_of_certificateRelationFieldsW395
#check ordinaryDescendedOfOrdinaryMap_isClosedMap_of_w380_w389_w386
#check ordinaryConcreteInputsW417_of_w380_w389_w386
#check currentWppOpLeftLcaClosedMapFromCertificatesV370StateW420
#check currentWppOpLeftLcaClosedMapFromCertificatesV370StateW420_productSuccess

end WppOpLeftLcaClosedMapFromCertificatesV370SupportW420

end LeanLCAExactChallenge


/-!
W423 carries W418 locally as a standalone block because audit/blockers files are
not importable Lean modules in this repository layout.
-/

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

universe u

namespace MetrizableLCA

/-- W407 closed-range membership spelling of the reverse-preimage input. -/
abbrev relationReverseClosedRangeMembershipW407
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B,
    iB b ∈
        (AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure →
      b ∈
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure

/-- W399 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W399 closed-range spelling of the same relation-pullback equality. -/
abbrev relationClosedRangePreimageEqualityW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- W399's relation-pullback and closed-range spellings are definitionally equal. -/
theorem relationPreimagePullbackConditionIffClosedRangeEqualityW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW399 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW399 f g f' g' iB := by
  rfl

/-- Under square equations, the source closed range maps into the target closed range. -/
theorem relationClosedRangeForwardOfSquaresW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
        (⊤ : AddSubgroup A)).topologicalClosure ≤
      AddSubgroup.comap iB.hom.toAddMonoidHom
        ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure) := by
  let sourceRange : AddSubgroup B :=
    AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)
  let targetClosed : AddSubgroup B' :=
    (AddSubgroup.map (f' - g').hom.toAddMonoidHom
      (⊤ : AddSubgroup A')).topologicalClosure
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom targetClosed
  have hrange_le : sourceRange ≤ targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ targetClosed
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
    exact AddSubgroup.le_topologicalClosure _
      (show (f' - g') (iA a) ∈
        AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A') from
        ⟨iA a, trivial, rfl⟩)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (targetClosed : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  exact AddSubgroup.topologicalClosure_minimal sourceRange hrange_le htargetPreimage_closed

/-- W407 reverse closed-range membership and square equations imply W399 relation pullback. -/
theorem relationPreimagePullbackCondition_of_reverseMembership_and_squares
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    relationPreimagePullbackConditionW399 f g f' g' iB := by
  apply (relationPreimagePullbackConditionIffClosedRangeEqualityW399 iB).mpr
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · exact relationClosedRangeForwardOfSquaresW418 iA iB hsquare_left hsquare_right

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem relationPreimageForwardOfSquaresW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    ∀ b : B, b ∈ cokernelSubgroup (f - g) →
      iB b ∈ cokernelSubgroup (f' - g') := by
  intro b hb
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g'))
  have hrange_le :
      AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤
        targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ cokernelSubgroup (f' - g')
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
    exact map_mem_cokernelSubgroup (f' - g') (iA a)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (cokernelSubgroup (f' - g') : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  have hclosure_le : cokernelSubgroup (f - g) ≤ targetPreimage :=
    AddSubgroup.topologicalClosure_minimal
      (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A))
      hrange_le htargetPreimage_closed
  exact hclosure_le hb

/-- Kernel condition needed to descend the ordinary component map through quotient objects. -/
theorem ordinaryDescendedTargetKernel_leW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    cokernelSubgroup (f - g) ≤
      (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact relationPreimageForwardOfSquaresW418 iA iB hsquare_left hsquare_right b hb

/-- The concrete ordinary descended quotient map induced by compatible component squares. -/
def ordinaryDescendedQuotientMapW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientObj B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW418 iA iB hsquare_left hsquare_right)

/-- The concrete ordinary descended quotient map satisfies W399's quotient-compatibility field. -/
theorem ordinaryDescendedQuotientMap_quotient_compatW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift_quotientMap B (cokernelSubgroup (f - g))
    (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW418 iA iB hsquare_left hsquare_right)

/-- W399 ordinary descended quotient topology input shape. -/
structure RelationPullbackDescendedFieldsInputsW399
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  relation_pullback : relationPreimagePullbackConditionW399 f g f' g' iB
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))

/-- W399 input constructor using the W405 descended quotient map. -/
theorem RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB)
    (hclosed : IsClosedMap
      (ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right :
        quotientObj B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) →
        quotientObj B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))) :
    RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB
      (ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right) where
  square_left := hsquare_left
  square_right := hsquare_right
  relation_pullback :=
    relationPreimagePullbackCondition_of_reverseMembership_and_squares
      iA iB hsquare_left hsquare_right hreverse
  quotient_compat :=
    ordinaryDescendedQuotientMap_quotient_compatW418
      iA iB hsquare_left hsquare_right
  descended_closedMap := hclosed

end MetrizableLCA

namespace WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418

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

/-- Ordinary quotient point used by the WPP-op adapter. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- WPP-op closed-range membership spelling of W407's reverse-preimage input. -/
abbrev WppOpRelationReverseClosedRangeMembershipW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  MetrizableLCA.relationReverseClosedRangeMembershipW407
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)

/-- Ordinary left square equation, from naturality. -/
theorem ordinarySquareLeftW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpLeft X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simpa [wppOpLeft] using ordinaryMap.naturality WalkingParallelPairHom.left

/-- Ordinary right square equation, from naturality. -/
theorem ordinarySquareRightW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpRight X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simpa [wppOpRight] using ordinaryMap.naturality WalkingParallelPairHom.right

/-- The ordinary descended quotient map induced by `ordinaryMap.app WalkingParallelPair.one`. -/
def ordinaryDescendedOfOrdinaryMapW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y :=
  MetrizableLCA.ordinaryDescendedQuotientMapW418
    (ordinaryMap.app WalkingParallelPair.zero)
    (ordinaryMap.app WalkingParallelPair.one)
    (ordinarySquareLeftW418 ordinaryMap)
    (ordinarySquareRightW418 ordinaryMap)

/-- W405 quotient compatibility for the concrete ordinary descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_quotient_compatW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedOfOrdinaryMapW418 ordinaryMap =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) := by
  simpa [ordinaryDescendedOfOrdinaryMapW418] using
    MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418
      (ordinaryMap.app WalkingParallelPair.zero)
      (ordinaryMap.app WalkingParallelPair.one)
      (ordinarySquareLeftW418 ordinaryMap)
      (ordinarySquareRightW418 ordinaryMap)

/-- WPP-op W399 ordinary input shape using the concrete descended quotient map. -/
abbrev WppOpRelationPullbackDescendedFieldsInputsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    Prop :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399
    (wppOpDomain X) (wppOpCodomain X)
    (wppOpDomain Y) (wppOpCodomain Y)
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.zero)
    (ordinaryMap.app WalkingParallelPair.one)
    (ordinaryDescendedOfOrdinaryMapW418 ordinaryMap)

/--
Checked WPP-op assembly: reverse closed-range membership fills W399's
relation-pullback field, W405's quotient-lift map fills quotient compatibility,
and the only remaining explicit input is closedness of the descended map.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (hreverse : WppOpRelationReverseClosedRangeMembershipW407 ordinaryMap)
    (hclosed : IsClosedMap (ordinaryDescendedOfOrdinaryMapW418 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)) :
    WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
    (ordinarySquareLeftW418 ordinaryMap)
    (ordinarySquareRightW418 ordinaryMap)
    hreverse hclosed

/-- Remaining input after W418 combines W407/W415 relation pullback and W405 quotient compatibility. -/
def remainingInputsAfterW418Assembly : List String :=
  ["IsClosedMap for ordinaryDescendedOfOrdinaryMapW418 ordinaryMap"]

theorem remainingInputsAfterW418Assembly_count :
    remainingInputsAfterW418Assembly.length = 1 := rfl

/-- Declaration names exported by this W418 support layer. -/
def w418SupportDeclarationNames : List String :=
  ["MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares",
    "MetrizableLCA.ordinaryDescendedQuotientMapW418",
    "MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended",
    "ordinaryDescendedOfOrdinaryMapW418",
    "ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap",
    "remainingInputsAfterW418Assembly"]

theorem w418SupportDeclarationNames_count :
    w418SupportDeclarationNames.length = 8 := rfl

/-- Machine-readable W418 state. -/
structure WppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  w399InputsAssemblyResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 :
    WppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 where
  seed := "6e5c083ed385eff326e065695060c97b"
  checkedFacts :=
    ["proved the W407 reverse-membership to W399 relation-pullback bridge with ordinary square equations",
      "defined the W405-shaped ordinary descended quotient map by quotientLift",
      "proved quotient compatibility for the concrete ordinary descended quotient map",
      "constructed the W399 relation/topology input package from reverse membership and IsClosedMap only"]
  remainingInputs := remainingInputsAfterW418Assembly
  w399InputsAssemblyResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418_productSuccess :
    currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418.productSuccessClaimed =
      false := rfl

section Checks

#check MetrizableLCA.relationReverseClosedRangeMembershipW407
#check MetrizableLCA.relationPreimagePullbackConditionW399
#check MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares
#check MetrizableLCA.ordinaryDescendedQuotientMapW418
#check MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
#check WppOpRelationReverseClosedRangeMembershipW407
#check ordinaryDescendedOfOrdinaryMapW418
#check ordinaryDescendedOfOrdinaryMap_quotient_compatW418
#check WppOpRelationPullbackDescendedFieldsInputsW399
#check relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap
#check remainingInputsAfterW418Assembly
#check remainingInputsAfterW418Assembly_count
#check w418SupportDeclarationNames
#check w418SupportDeclarationNames_count
#check currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418
#check currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418_productSuccess

end Checks

end WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423

/-- W417 and W418 use the same concrete ordinary descended quotient map. -/
theorem ordinaryDescendedOfOrdinaryMapW417_eq_W418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y) :
    WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.ordinaryDescendedOfOrdinaryMapW417 ordinaryMap =
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMapW418 ordinaryMap := rfl

/--
W423 certificate-package assembly: W407 reverse membership supplies the W399
relation field, while the W420 W395 package supplies the descended closed-map
input.  The caller does not pass a closed-map hypothesis directly.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_certificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y}
    (hreverse :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationReverseClosedRangeMembershipW407 ordinaryMap)
    (hcert : WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.CertificateRelationFieldsW395 ordinaryMap) :
    WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap
    hreverse
    (by
      simpa [ordinaryDescendedOfOrdinaryMapW417_eq_W418] using
        WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.ordinaryDescendedOfOrdinaryMap_isClosedMap_of_certificateRelationFieldsW395 hcert)

/--
W423 separate-certificate assembly: the W380, W389, and W386 certificates are
first composed by W420, then used to fill W418's only remaining closed-map input.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y}
    (hreverse :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationReverseClosedRangeMembershipW407 ordinaryMap)
    (hclosed : WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback : WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget : WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.TargetRelationLiftCertificateW386 ordinaryMap) :
    WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_certificateRelationFieldsW395
    hreverse
    (WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.certificateRelationFieldsW395_of_w380_w389_w386 hclosed hpullback htarget)

def w423SupportDeclarationNames : List String :=
  ["ordinaryDescendedOfOrdinaryMapW417_eq_W418",
    "relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_certificateRelationFieldsW395",
    "relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_w380_w389_w386"]

theorem w423SupportDeclarationNames_count :
    w423SupportDeclarationNames.length = 3 := rfl

def remainingW399CertificateCompositionInputsW423 : List String :=
  ["W407 reverse closed-range membership",
    "W420 certificate package, or W380/W389/W386 certificates",
    "promote the standalone audit blocks to importable Lean modules before integrating into the main library"]

theorem remainingW399CertificateCompositionInputsW423_count :
    remainingW399CertificateCompositionInputsW423.length = 3 := rfl

structure WppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  w399CertificateCompositionResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423 :
    WppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423 where
  seed := "S6h8LsYEdZl52Utfbz5BQzOX"
  declarations := w423SupportDeclarationNames
  remainingInputs := remainingW399CertificateCompositionInputsW423
  w399CertificateCompositionResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423_productSuccess :
    currentWppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423.productSuccessClaimed =
      false := rfl

section Checks

#check ordinaryDescendedOfOrdinaryMapW417_eq_W418
#check relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_certificateRelationFieldsW395
#check relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_w380_w389_w386
#check w423SupportDeclarationNames
#check remainingW399CertificateCompositionInputsW423
#check currentWppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423
#check currentWppOpW399InputsFromReverseMembershipAndCertificatesV370StateW423_productSuccess

end Checks

end WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423

namespace WppOpW399InputsFromCertificatesOnlyV370SupportW426

/--
W426 adapter: W420's W389 relation-pullback equality contains the reverse
closed-range membership needed by the W418/W423 W407 input.
-/
theorem relationReverseClosedRangeMembershipW407_of_relationPullbackEqualityCertificateW389
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y}
    (hpullback :
      WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.RelationPullbackEqualityCertificateW389 ordinaryMap) :
    WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationReverseClosedRangeMembershipW407 ordinaryMap := by
  intro b hb
  have hb_comap :
      b ∈ AddSubgroup.comap
        (ordinaryMap.app WalkingParallelPair.one).hom.toAddMonoidHom
        (MetrizableLCA.cokernelSubgroup
          (WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpLeft Y -
            WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpRight Y)) := hb
  simpa
    [WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationReverseClosedRangeMembershipW407,
      MetrizableLCA.relationReverseClosedRangeMembershipW407,
      WppOpLeftLcaClosedMapFromRelationFieldsV370SupportW417.relationPreimagePullbackConditionW417]
    using (hpullback.relation_pullback ▸ hb_comap)

/--
W426 certificate-only assembly: the W395 package supplies both the W389
reverse-membership adapter and W420's descended closed-map input, so callers no
longer pass W407 explicitly.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_certificateRelationFieldsW395
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y}
    (hcert :
      WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.CertificateRelationFieldsW395 ordinaryMap) :
    WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423.relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_certificateRelationFieldsW395
    (relationReverseClosedRangeMembershipW407_of_relationPullbackEqualityCertificateW389
      (WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.RelationPullbackEqualityCertificateW389.mk
        hcert.relation_pullback))
    hcert

/--
W426 separate-certificate assembly: W380/W389/W386 are first composed into the
W395 package, and W389 also supplies the W407 reverse-membership input.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_w380_w389_w386
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap :
      WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram X ⟶
        WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.wppOpOrdinaryDiagram Y}
    (hclosed :
      WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.ComponentClosedMapCertificateW380 ordinaryMap)
    (hpullback :
      WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.RelationPullbackEqualityCertificateW389 ordinaryMap)
    (htarget :
      WppOpLeftLcaClosedMapFromCertificatesV370SupportW420.TargetRelationLiftCertificateW386 ordinaryMap) :
    WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423.relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_w380_w389_w386
    (relationReverseClosedRangeMembershipW407_of_relationPullbackEqualityCertificateW389 hpullback)
    hclosed hpullback htarget

def w426SupportDeclarationNames : List String :=
  ["relationReverseClosedRangeMembershipW407_of_relationPullbackEqualityCertificateW389",
    "relationPullbackDescendedFieldsInputsW399_of_certificateRelationFieldsW395",
    "relationPullbackDescendedFieldsInputsW399_of_w380_w389_w386"]

theorem w426SupportDeclarationNames_count :
    w426SupportDeclarationNames.length = 3 := rfl

def remainingW399CertificatesOnlyInputsW426 : List String :=
  ["W420 CertificateRelationFieldsW395 package, or separate W380/W389/W386 certificates",
    "promote the standalone audit blocks to importable Lean modules before integrating into the main library"]

theorem remainingW399CertificatesOnlyInputsW426_count :
    remainingW399CertificatesOnlyInputsW426.length = 2 := rfl

structure WppOpW399InputsFromCertificatesOnlyV370StateW426 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  w399CertificatesOnlyResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpW399InputsFromCertificatesOnlyV370StateW426 :
    WppOpW399InputsFromCertificatesOnlyV370StateW426 where
  seed := "c7c128d0dad3b2555fa550c07b149847"
  declarations := w426SupportDeclarationNames
  remainingInputs := remainingW399CertificatesOnlyInputsW426
  w399CertificatesOnlyResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpW399InputsFromCertificatesOnlyV370StateW426_productSuccess :
    currentWppOpW399InputsFromCertificatesOnlyV370StateW426.productSuccessClaimed =
      false := rfl

section Checks

#check relationReverseClosedRangeMembershipW407_of_relationPullbackEqualityCertificateW389
#check relationPullbackDescendedFieldsInputsW399_of_certificateRelationFieldsW395
#check relationPullbackDescendedFieldsInputsW399_of_w380_w389_w386
#check w426SupportDeclarationNames
#check remainingW399CertificatesOnlyInputsW426
#check currentWppOpW399InputsFromCertificatesOnlyV370StateW426
#check currentWppOpW399InputsFromCertificatesOnlyV370StateW426_productSuccess

end Checks

end WppOpW399InputsFromCertificatesOnlyV370SupportW426

end LeanLCAExactChallenge
