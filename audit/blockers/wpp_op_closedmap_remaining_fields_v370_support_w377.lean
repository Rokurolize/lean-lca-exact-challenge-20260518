import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W377: WPP-op closed-map remaining-fields support.

This standalone audit file connects the W374 remaining-input package to the
W371 concrete descended-quotient closed-map consumer.  The new adapter removes
the target quotient closed-on-saturated field from callers by supplying it from
the checked quotient-map theorem, leaving only the component closed-map,
relation-pullback, and target-relation-lifting fields.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpClosedMapRemainingFieldsV370SupportW377

open LeanLCAExactChallenge.MetrizableLCA

universe u

namespace ConcreteMetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW377 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- W377-local spelling of the relation-pullback equality used by W352/W368/W371. -/
abbrev relationPreimagePullbackConditionW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- Concrete target relation lifting through the component map. -/
abbrev targetRelationLiftsThroughComponentW377
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- Target quotient closed-on-saturated package used by W374 and W371. -/
structure TargetQuotientClosedOnSaturatedSetsW377
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW377 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/-- For any quotient map, closed saturated sets have closed images. -/
theorem image_closed_of_isQuotientMap_and_saturatedW377
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsQuotientMap q) {S : Set α}
    (hS : IsClosed S) (hsaturated : IsSaturatedForW377 q S) :
    IsClosed (q '' S) := by
  have hpre_eq : q ⁻¹' (q '' S) = S := by
    apply le_antisymm hsaturated
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hpre_closed : IsClosed (q ⁻¹' (q '' S)) := by
    simpa [hpre_eq] using hS
  exact hq.1.isClosed_preimage.mp hpre_closed

/-- The local quotient map is a topological quotient map. -/
theorem quotientMap_isQuotientMapW377
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X)) :
    IsQuotientMap (quotientMap X N hN : X → quotientObj X N hN) := by
  change IsQuotientMap (QuotientAddGroup.mk' N : X → X ⧸ N)
  exact QuotientAddGroup.isQuotientMap_mk N

/-- The target quotient projection closes closed saturated sets. -/
theorem quotientMap_image_closed_of_closed_saturatedW377
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X} (hS : IsClosed S)
    (hsaturated :
      IsSaturatedForW377
        (quotientMap X N hN : X → quotientObj X N hN) S) :
    IsClosed ((quotientMap X N hN : X → quotientObj X N hN) '' S) := by
  exact image_closed_of_isQuotientMap_and_saturatedW377
    (quotientMap_isQuotientMapW377 X N hN) hS hsaturated

/-- The checked quotient theorem supplies the target package. -/
theorem targetQuotientClosedOnSaturatedSetsW377
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    TargetQuotientClosedOnSaturatedSetsW377 B' N' hN' where
  closed_image := by
    intro S hS hsaturated
    exact quotientMap_image_closed_of_closed_saturatedW377 B' N' hN' hS hsaturated

/-- Stability under translations by a subgroup. -/
def IsStableUnderSubgroupTranslationsW377 {X : Type _} [AddGroup X]
    (N : AddSubgroup X) (S : Set X) : Prop :=
  ∀ x : X, x ∈ S → ∀ n : X, n ∈ N → x + n ∈ S

/-- Representative-image saturation for the target quotient. -/
abbrev targetRepresentativeImageSaturatedW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _)),
    IsClosed C →
      IsSaturatedForW377
        (quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _) :
            B' →
              quotientObj B' (cokernelSubgroup (f' - g'))
                (AddSubgroup.isClosed_topologicalClosure _))
        ((iB : B → B') ''
          ((quotientMap B (cokernelSubgroup (f - g))
              (AddSubgroup.isClosed_topologicalClosure _) :
                B →
                  quotientObj B (cokernelSubgroup (f - g))
                    (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C))

/-- Translation stability gives saturation for additive quotient maps. -/
theorem quotientMap_saturated_of_subgroup_translation_stableW377
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X}
    (hstable : IsStableUnderSubgroupTranslationsW377 N S) :
    IsSaturatedForW377
      (quotientMap X N hN : X → quotientObj X N hN) S := by
  intro y hy
  rcases hy with ⟨x, hxS, hq⟩
  have hdiff : y - x ∈ N := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp (by
      simpa [quotientMap_apply] using hq.symm)
  have hy_eq : y = x + (y - x) := by abel
  rw [hy_eq]
  exact hstable x hxS (y - x) hdiff

/-- Relation pullback plus target relation lifting gives representative-image translation stability. -/
theorem representativeImage_translation_stable_of_relation_lifts_and_pullbackW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW377 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW377 f' g' iB)
    (C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _))) :
    IsStableUnderSubgroupTranslationsW377
      (cokernelSubgroup (f' - g'))
      ((iB : B → B') ''
        ((quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B →
                quotientObj B (cokernelSubgroup (f - g))
                  (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C)) := by
  intro y hy n hn
  rcases hy with ⟨b, hbC, rfl⟩
  rcases hlift n hn with ⟨d, hd⟩
  refine ⟨b + d, ?_, ?_⟩
  · have hd_source : d ∈ cokernelSubgroup (f - g) := by
      have hd_comap :
          d ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := by
        simpa [hd] using hn
      simpa [relationPreimagePullbackConditionW377] using (hpullback ▸ hd_comap)
    have hq_eq :
        (quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B →
                quotientObj B (cokernelSubgroup (f - g))
                  (AddSubgroup.isClosed_topologicalClosure _)) (b + d) =
          (quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B →
                quotientObj B (cokernelSubgroup (f - g))
                  (AddSubgroup.isClosed_topologicalClosure _)) b := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa [quotientMap_apply] using hd_source
    simpa [hq_eq] using hbC
  · calc
      iB (b + d) = iB b + iB d := by
        exact map_add iB.hom.toAddMonoidHom b d
      _ = iB b + n := by rw [hd]

/-- Relation pullback plus target relation lifting proves representative-image saturation. -/
theorem targetRepresentativeImageSaturatedW377_of_relation_lifts_and_pullback
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW377 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW377 f' g' iB) :
    targetRepresentativeImageSaturatedW377 f g f' g' iB := by
  intro C _hC
  exact quotientMap_saturated_of_subgroup_translation_stableW377
    B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _)
    (representativeImage_translation_stable_of_relation_lifts_and_pullbackW377
      iB hpullback hlift C)

/-- W371-style representative-image closedness condition. -/
abbrev descendedQuotientRepresentativeImageClosedConditionW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B')
    (_descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop :=
  ∀ C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _)),
    IsClosed C →
      IsClosed
        ((quotientMap B' (cokernelSubgroup (f' - g'))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B' →
                quotientObj B' (cokernelSubgroup (f' - g'))
                  (AddSubgroup.isClosed_topologicalClosure _)) ''
          ((iB : B → B') ''
            ((quotientMap B (cokernelSubgroup (f - g))
                (AddSubgroup.isClosed_topologicalClosure _) :
                  B →
                    quotientObj B (cokernelSubgroup (f - g))
                      (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C)))

/-- Component closedness plus target closed-on-saturated support proves the representative-image condition. -/
theorem representativeImageClosed_of_componentClosed_targetLift_targetClosedW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (htarget_closed :
      TargetQuotientClosedOnSaturatedSetsW377 B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))
    (htarget_lift : targetRepresentativeImageSaturatedW377 f g f' g' iB) :
    descendedQuotientRepresentativeImageClosedConditionW377
      f g f' g' iB descended := by
  intro C hC
  let qsource :
      B → quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) :=
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
  let qtarget :
      B' → quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
    quotientMap B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _)
  let representativeImage : Set B' := (iB : B → B') '' (qsource ⁻¹' C)
  have hpre_closed : IsClosed (qsource ⁻¹' C) :=
    hC.preimage
      (quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.continuous
  have hrep_closed : IsClosed representativeImage :=
    hiB_closedMap (qsource ⁻¹' C) hpre_closed
  have hrep_saturated : IsSaturatedForW377 qtarget representativeImage := by
    exact htarget_lift C hC
  exact htarget_closed.closed_image representativeImage hrep_closed hrep_saturated

/-- W355-style representative-image criterion gives closedness of the descended quotient map. -/
theorem descendedQuotient_closedMap_of_representativeImageClosedW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hcompat :
      quotientMap B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
        iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))
    (hclosed :
      descendedQuotientRepresentativeImageClosedConditionW377
        f g f' g' iB descended) :
    IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) := by
  intro C hC
  have himage_eq :
      (descended '' C) =
        ((quotientMap B' (cokernelSubgroup (f' - g'))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B' →
                quotientObj B' (cokernelSubgroup (f' - g'))
                  (AddSubgroup.isClosed_topologicalClosure _)) ''
          ((iB : B → B') ''
            ((quotientMap B (cokernelSubgroup (f - g))
                (AddSubgroup.isClosed_topologicalClosure _) :
                  B →
                    quotientObj B (cokernelSubgroup (f - g))
                      (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C))) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hxC, rfl⟩
      rcases quotientMap_surjective B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) x with ⟨b, rfl⟩
      refine ⟨iB b, ?_, ?_⟩
      · exact ⟨b, hxC, rfl⟩
      · exact (congrArg
          (fun q :
            B ⟶ quotientObj B' (cokernelSubgroup (f' - g'))
              (AddSubgroup.isClosed_topologicalClosure _) => q b)
          hcompat).symm
    · intro hy
      rcases hy with ⟨b', hb', rfl⟩
      rcases hb' with ⟨b, hbC, rfl⟩
      refine ⟨quotientMap B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) b, hbC, ?_⟩
      exact congrArg
          (fun q :
            B ⟶ quotientObj B' (cokernelSubgroup (f' - g'))
              (AddSubgroup.isClosed_topologicalClosure _) => q b)
          hcompat
  rw [himage_eq]
  exact hclosed C hC

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem concreteQuotient_relationForwardW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
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

/-- Kernel condition needed to descend the component map through quotient objects. -/
theorem concreteQuotient_targetKernel_leW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    cokernelSubgroup (f - g) ≤
      (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact concreteQuotient_relationForwardW377 iA iB hsquare_left hsquare_right b hb

/-- The concrete descended quotient map induced by compatible component squares. -/
def concreteDescendedQuotientMapW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientObj B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (concreteQuotient_targetKernel_leW377 iA iB hsquare_left hsquare_right)

/-- The descended quotient map is compatible with the concrete quotient projections. -/
theorem concreteDescendedQuotientMap_quotient_compatW377
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ≫
        concreteDescendedQuotientMapW377 iA iB hsquare_left hsquare_right =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift_quotientMap B (cokernelSubgroup (f - g))
    (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (concreteQuotient_targetKernel_leW377 iA iB hsquare_left hsquare_right)

/-- W371 concrete input package. -/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW377 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW377 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW377 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- W374 remaining-input package before inserting square equations. -/
structure ConcreteQuotientClosedMapRemainingInputsW374
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW377 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW377 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW377 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- Reduced remaining fields: the target quotient closed-on-saturated field is supplied by W377. -/
structure ConcreteQuotientClosedMapRelationFieldsW377
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW377 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW377 f' g' iB

/-- Adapter from the reduced relation/component fields to W374's remaining-input package. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    ConcreteQuotientClosedMapRemainingInputsW374 f g f' g' iA iB where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts
  target_closed_on_saturated :=
    targetQuotientClosedOnSaturatedSetsW377 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- W374 consumer: remaining inputs plus square equations build W371 inputs. -/
theorem ConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRemainingInputsW374 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB hsquare_left hsquare_right where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts
  target_closed_on_saturated := h.target_closed_on_saturated

/-- Reduced fields directly build W371 inputs by way of the W374 remaining-input adapter. -/
theorem ConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRelationFieldsW377 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB hsquare_left hsquare_right :=
  ConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374 h.to_remaining_inputsW374

/-- W371 consumer: concrete inputs prove the descended quotient map is closed. -/
theorem ConcreteQuotientClosedMapInputsW371.descended_closedMap
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB
      hsquare_left hsquare_right) :
    IsClosedMap
      (concreteDescendedQuotientMapW377 iA iB hsquare_left hsquare_right :
        quotientObj B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) →
          quotientObj B' (cokernelSubgroup (f' - g'))
            (AddSubgroup.isClosed_topologicalClosure _)) := by
  have hsaturated :
      targetRepresentativeImageSaturatedW377 f g f' g' iB :=
    targetRepresentativeImageSaturatedW377_of_relation_lifts_and_pullback
      iB h.relation_pullback h.target_relation_lifts
  have hrep :
      descendedQuotientRepresentativeImageClosedConditionW377 f g f' g' iB
        (concreteDescendedQuotientMapW377 iA iB hsquare_left hsquare_right) :=
    representativeImageClosed_of_componentClosed_targetLift_targetClosedW377
      iB h.component_closedMap h.target_closed_on_saturated hsaturated
  exact descendedQuotient_closedMap_of_representativeImageClosedW377
    iB (concreteDescendedQuotientMap_quotient_compatW377
      iA iB hsquare_left hsquare_right) hrep

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

/-- Concrete WPP-op component at the ordinary source object. -/
abbrev wppOpOrdinaryDomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpDomain X ⟶ wppOpDomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero)

/-- Concrete WPP-op component at the ordinary target object. -/
abbrev wppOpOrdinaryCodomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpCodomain X ⟶ wppOpCodomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)

/-- W374's named left square equation, from naturality. -/
theorem wppOpLeftSquareEquationW377
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- W374's named right square equation, from naturality. -/
theorem wppOpRightSquareEquationW377
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- WPP-op specialization of the W374 remaining-input package. -/
abbrev WppOpConcreteQuotientClosedMapRemainingInputsW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op specialization of the reduced W377 relation/component fields. -/
abbrev WppOpConcreteQuotientClosedMapRelationFieldsW377
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/-- WPP-op specialization of W371's concrete input package. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hsquare_left :
      wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpLeft Y)
    (hsquare_right :
      wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpRight Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    hsquare_left hsquare_right

/-- Adapter from reduced W377 relation/component fields to W374 remaining inputs. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    WppOpConcreteQuotientClosedMapRemainingInputsW374 α :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374 h

/-- W374 consumer theorem: remaining fields plus naturality squares build W371 inputs. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRemainingInputsW374 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α
      (wppOpLeftSquareEquationW377 α)
      (wppOpRightSquareEquationW377 α) :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374 h

/-- Reduced W377 fields directly build the W371 input package through W374's remaining-input adapter. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α
      (wppOpLeftSquareEquationW377 α)
      (wppOpRightSquareEquationW377 α) :=
  WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374 h.to_remaining_inputsW374

/-- W371 WPP-op consumer theorem for the concrete quotient/coequalizer descended map. -/
theorem WppOpConcreteQuotientClosedMapInputsW371.descended_closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {hsquare_left :
      wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpLeft Y}
    {hsquare_right :
      wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpRight Y}
    (h :
      WppOpConcreteQuotientClosedMapInputsW371 α
        hsquare_left hsquare_right) :
    IsClosedMap
      (ConcreteMetrizableLCA.concreteDescendedQuotientMapW377
        (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
        hsquare_left hsquare_right :
        quotientObj (wppOpCodomain X)
            (cokernelSubgroup (wppOpLeft X - wppOpRight X))
            (AddSubgroup.isClosed_topologicalClosure _) →
          quotientObj (wppOpCodomain Y)
            (cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
            (AddSubgroup.isClosed_topologicalClosure _)) :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.descended_closedMap h

/-- Final W377 consumer: reduced relation/component fields imply closedness of the WPP-op descended map. -/
theorem WppOpConcreteQuotientClosedMapRelationFieldsW377.descended_closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRelationFieldsW377 α) :
    IsClosedMap
      (ConcreteMetrizableLCA.concreteDescendedQuotientMapW377
        (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
        (wppOpLeftSquareEquationW377 α) (wppOpRightSquareEquationW377 α) :
        quotientObj (wppOpCodomain X)
            (cokernelSubgroup (wppOpLeft X - wppOpRight X))
            (AddSubgroup.isClosed_topologicalClosure _) →
          quotientObj (wppOpCodomain Y)
            (cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
            (AddSubgroup.isClosed_topologicalClosure _)) :=
  WppOpConcreteQuotientClosedMapInputsW371.descended_closedMap h.to_w371_inputs

/-- Machine-readable W377 state. -/
structure WppOpClosedMapRemainingFieldsV370SupportStateW377 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpClosedMapRemainingFieldsV370SupportStateW377 :
    WppOpClosedMapRemainingFieldsV370SupportStateW377 where
  seed := "seed-afcea42ae5ce721a"
  checkedFacts :=
    ["ConcreteMetrizableLCA.targetQuotientClosedOnSaturatedSetsW377",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs",
      "ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.descended_closedMap",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374",
      "WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs",
      "WppOpConcreteQuotientClosedMapInputsW371.descended_closedMap",
      "WppOpConcreteQuotientClosedMapRelationFieldsW377.descended_closedMap"]
  remainingInputs :=
    ["component closed map for the ordinary codomain component",
      "relation-pullback equality",
      "target relation lifting through the ordinary codomain component"]
  productSuccessClaimed := false

theorem currentWppOpClosedMapRemainingFieldsV370SupportStateW377_productSuccess :
    currentWppOpClosedMapRemainingFieldsV370SupportStateW377.productSuccessClaimed = false := rfl

section Checks

#check WppOpClosedMapRemainingFieldsV370SupportW377.ConcreteMetrizableLCA.targetQuotientClosedOnSaturatedSetsW377
#check WppOpClosedMapRemainingFieldsV370SupportW377.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374
#check WppOpClosedMapRemainingFieldsV370SupportW377.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
#check WppOpClosedMapRemainingFieldsV370SupportW377.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs
#check WppOpClosedMapRemainingFieldsV370SupportW377.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371.descended_closedMap
#check WppOpClosedMapRemainingFieldsV370SupportW377.WppOpConcreteQuotientClosedMapRelationFieldsW377.to_remaining_inputsW374
#check WppOpClosedMapRemainingFieldsV370SupportW377.WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
#check WppOpClosedMapRemainingFieldsV370SupportW377.WppOpConcreteQuotientClosedMapRelationFieldsW377.to_w371_inputs
#check WppOpClosedMapRemainingFieldsV370SupportW377.WppOpConcreteQuotientClosedMapInputsW371.descended_closedMap
#check WppOpClosedMapRemainingFieldsV370SupportW377.WppOpConcreteQuotientClosedMapRelationFieldsW377.descended_closedMap
#check WppOpClosedMapRemainingFieldsV370SupportW377.currentWppOpClosedMapRemainingFieldsV370SupportStateW377_productSuccess

end Checks

end WppOpClosedMapRemainingFieldsV370SupportW377

end LeanLCAExactChallenge
