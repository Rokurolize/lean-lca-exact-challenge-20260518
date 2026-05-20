import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W368: target representative-image saturation support.

This standalone audit file keeps the W365 closed-map composer shape and closes
its remaining target representative-image saturation input from concrete
relation data:

* the source relation subgroup is the preimage of the target relation subgroup
  along `iB`;
* every target relation element lifts through the component map `iB`.

The final consumer theorem packages those concrete fields as
`QuotientClosedMapComposerInputsW365` and feeds them to
`QuotientClosedMapComposerInputsW365.descended_closedMap`.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

universe u

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW365 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- W365-local relation-pullback equality matching the W352 boundary. -/
abbrev relationPreimagePullbackConditionW365
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- Stability under translations by a subgroup. -/
def IsStableUnderSubgroupTranslationsW368 {X : Type _} [AddGroup X]
    (N : AddSubgroup X) (S : Set X) : Prop :=
  ∀ x : X, x ∈ S → ∀ n : X, n ∈ N → x + n ∈ S

/--
Concrete W360-style relation-lifting field: target relation elements lift
through the component map.
-/
abbrev targetRelationLiftsThroughComponentW368
    {B A' B' : MetrizableLCA.{u}} (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
W365-local copy of W355's representative-image closedness condition.

For every closed source quotient set, pull it back to representatives, map by
the component `iB`, and project to the target quotient.
-/
abbrev descendedQuotientRepresentativeImageClosedConditionW365
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B')
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

/-- For any quotient map, closed saturated sets have closed images. -/
theorem image_closed_of_isQuotientMap_and_saturatedW365
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsQuotientMap q) {S : Set α}
    (hS : IsClosed S) (hsaturated : IsSaturatedForW365 q S) :
    IsClosed (q '' S) := by
  have hpre_eq : q ⁻¹' (q '' S) = S := by
    apply le_antisymm hsaturated
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hpre_closed : IsClosed (q ⁻¹' (q '' S)) := by
    simpa [hpre_eq] using hS
  exact hq.1.isClosed_preimage.mp hpre_closed

/-- The local quotient map is a topological quotient map. -/
theorem quotientMap_isQuotientMapW365
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X)) :
    IsQuotientMap (quotientMap X N hN : X → quotientObj X N hN) := by
  change IsQuotientMap (QuotientAddGroup.mk' N : X → X ⧸ N)
  exact QuotientAddGroup.isQuotientMap_mk N

/-- The target quotient projection closes closed saturated sets. -/
theorem quotientMap_image_closed_of_closed_saturatedW365
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X} (hS : IsClosed S)
    (hsaturated :
      IsSaturatedForW365
        (quotientMap X N hN : X → quotientObj X N hN) S) :
    IsClosed ((quotientMap X N hN : X → quotientObj X N hN) '' S) := by
  exact image_closed_of_isQuotientMap_and_saturatedW365
    (quotientMap_isQuotientMapW365 X N hN) hS hsaturated

/--
For an additive quotient, translation stability by the quotient subgroup is
enough to prove saturation for the quotient map.
-/
theorem quotientMap_saturated_of_subgroup_translation_stableW368
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X}
    (hstable : IsStableUnderSubgroupTranslationsW368 N S) :
    IsSaturatedForW365
      (quotientMap X N hN : X → quotientObj X N hN) S := by
  intro y hy
  rcases hy with ⟨x, hxS, hq⟩
  have hdiff : y - x ∈ N := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp (by
      simpa [quotientMap_apply] using hq.symm)
  have hy_eq : y = x + (y - x) := by abel
  rw [hy_eq]
  exact hstable x hxS (y - x) hdiff

/-- Target quotient closed-on-saturated package copied from the W363 boundary. -/
structure TargetQuotientClosedOnSaturatedSetsW365
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW365 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/-- The checked quotient theorem supplies the target package. -/
theorem targetQuotientClosedOnSaturatedSetsW365
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    TargetQuotientClosedOnSaturatedSetsW365 B' N' hN' where
  closed_image := by
    intro S hS hsaturated
    exact quotientMap_image_closed_of_closed_saturatedW365 B' N' hN' hS hsaturated

/--
Target relation lifting needed by the closed-map composer.

For every closed source quotient set, the representative image in the target is
saturated for the target quotient relation.
-/
abbrev targetRepresentativeImageSaturatedW365
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _)),
    IsClosed C →
      IsSaturatedForW365
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

/--
Target relation lifting plus the source-target relation pullback equality gives
the translate closure needed for representative-image saturation.
-/
theorem representativeImage_translation_stable_of_relation_lifts_and_pullbackW368
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW365 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW368 f' g' iB)
    (C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _))) :
    IsStableUnderSubgroupTranslationsW368
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
      simpa [relationPreimagePullbackConditionW365] using (hpullback ▸ hd_comap)
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

/--
Concrete W368 bridge: relation pullback plus target relation lifting proves the
exact W365 representative-image saturation input.
-/
theorem targetRepresentativeImageSaturatedW365_of_relation_lifts_and_pullbackW368
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW365 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW368 f' g' iB) :
    targetRepresentativeImageSaturatedW365 f g f' g' iB := by
  intro C _hC
  exact quotientMap_saturated_of_subgroup_translation_stableW368
    B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _)
    (representativeImage_translation_stable_of_relation_lifts_and_pullbackW368
      iB hpullback hlift C)

/--
Component closedness plus target closed-on-saturated support proves the W355
representative-image condition.
-/
theorem representativeImageClosed_of_componentClosed_targetLift_targetClosedW365
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (htarget_closed :
      TargetQuotientClosedOnSaturatedSetsW365 B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))
    (htarget_lift : targetRepresentativeImageSaturatedW365 f g f' g' iB) :
    descendedQuotientRepresentativeImageClosedConditionW365
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
  have hrep_saturated : IsSaturatedForW365 qtarget representativeImage := by
    exact htarget_lift C hC
  exact htarget_closed.closed_image representativeImage hrep_closed hrep_saturated

/-- W355-style representative-image criterion gives closedness of the descended quotient map. -/
theorem descendedQuotient_closedMap_of_representativeImageClosedW365
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
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
      descendedQuotientRepresentativeImageClosedConditionW365
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

/--
Composer inputs: component closed map, relation pullback, target relation
lifting, target quotient closed-on-saturated support, and quotient compatibility.
-/
structure QuotientClosedMapComposerInputsW365
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW365 f g f' g' iB
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  target_relation_lift : targetRepresentativeImageSaturatedW365 f g f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW365 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- The packaged inputs supply the W355 representative-image condition. -/
theorem QuotientClosedMapComposerInputsW365.representative_image_closed
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : QuotientClosedMapComposerInputsW365 A B A' B' f g f' g' iB descended) :
    descendedQuotientRepresentativeImageClosedConditionW365
      f g f' g' iB descended :=
  representativeImageClosed_of_componentClosed_targetLift_targetClosedW365
    iB h.component_closedMap h.target_closed_on_saturated h.target_relation_lift

/--
Main W365 composer: the checked inputs yield the W355-style `IsClosedMap` for
the descended quotient morphism.
-/
theorem QuotientClosedMapComposerInputsW365.descended_closedMap
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : QuotientClosedMapComposerInputsW365 A B A' B' f g f' g' iB descended) :
    IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  descendedQuotient_closedMap_of_representativeImageClosedW365
    iB h.quotient_compat h.representative_image_closed

/--
W368 concrete composer inputs replace W365's already-saturated target field by
the relation-pullback and target-relation lifting fields that imply it.
-/
structure TargetRepresentativeSaturationComposerInputsW368
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW365 f g f' g' iB
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  target_relation_lifts : targetRelationLiftsThroughComponentW368 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW365 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- W368 concrete inputs produce the W365 composer package. -/
theorem TargetRepresentativeSaturationComposerInputsW368.to_w365_inputs
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : TargetRepresentativeSaturationComposerInputsW368 A B A' B' f g f' g' iB descended) :
    QuotientClosedMapComposerInputsW365 A B A' B' f g f' g' iB descended where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  quotient_compat := h.quotient_compat
  target_relation_lift :=
    targetRepresentativeImageSaturatedW365_of_relation_lifts_and_pullbackW368
      iB h.relation_pullback h.target_relation_lifts
  target_closed_on_saturated := h.target_closed_on_saturated

/--
Consumer theorem requested by W368: concrete relation lifting feeds into the
W365 composer and yields closedness of the descended quotient map.
-/
theorem TargetRepresentativeSaturationComposerInputsW368.descended_closedMap
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : TargetRepresentativeSaturationComposerInputsW368 A B A' B' f g f' g' iB descended) :
    IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  QuotientClosedMapComposerInputsW365.descended_closedMap h.to_w365_inputs

/-- Machine-readable W368 state. -/
structure TargetRepresentativeSaturationV370SupportStateW368 : Type where
  seed : String
  checkedFacts : List String
  packagedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentTargetRepresentativeSaturationV370SupportStateW368 :
    TargetRepresentativeSaturationV370SupportStateW368 where
  seed := "4c6baa4b58bc45ad65a09b29e464b77b"
  checkedFacts :=
    ["MetrizableLCA.image_closed_of_isQuotientMap_and_saturatedW365",
      "MetrizableLCA.quotientMap_isQuotientMapW365",
      "MetrizableLCA.quotientMap_image_closed_of_closed_saturatedW365",
      "MetrizableLCA.targetQuotientClosedOnSaturatedSetsW365",
      "MetrizableLCA.quotientMap_saturated_of_subgroup_translation_stableW368",
      "MetrizableLCA.representativeImage_translation_stable_of_relation_lifts_and_pullbackW368",
      "MetrizableLCA.targetRepresentativeImageSaturatedW365_of_relation_lifts_and_pullbackW368",
      "MetrizableLCA.representativeImageClosed_of_componentClosed_targetLift_targetClosedW365",
      "MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW365",
      "MetrizableLCA.QuotientClosedMapComposerInputsW365.representative_image_closed",
      "MetrizableLCA.QuotientClosedMapComposerInputsW365.descended_closedMap",
      "MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.to_w365_inputs",
      "MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.descended_closedMap"]
  packagedInputs :=
    ["component closed map",
      "relation-pullback equality for the W352-facing descended quotient fields",
      "quotient compatibility for the descended quotient map",
      "target relation lifting through iB",
      "target quotient projection closed on closed saturated sets"]
  remainingInputs :=
    ["instantiate these inputs for the concrete WPP-op quotient/coequalizer descended map"]
  productSuccessClaimed := false

theorem currentTargetRepresentativeSaturationV370SupportStateW368_productSuccess :
    currentTargetRepresentativeSaturationV370SupportStateW368.productSuccessClaimed = false := rfl

def targetRepresentativeSaturationV370SupportDeclarationNamesW368 : List String :=
  ["MetrizableLCA.IsSaturatedForW365",
    "MetrizableLCA.relationPreimagePullbackConditionW365",
    "MetrizableLCA.IsStableUnderSubgroupTranslationsW368",
    "MetrizableLCA.targetRelationLiftsThroughComponentW368",
    "MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW365",
    "MetrizableLCA.image_closed_of_isQuotientMap_and_saturatedW365",
    "MetrizableLCA.quotientMap_isQuotientMapW365",
    "MetrizableLCA.quotientMap_image_closed_of_closed_saturatedW365",
    "MetrizableLCA.quotientMap_saturated_of_subgroup_translation_stableW368",
    "MetrizableLCA.TargetQuotientClosedOnSaturatedSetsW365",
    "MetrizableLCA.targetQuotientClosedOnSaturatedSetsW365",
    "MetrizableLCA.targetRepresentativeImageSaturatedW365",
    "MetrizableLCA.representativeImage_translation_stable_of_relation_lifts_and_pullbackW368",
    "MetrizableLCA.targetRepresentativeImageSaturatedW365_of_relation_lifts_and_pullbackW368",
    "MetrizableLCA.representativeImageClosed_of_componentClosed_targetLift_targetClosedW365",
    "MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW365",
    "MetrizableLCA.QuotientClosedMapComposerInputsW365",
    "MetrizableLCA.QuotientClosedMapComposerInputsW365.representative_image_closed",
    "MetrizableLCA.QuotientClosedMapComposerInputsW365.descended_closedMap",
    "MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368",
    "MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.to_w365_inputs",
    "MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.descended_closedMap",
    "MetrizableLCA.currentTargetRepresentativeSaturationV370SupportStateW368",
    "MetrizableLCA.currentTargetRepresentativeSaturationV370SupportStateW368_productSuccess"]

theorem targetRepresentativeSaturationV370SupportDeclarationNamesW368_count :
    targetRepresentativeSaturationV370SupportDeclarationNamesW368.length = 24 := rfl

section Checks

#check MetrizableLCA.IsSaturatedForW365
#check MetrizableLCA.relationPreimagePullbackConditionW365
#check MetrizableLCA.IsStableUnderSubgroupTranslationsW368
#check MetrizableLCA.targetRelationLiftsThroughComponentW368
#check MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW365
#check MetrizableLCA.image_closed_of_isQuotientMap_and_saturatedW365
#check MetrizableLCA.quotientMap_isQuotientMapW365
#check MetrizableLCA.quotientMap_image_closed_of_closed_saturatedW365
#check MetrizableLCA.quotientMap_saturated_of_subgroup_translation_stableW368
#check MetrizableLCA.TargetQuotientClosedOnSaturatedSetsW365
#check MetrizableLCA.targetQuotientClosedOnSaturatedSetsW365
#check MetrizableLCA.targetRepresentativeImageSaturatedW365
#check MetrizableLCA.representativeImage_translation_stable_of_relation_lifts_and_pullbackW368
#check MetrizableLCA.targetRepresentativeImageSaturatedW365_of_relation_lifts_and_pullbackW368
#check MetrizableLCA.representativeImageClosed_of_componentClosed_targetLift_targetClosedW365
#check MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW365
#check MetrizableLCA.QuotientClosedMapComposerInputsW365
#check MetrizableLCA.QuotientClosedMapComposerInputsW365.representative_image_closed
#check MetrizableLCA.QuotientClosedMapComposerInputsW365.descended_closedMap
#check MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368
#check MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.to_w365_inputs
#check MetrizableLCA.TargetRepresentativeSaturationComposerInputsW368.descended_closedMap
#check MetrizableLCA.currentTargetRepresentativeSaturationV370SupportStateW368
#check MetrizableLCA.currentTargetRepresentativeSaturationV370SupportStateW368_productSuccess
#check MetrizableLCA.targetRepresentativeSaturationV370SupportDeclarationNamesW368
#check MetrizableLCA.targetRepresentativeSaturationV370SupportDeclarationNamesW368_count

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
