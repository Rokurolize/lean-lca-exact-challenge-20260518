import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W360: descended representative-image saturation and quotient-closed support.

W358 isolated the target-side obligation for W355: the image of each closed
source quotient preimage under the target quotient map is closed once that
representative image is closed and saturated.  This file checks the missing
saturation algebra in a standalone form.

The concrete content is deliberately conditional.  A quotient preimage is
saturated when the set is stable under translations by the quotient subgroup.
For descended representative images, that translation stability follows from:

* a pullback equality between the source relation subgroup and the target
  relation subgroup preimage along `iB`;
* a target-relation lifting statement saying target relation elements that must
  be absorbed by the image lift through `iB`.

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

/-- A set is saturated for a map when it contains every full fiber over its image. -/
def IsSaturatedForW360 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- Stability under translations by a subgroup. -/
def IsStableUnderSubgroupTranslationsW360 {X : Type _} [AddGroup X]
    (N : AddSubgroup X) (S : Set X) : Prop :=
  ∀ x : X, x ∈ S → ∀ n : X, n ∈ N → x + n ∈ S

/--
For an additive quotient, translation stability by the quotient subgroup is
enough to prove saturation for the quotient map.
-/
theorem quotientMap_saturated_of_subgroup_translation_stableW360
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X}
    (hstable : IsStableUnderSubgroupTranslationsW360 N S) :
    IsSaturatedForW360
      (quotientMap X N hN : X → quotientObj X N hN) S := by
  intro y hy
  rcases hy with ⟨x, hxS, hq⟩
  have hdiff : y - x ∈ N := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp (by
      simpa [quotientMap_apply] using hq.symm)
  have hy_eq : y = x + (y - x) := by abel
  rw [hy_eq]
  exact hstable x hxS (y - x) hdiff

/-- Source-target relation pullback equality for the descended component `iB`. -/
abbrev relationPreimagePullbackConditionW360
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/--
The target relation elements relevant to the representative image lift through
the component map.
-/
abbrev targetRelationLiftsThroughComponentW360
    {B A' B' : MetrizableLCA.{u}} (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/--
Target-relation lifting plus the source-target relation pullback equality gives
the concrete translate closure needed for representative-image saturation.
-/
theorem representativeImage_translation_stable_of_relation_lifts_and_pullbackW360
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW360 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW360 f' g' iB)
    (C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _))) :
    IsStableUnderSubgroupTranslationsW360
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
      simpa [relationPreimagePullbackConditionW360] using (hpullback ▸ hd_comap)
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
The W358 representative images are saturated for the target quotient whenever
the target relation lifts through `iB` and the source relation subgroup is the
preimage of the target relation subgroup.
-/
theorem representativeImage_saturated_of_relation_lifts_and_pullbackW360
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW360 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW360 f' g' iB)
    (C : Set (quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _))) :
    IsSaturatedForW360
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
                  (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C)) :=
  quotientMap_saturated_of_subgroup_translation_stableW360
    B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _)
    (representativeImage_translation_stable_of_relation_lifts_and_pullbackW360
      iB hpullback hlift C)

/--
Named target quotient theorem shape: the target quotient projection closes
closed saturated sets.  W360 does not assert this theorem globally; it records
the exact local API needed by the W355/W358 consumer.
-/
structure TargetQuotientClosedOnSaturatedSetsW360
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW360 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/--
Representative-image closedness condition from W355/W358, copied locally so the
file remains standalone.
-/
abbrev descendedQuotientRepresentativeImageClosedConditionW360
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

/--
Closed representative images plus W360 saturation feed the named target
closed-on-saturated quotient theorem, giving the W355/W358 representative-image
closedness condition.
-/
theorem descendedQuotient_representativeImageClosed_of_relation_lifts_pullback_and_targetClosedOnSaturatedW360
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (hpullback : relationPreimagePullbackConditionW360 f g f' g' iB)
    (hlift : targetRelationLiftsThroughComponentW360 f' g' iB)
    (htarget :
      TargetQuotientClosedOnSaturatedSetsW360 B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :
    descendedQuotientRepresentativeImageClosedConditionW360
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
  have hrep_saturated : IsSaturatedForW360 qtarget representativeImage := by
    exact representativeImage_saturated_of_relation_lifts_and_pullbackW360
      iB hpullback hlift C
  exact htarget.closed_image representativeImage hrep_closed hrep_saturated

/-- Machine-readable W360 state. -/
structure DescendedSaturationQuotientClosedV369SupportStateW360 : Type where
  seed : String
  checkedFacts : List String
  sufficientInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentDescendedSaturationQuotientClosedV369SupportStateW360 :
    DescendedSaturationQuotientClosedV369SupportStateW360 where
  seed := "8165dc1339949089a56a5b6d010a2c2d"
  checkedFacts :=
    ["MetrizableLCA.quotientMap_saturated_of_subgroup_translation_stableW360",
      "MetrizableLCA.representativeImage_translation_stable_of_relation_lifts_and_pullbackW360",
      "MetrizableLCA.representativeImage_saturated_of_relation_lifts_and_pullbackW360",
      "MetrizableLCA.descendedQuotient_representativeImageClosed_of_relation_lifts_pullback_and_targetClosedOnSaturatedW360"]
  sufficientInputs :=
    ["IsClosedMap (iB : B → B')",
      "relationPreimagePullbackConditionW360 f g f' g' iB",
      "targetRelationLiftsThroughComponentW360 f' g' iB",
      "TargetQuotientClosedOnSaturatedSetsW360 for the target relation quotient"]
  remainingInputs :=
    ["instantiate target-relation lifting for the concrete descended map",
      "instantiate target quotient closedness on closed saturated subsets",
      "connect this representative-image condition to the upstream W355 closed-map criterion"]
  productSuccessClaimed := false

theorem currentDescendedSaturationQuotientClosedV369SupportStateW360_productSuccess :
    currentDescendedSaturationQuotientClosedV369SupportStateW360.productSuccessClaimed = false := rfl

def descendedSaturationQuotientClosedV369SupportDeclarationNamesW360 : List String :=
  ["MetrizableLCA.IsSaturatedForW360",
    "MetrizableLCA.IsStableUnderSubgroupTranslationsW360",
    "MetrizableLCA.quotientMap_saturated_of_subgroup_translation_stableW360",
    "MetrizableLCA.relationPreimagePullbackConditionW360",
    "MetrizableLCA.targetRelationLiftsThroughComponentW360",
    "MetrizableLCA.representativeImage_translation_stable_of_relation_lifts_and_pullbackW360",
    "MetrizableLCA.representativeImage_saturated_of_relation_lifts_and_pullbackW360",
    "MetrizableLCA.TargetQuotientClosedOnSaturatedSetsW360",
    "MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW360",
    "MetrizableLCA.descendedQuotient_representativeImageClosed_of_relation_lifts_pullback_and_targetClosedOnSaturatedW360",
    "MetrizableLCA.currentDescendedSaturationQuotientClosedV369SupportStateW360",
    "MetrizableLCA.currentDescendedSaturationQuotientClosedV369SupportStateW360_productSuccess",
    "MetrizableLCA.descendedSaturationQuotientClosedV369SupportDeclarationNamesW360",
    "MetrizableLCA.descendedSaturationQuotientClosedV369SupportDeclarationNamesW360_count"]

theorem descendedSaturationQuotientClosedV369SupportDeclarationNamesW360_count :
    descendedSaturationQuotientClosedV369SupportDeclarationNamesW360.length = 14 := rfl

end MetrizableLCA

end LeanLCAExactChallenge
