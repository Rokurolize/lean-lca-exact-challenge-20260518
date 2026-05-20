import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W358: saturated representative-image support for descended quotient closedness.

W355 reduced the descended quotient closed-map input to closedness of target
quotient images of representative images.  This file sharpens that boundary:
component closedness of `iB` is enough to make the representative image closed,
and a target quotient projection theorem on closed saturated sets is enough to
finish, provided the concrete representative image is saturated for the target
quotient relation.

Thus the remaining concrete topological input is not merely that `iB` is a
closed map.  One must also show either that the target quotient projection is
closed on the relevant images directly, or that those images are saturated and
the projection is closed on closed saturated sets.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

universe u

/-- A set is saturated with respect to a quotient-like map when it contains the
whole fiber over every point in its image. -/
def IsSaturatedForW358 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

theorem isSaturatedForW358_iff_preimage_image_subset
    {α β : Type _} (q : α → β) (S : Set α) :
    IsSaturatedForW358 q S ↔ q ⁻¹' (q '' S) ⊆ S :=
  Iff.rfl

/--
Representative-image closedness condition from W355, copied locally so this
standalone audit file does not depend on another worker's untracked file.
-/
abbrev descendedQuotientRepresentativeImageClosedConditionW358
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
The saturation/closed-projection reduction for W355's representative-image
condition.

For each closed source quotient set `C`, closedness of `iB` closes the
representative image in `B'`.  A target quotient projection theorem on closed
saturated sets then closes its quotient image.  The remaining non-formal datum
is exactly the saturation of these specific representative images.
-/
theorem descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnSaturatedW358
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (htarget_closed_on_closed_saturated :
      ∀ S : Set B', IsClosed S →
        IsSaturatedForW358
          (quotientMap B' (cokernelSubgroup (f' - g'))
            (AddSubgroup.isClosed_topologicalClosure _) :
              B' →
                quotientObj B' (cokernelSubgroup (f' - g'))
                  (AddSubgroup.isClosed_topologicalClosure _)) S →
        IsClosed
          ((quotientMap B' (cokernelSubgroup (f' - g'))
              (AddSubgroup.isClosed_topologicalClosure _) :
                B' →
                  quotientObj B' (cokernelSubgroup (f' - g'))
                    (AddSubgroup.isClosed_topologicalClosure _)) '' S))
    (hrepresentative_saturated :
      ∀ C : Set (quotientObj B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _)),
        IsClosed C →
          IsSaturatedForW358
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
                        (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C))) :
    descendedQuotientRepresentativeImageClosedConditionW358
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
  have hrep_saturated : IsSaturatedForW358 qtarget representativeImage := by
    exact hrepresentative_saturated C hC
  exact htarget_closed_on_closed_saturated representativeImage hrep_closed hrep_saturated

/--
Boundary form: if the component map is closed, then W355's condition is reduced
to the closedness of the target quotient projection on each closed
representative image.  This isolates the exact target-side obligation without
assuming saturation.
-/
theorem descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnRepresentativeImagesW358
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (htarget_closed_on_representative_images :
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
                          (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C)))) :
    descendedQuotientRepresentativeImageClosedConditionW358
      f g f' g' iB descended := by
  intro C hC
  let qsource :
      B → quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) :=
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
  have hpre_closed : IsClosed (qsource ⁻¹' C) :=
    hC.preimage
      (quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.continuous
  have _hrep_closed : IsClosed ((iB : B → B') '' (qsource ⁻¹' C)) :=
    hiB_closedMap (qsource ⁻¹' C) hpre_closed
  exact htarget_closed_on_representative_images C hC

/-- Machine-readable W358 state. -/
structure DescendedRepresentativeImageClosedV369SupportStateW358 : Type where
  seed : String
  checkedFacts : List String
  sufficientInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentDescendedRepresentativeImageClosedV369SupportStateW358 :
    DescendedRepresentativeImageClosedV369SupportStateW358 where
  seed := "8405dfee50cd7b647e6d584b80bb8ad0"
  checkedFacts :=
    ["MetrizableLCA.IsSaturatedForW358",
      "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnSaturatedW358",
      "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnRepresentativeImagesW358"]
  sufficientInputs :=
    ["IsClosedMap (iB : B → B')",
      "target quotient projection closes closed saturated subsets",
      "the W355 representative images are saturated for the target quotient map"]
  remainingInputs :=
    ["prove saturation of the concrete descended representative images",
      "or prove target quotient projection closedness directly on those representative images",
      "combine this W358 representative-image condition with W355's descended closed-map criterion"]
  productSuccessClaimed := false

theorem currentDescendedRepresentativeImageClosedV369SupportStateW358_productSuccess :
    currentDescendedRepresentativeImageClosedV369SupportStateW358.productSuccessClaimed = false := rfl

def descendedRepresentativeImageClosedV369SupportDeclarationNamesW358 : List String :=
  ["MetrizableLCA.IsSaturatedForW358",
    "MetrizableLCA.isSaturatedForW358_iff_preimage_image_subset",
    "MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW358",
    "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnSaturatedW358",
    "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedOnRepresentativeImagesW358",
    "MetrizableLCA.DescendedRepresentativeImageClosedV369SupportStateW358",
    "MetrizableLCA.currentDescendedRepresentativeImageClosedV369SupportStateW358",
    "MetrizableLCA.currentDescendedRepresentativeImageClosedV369SupportStateW358_productSuccess",
    "MetrizableLCA.descendedRepresentativeImageClosedV369SupportDeclarationNamesW358",
    "MetrizableLCA.descendedRepresentativeImageClosedV369SupportDeclarationNamesW358_count"]

theorem descendedRepresentativeImageClosedV369SupportDeclarationNamesW358_count :
    descendedRepresentativeImageClosedV369SupportDeclarationNamesW358.length = 10 := rfl

end MetrizableLCA

end LeanLCAExactChallenge
