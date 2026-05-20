import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W355: descended quotient closed-map support.

W352 isolates `IsClosedMap descended` as a remaining topological input for the
descended quotient morphism.  This standalone file gives a Lean-checked
representative-image criterion for that input.  It is intentionally phrased at
the explicit quotient-object level used by `MetrizableLCA.cokernelObj`: to prove
that the descended map is closed, it suffices to prove that every closed set in
the source quotient has closed target quotient image after pulling it back to
representatives, applying the component map, and projecting to the target
quotient.

This keeps the remaining obligation sharp.  A component closed-map hypothesis
on `iB` alone closes only `iB '' (q_source ⁻¹' C)` in `B'`; the additional
target-quotient image closedness/saturation step is the missing boundary.
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

/--
Representative-image closedness condition for the descended quotient map.

For every closed `C` in the source quotient, pull `C` back along the source
quotient map, apply the representative component map `iB`, and project to the
target quotient.  If that final image is closed, then the descended quotient
map is closed.
-/
abbrev descendedQuotientRepresentativeImageClosedConditionW355
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
The representative-image criterion gives the W352 closed-map input for the
descended quotient morphism.
-/
theorem descendedQuotient_closedMap_of_representativeImageClosedW355
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
      descendedQuotientRepresentativeImageClosedConditionW355
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
Minimal W352-facing package: quotient compatibility plus the representative
closed-image criterion is precisely enough to supply `IsClosedMap descended`.
-/
structure DescendedQuotientClosedMapInputsW355
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  representative_image_closed :
    descendedQuotientRepresentativeImageClosedConditionW355 f g f' g' iB descended

theorem DescendedQuotientClosedMapInputsW355.descended_closedMap
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : DescendedQuotientClosedMapInputsW355 A B A' B' f g f' g' iB descended) :
    IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  descendedQuotient_closedMap_of_representativeImageClosedW355
    iB h.quotient_compat h.representative_image_closed

/--
A still more direct sufficient condition: if the target quotient projection is
closed on all closed representative images arising from closed source-quotient
sets, the representative-image criterion follows.
-/
theorem descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedW355
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (hiB_closedMap : IsClosedMap (iB : B → B'))
    (htarget_closed_on_representative_images :
      ∀ S : Set B', IsClosed S →
        (∃ C : Set (quotientObj B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _)),
          IsClosed C ∧
            S = (iB : B → B') ''
              ((quotientMap B (cokernelSubgroup (f - g))
                  (AddSubgroup.isClosed_topologicalClosure _) :
                    B →
                      quotientObj B (cokernelSubgroup (f - g))
                        (AddSubgroup.isClosed_topologicalClosure _)) ⁻¹' C)) →
        IsClosed
          ((quotientMap B' (cokernelSubgroup (f' - g'))
              (AddSubgroup.isClosed_topologicalClosure _) :
                B' →
                  quotientObj B' (cokernelSubgroup (f' - g'))
                    (AddSubgroup.isClosed_topologicalClosure _)) '' S)) :
    descendedQuotientRepresentativeImageClosedConditionW355
      f g f' g' iB descended := by
  intro C hC
  let qsource :
      B → quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) :=
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
  let representativeImage : Set B' := (iB : B → B') '' (qsource ⁻¹' C)
  have hpre_closed : IsClosed (qsource ⁻¹' C) :=
    hC.preimage
      (quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.continuous
  have hrep_closed : IsClosed representativeImage :=
    hiB_closedMap (qsource ⁻¹' C) hpre_closed
  exact htarget_closed_on_representative_images representativeImage hrep_closed
    ⟨C, hC, rfl⟩

/-- Machine-readable W355 state. -/
structure DescendedQuotientClosedMapV369SupportStateW355 : Type where
  seed : String
  checkedFacts : List String
  sufficientInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentDescendedQuotientClosedMapV369SupportStateW355 :
    DescendedQuotientClosedMapV369SupportStateW355 where
  seed := "ce1793e08388a3c2d47e534e761ac414"
  checkedFacts :=
    ["MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW355",
      "MetrizableLCA.DescendedQuotientClosedMapInputsW355.descended_closedMap",
      "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedW355"]
  sufficientInputs :=
    ["quotient compatibility for the descended quotient map",
      "closedness of target quotient images of representative images for all closed source quotient sets"]
  remainingInputs :=
    ["prove the representative-image closedness criterion for the concrete WPP-op descended quotient map",
      "or prove the component map is closed and the target quotient projection is closed on those representative images",
      "combine this closed-map supplier with W352 relation-pullback and injectivity fields"]
  productSuccessClaimed := false

theorem currentDescendedQuotientClosedMapV369SupportStateW355_productSuccess :
    currentDescendedQuotientClosedMapV369SupportStateW355.productSuccessClaimed = false := rfl

def descendedQuotientClosedMapV369SupportDeclarationNamesW355 : List String :=
  ["MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW355",
    "MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW355",
    "MetrizableLCA.DescendedQuotientClosedMapInputsW355",
    "MetrizableLCA.DescendedQuotientClosedMapInputsW355.descended_closedMap",
    "MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedW355",
    "MetrizableLCA.DescendedQuotientClosedMapV369SupportStateW355",
    "MetrizableLCA.currentDescendedQuotientClosedMapV369SupportStateW355",
    "MetrizableLCA.currentDescendedQuotientClosedMapV369SupportStateW355_productSuccess",
    "MetrizableLCA.descendedQuotientClosedMapV369SupportDeclarationNamesW355",
    "MetrizableLCA.descendedQuotientClosedMapV369SupportDeclarationNamesW355_count"]

theorem descendedQuotientClosedMapV369SupportDeclarationNamesW355_count :
    descendedQuotientClosedMapV369SupportDeclarationNamesW355.length = 10 := rfl

section Checks

#check MetrizableLCA.descendedQuotientRepresentativeImageClosedConditionW355
#check MetrizableLCA.descendedQuotient_closedMap_of_representativeImageClosedW355
#check MetrizableLCA.DescendedQuotientClosedMapInputsW355
#check MetrizableLCA.DescendedQuotientClosedMapInputsW355.descended_closedMap
#check MetrizableLCA.descendedQuotient_representativeImageClosed_of_componentClosed_and_targetProjectionClosedW355
#check MetrizableLCA.DescendedQuotientClosedMapV369SupportStateW355
#check MetrizableLCA.currentDescendedQuotientClosedMapV369SupportStateW355
#check MetrizableLCA.currentDescendedQuotientClosedMapV369SupportStateW355_productSuccess
#check MetrizableLCA.descendedQuotientClosedMapV369SupportDeclarationNamesW355
#check MetrizableLCA.descendedQuotientClosedMapV369SupportDeclarationNamesW355_count
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientMap
#check MetrizableLCA.quotientMap_surjective
#check MetrizableLCA.cokernelSubgroup
#check IsClosedMap

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
