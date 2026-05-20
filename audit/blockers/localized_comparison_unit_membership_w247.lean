import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
W247 audit: unit/counit membership transport for localized comparison routes.

This file packages the reusable objectwise membership transport needed after a
comparison-factor adjunction has been transported across a natural isomorphism.
It deliberately does not assert that the concrete localized comparison
adjunction exists.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizedComparisonUnitMembershipW247

section ObjectwiseTransport

variable {J : Type u₁} {C : Type u₂} [Category.{v₁} J] [Category.{v₂} C]

/-- Objectwise membership is stable under postcomposition by a natural isomorphism. -/
theorem functorCategory_postcomp_iso_mem
    (W : MorphismProperty C) [W.RespectsIso]
    {F G H : J ⥤ C} (α : F ⟶ G) (e : G ≅ H)
    (hα : W.functorCategory J α) :
    W.functorCategory J (α ≫ e.hom) := by
  intro j
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.postcomp W (e.hom.app j) (α.app j) (hα j)

/-- Objectwise membership is stable under precomposition by a natural isomorphism. -/
theorem functorCategory_precomp_iso_mem
    (W : MorphismProperty C) [W.RespectsIso]
    {F G H : J ⥤ C} (e : F ≅ G) (α : G ⟶ H)
    (hα : W.functorCategory J α) :
    W.functorCategory J (e.hom ≫ α) := by
  intro j
  dsimp [MorphismProperty.functorCategory] at hα ⊢
  simpa using MorphismProperty.RespectsIso.precomp W (e.hom.app j) (α.app j) (hα j)

end ObjectwiseTransport

section AdjunctionTransport

variable {D : Type u₁} {E : Type u₂} [Category.{v₁} D] [Category.{v₂} E]

/-- Unit-membership transport across an isomorphism of left localized composites. -/
theorem rightAdjunction_unit_mem_of_transport_eq
    (W : MorphismProperty D) [W.RespectsIso]
    {F F' : D ⥤ E} {R : E ⥤ D} (e : F ≅ F')
    (adj : F ⊣ R) (adj' : F' ⊣ R)
    (hunit : W.functorCategory D adj.unit)
    (hunit_eq : adj'.unit = adj.unit ≫ (Functor.isoWhiskerRight e R).hom) :
    W.functorCategory D adj'.unit := by
  rw [hunit_eq]
  exact functorCategory_postcomp_iso_mem W adj.unit (Functor.isoWhiskerRight e R) hunit

/-- Counit-membership transport across an isomorphism of right localized composites. -/
theorem leftAdjunction_counit_mem_of_transport_eq
    (W : MorphismProperty D) [W.RespectsIso]
    {L : E ⥤ D} {F F' : D ⥤ E} (e : F ≅ F')
    (adj : L ⊣ F) (adj' : L ⊣ F')
    (hcounit : W.functorCategory D adj.counit)
    (hcounit_eq :
      adj'.counit = (Functor.isoWhiskerRight e L).symm.hom ≫ adj.counit) :
    W.functorCategory D adj'.counit := by
  rw [hcounit_eq]
  exact functorCategory_precomp_iso_mem W (Functor.isoWhiskerRight e L).symm adj.counit
    hcounit

end AdjunctionTransport

structure LocalizedComparisonUnitMembershipState : Type where
  objectwisePostcompTransportPackaged : Bool
  objectwisePrecompTransportPackaged : Bool
  conditionalUnitMembershipTransportPackaged : Bool
  conditionalCounitMembershipTransportPackaged : Bool
  transportedAdjunctionFound : Bool
  productSuccessClaimed : Bool

def currentLocalizedComparisonUnitMembershipState : LocalizedComparisonUnitMembershipState where
  objectwisePostcompTransportPackaged := true
  objectwisePrecompTransportPackaged := true
  conditionalUnitMembershipTransportPackaged := true
  conditionalCounitMembershipTransportPackaged := true
  transportedAdjunctionFound := false
  productSuccessClaimed := false

theorem currentState_has_conditional_membership_transport :
    currentLocalizedComparisonUnitMembershipState.conditionalUnitMembershipTransportPackaged = true ∧
      currentLocalizedComparisonUnitMembershipState.conditionalCounitMembershipTransportPackaged =
        true := by
  exact ⟨rfl, rfl⟩

theorem currentState_not_productSuccess :
    currentLocalizedComparisonUnitMembershipState.productSuccessClaimed = false := rfl

def localizedComparisonUnitMembershipFindings : List String :=
  ["MorphismProperty.functorCategory is objectwise",
    "membership transports across natural isomorphisms when the base property respects isomorphisms",
    "right-adjunction unit membership transports after the explicit W250 unit equality",
    "left-adjunction counit membership transports after the explicit W250 counit equality",
    "the remaining missing input is the concrete transported localized comparison adjunction",
    "no product success is claimed here"]

theorem localizedComparisonUnitMembershipFindings_count :
    localizedComparisonUnitMembershipFindings.length = 6 := rfl

section Checks

#check MorphismProperty.functorCategory
#check functorCategory_postcomp_iso_mem
#check functorCategory_precomp_iso_mem
#check rightAdjunction_unit_mem_of_transport_eq
#check leftAdjunction_counit_mem_of_transport_eq
#check BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso
#check currentState_has_conditional_membership_transport
#check currentState_not_productSuccess
#check localizedComparisonUnitMembershipFindings_count

end Checks

end LocalizedComparisonUnitMembershipW247

end LeanLCAExactChallenge
