import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.FiniteProductExactness

/-!
General non-discrete functor-category localization for whiskering right.

Mathlib supplies the finite discrete case in `CategoryTheory.Functor.IsLocalization.pi` and
`Mathlib.CategoryTheory.Localization.FiniteProducts`. The non-discrete analogue needed by
the `WalkingParallelPair` route would say that, for a localization `L : C ⥤ D` at `W`, the
objectwise functor `(Functor.whiskeringRight J C D).obj L : (J ⥤ C) ⥤ (J ⥤ D)` is a
localization at `W.functorCategory J`.

The direct proof is not present in the local API. This file minimizes the remaining input:
the target theorem follows exactly from the two fixed-target universal properties required by
`Functor.IsLocalization.mk'`, and the same target specializes to the `WalkingParallelPair`
input consumed by the equalizer route.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe w v v₁ v₂ u₁ u₂ u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The general theorem needed for a non-discrete finite shape `J`. -/
abbrev WhiskeringRightFunctorCategoryLocalizationTarget
    (J : Type w) [Category.{v} J] (L : C ⥤ D) (W : MorphismProperty C) : Prop :=
  ((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)

/--
The fixed-target universal property still needed for the objectwise functor-category
localization theorem.
-/
abbrev WhiskeringRightFixedTargetUniversalProperty
    (J : Type w) [Category.{v} J] (L : C ⥤ D) (W : MorphismProperty C)
    (E : Type*) [Category E] : Type _ :=
  StrictUniversalPropertyFixedTarget
    ((whiskeringRight J C D).obj L) (W.functorCategory J) E

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace WhiskeringRightFunctorCategoryLocalizationTarget

/--
The objectwise functor inverts objectwise weak equivalences. This part is formal from the
base localization.
-/
lemma inverts :
    (W.functorCategory J).IsInvertedBy ((whiskeringRight J C D).obj L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso ((((whiskeringRight J C D).obj L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/--
The minimized remaining proof obligation: once the two fixed-target universal properties
required by `Functor.IsLocalization.mk'` are supplied, the general localization statement is
immediate.
-/
lemma of_fixedTargetUniversalProperties
    (hTarget :
      WhiskeringRightFixedTargetUniversalProperty J L W (J ⥤ D))
    (hModel :
      WhiskeringRightFixedTargetUniversalProperty J L W
        ((W.functorCategory J).Localization)) :
    WhiskeringRightFunctorCategoryLocalizationTarget J L W :=
  Functor.IsLocalization.mk'
    (L := ((whiskeringRight J C D).obj L)) (W := W.functorCategory J) hTarget hModel

/--
The concrete universal-property gap for arbitrary targets: every functor out of `J ⥤ C`
which inverts objectwise weak equivalences must lift uniquely across the objectwise
localization functor.
-/
abbrev arbitraryTargetLiftingGap (E : Type u) [Category.{v₂} E] : Prop :=
  Nonempty (WhiskeringRightFixedTargetUniversalProperty J L W E)

end WhiskeringRightFunctorCategoryLocalizationTarget

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WhiskeringRightLocalizationGeneralW223

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- The non-discrete finite-shape target, now named as a specialization of the general gap. -/
abbrev WalkingParallelPairWhiskeringRightLocalizationTarget : Prop :=
  CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget
    WalkingParallelPair (Dbounded.localization C) (boundedExactWeakEquivalence C)

/--
The two exact fixed-target universal-property inputs that remain to be supplied for
`WalkingParallelPair`.
-/
abbrev WalkingParallelPairFixedTargetUniversalProperty
    (E : Type*) [Category E] : Type _ :=
  CategoryTheory.Localization.WhiskeringRightFixedTargetUniversalProperty
    WalkingParallelPair (Dbounded.localization C) (boundedExactWeakEquivalence C) E

/-- If the minimized universal-property inputs are available, the missing input follows. -/
lemma walkingParallelPairTarget_of_fixedTargetUniversalProperties
    (hTarget :
      WalkingParallelPairFixedTargetUniversalProperty C (WalkingParallelPair ⥤ Dbounded C))
    (hModel :
      WalkingParallelPairFixedTargetUniversalProperty C
        (((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair).Localization)) :
    WalkingParallelPairWhiskeringRightLocalizationTarget C :=
  CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget.of_fixedTargetUniversalProperties
      (Dbounded.localization C) (boundedExactWeakEquivalence C)
      (J := WalkingParallelPair) hTarget hModel

/-- Route state: discrete products are available; non-discrete lifting is the gap. -/
structure WhiskeringRightLocalizationGeneralState : Type where
  selectedRoute : Nat
  availableDiscreteTheorem : String
  formalObjectwiseInversion : String
  missingTargetUniversalProperty : String
  missingModelUniversalProperty : String
  downstreamConsumer : String

/-- Route-1 state for the current local API. -/
def currentState : WhiskeringRightLocalizationGeneralState where
  selectedRoute := 1
  availableDiscreteTheorem := "CategoryTheory.Functor.IsLocalization.pi"
  formalObjectwiseInversion :=
    "WhiskeringRightFunctorCategoryLocalizationTarget.inverts"
  missingTargetUniversalProperty :=
    "StrictUniversalPropertyFixedTarget ((whiskeringRight WalkingParallelPair _ _).obj (Dbounded.localization C)) ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair) (WalkingParallelPair ⥤ Dbounded C)"
  missingModelUniversalProperty :=
    "StrictUniversalPropertyFixedTarget ((whiskeringRight WalkingParallelPair _ _).obj (Dbounded.localization C)) ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair) (((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair).Localization)"
  downstreamConsumer := "WalkingParallelPairFunctorCategoryLocalizationInput"

theorem currentState_selectedRoute :
    currentState.selectedRoute = 1 := rfl

theorem currentState_availableDiscreteTheorem :
    currentState.availableDiscreteTheorem = "CategoryTheory.Functor.IsLocalization.pi" := rfl

def declarationNames : List String :=
  ["CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget",
    "CategoryTheory.Localization.WhiskeringRightFixedTargetUniversalProperty",
    "CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget.inverts",
    "CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget.of_fixedTargetUniversalProperties",
    "WalkingParallelPairWhiskeringRightLocalizationTarget",
    "WalkingParallelPairFixedTargetUniversalProperty",
    "walkingParallelPairTarget_of_fixedTargetUniversalProperties",
    "currentState"]

theorem declarationNames_count :
    declarationNames.length = 8 := rfl

#check CategoryTheory.Functor.IsLocalization.pi
#check CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget.inverts
#check CategoryTheory.Localization.WhiskeringRightFunctorCategoryLocalizationTarget.of_fixedTargetUniversalProperties
#check WalkingParallelPairWhiskeringRightLocalizationTarget
#check walkingParallelPairTarget_of_fixedTargetUniversalProperties

end WhiskeringRightLocalizationGeneralW223

end LeanLCAExactChallenge
