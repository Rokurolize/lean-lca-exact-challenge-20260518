import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
W227 audit: fixed-target universal-property fields for whiskering-right localization.

W223 reduced the non-discrete functor-category localization target for
`(Functor.whiskeringRight J C D).obj L` to the two fixed targets required by
`Functor.IsLocalization.mk'`. This file records the exact four fields needed for each
fixed target and specializes the package to `WalkingParallelPair` for W219/W224.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe w v v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The objectwise functor induced by `L` on `J`-shaped diagrams. -/
abbrev WhiskeringRightObjectwiseFunctor (J : Type w) [Category.{v} J]
    (L : C ⥤ D) : (J ⥤ C) ⥤ (J ⥤ D) :=
  (whiskeringRight J C D).obj L

/--
The formal inversion field for the objectwise functor. A morphism in
`W.functorCategory J` is objectwise in `W`, so the base localization inverts every
component and natural isomorphism is checked componentwise.
-/
lemma whiskeringRightObjectwise_inverts (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] :
    (W.functorCategory J).IsInvertedBy (WhiskeringRightObjectwiseFunctor J L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso (((WhiskeringRightObjectwiseFunctor J L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/--
The four fixed-target fields still needed to turn objectwise whiskering into a
localization. This is deliberately isomorphic to
`StrictUniversalPropertyFixedTarget`, but with the exact source and target categories
expanded for the `J`-functor-category problem.
-/
structure WhiskeringRightFixedTargetFields (L : C ⥤ D) (W : MorphismProperty C)
    (E : Type*) [Category E] where
  inverts :
    (W.functorCategory J).IsInvertedBy (WhiskeringRightObjectwiseFunctor J L)
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      WhiskeringRightObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      WhiskeringRightObjectwiseFunctor J L ⋙ F₁ =
        WhiskeringRightObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace WhiskeringRightFixedTargetFields

variable {L : C ⥤ D} {W : MorphismProperty C}
variable {E : Type*} [Category E]

/-- Convert the expanded field package into mathlib's fixed-target universal property. -/
def toStrictUniversalProperty
    (h : WhiskeringRightFixedTargetFields (J := J) L W E) :
    StrictUniversalPropertyFixedTarget (WhiskeringRightObjectwiseFunctor J L)
      (W.functorCategory J) E where
  inverts := h.inverts
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end WhiskeringRightFixedTargetFields

/--
The exact W223/W224 handoff theorem: the objectwise `J`-diagram functor is a
localization once the fixed-target fields are supplied for the target diagram category
and for the canonical localization model.
-/
lemma whiskeringRight_isLocalization_of_fixedTargetFields
    (L : C ⥤ D) (W : MorphismProperty C)
    (hTarget :
      WhiskeringRightFixedTargetFields (J := J) L W (J ⥤ D))
    (hModel :
      WhiskeringRightFixedTargetFields (J := J) L W
        ((W.functorCategory J).Localization)) :
    (WhiskeringRightObjectwiseFunctor J L).IsLocalization (W.functorCategory J) :=
  Functor.IsLocalization.mk'
    (L := WhiskeringRightObjectwiseFunctor J L) (W := W.functorCategory J)
    hTarget.toStrictUniversalProperty hModel.toStrictUniversalProperty

/--
When the fixed-target fields reuse the formal objectwise inversion field, only `lift`,
`fac`, and `uniq` remain as data to construct for each target.
-/
structure WhiskeringRightRemainingFixedTargetData (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (E : Type*) [Category E] where
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      WhiskeringRightObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      WhiskeringRightObjectwiseFunctor J L ⋙ F₁ =
        WhiskeringRightObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WhiskeringRightFixedTargetUpW227

variable (C : Type*) [Category C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- The fixed-target localization functor needed by W219 for parallel pairs. -/
abbrev WalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ BoundedComplexCategory C) ⥤ (WalkingParallelPair ⥤ Dbounded C) :=
  CategoryTheory.Localization.WhiskeringRightObjectwiseFunctor WalkingParallelPair
    (Dbounded.localization C)

/-- The W219/W224 fixed-target field package for a chosen target category `E`. -/
abbrev WalkingParallelPairFixedTargetFields (E : Type*) [Category E] : Type _ :=
  CategoryTheory.Localization.WhiskeringRightFixedTargetFields
    (J := WalkingParallelPair) (Dbounded.localization C) (boundedExactWeakEquivalence C) E

/-- The precise non-discrete functor-category localization target for W219. -/
abbrev WalkingParallelPairFunctorCategoryLocalizationTarget : Prop :=
  (WalkingParallelPairObjectwiseFunctor C).IsLocalization
    ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair)

/--
The reusable W219 handoff: two fixed-target field packages prove the missing
`WalkingParallelPair` functor-category localization target.
-/
lemma walkingParallelPairTarget_of_fixedTargetFields
    (hTarget : WalkingParallelPairFixedTargetFields C (WalkingParallelPair ⥤ Dbounded C))
    (hModel :
      WalkingParallelPairFixedTargetFields C
        (((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair).Localization)) :
    WalkingParallelPairFunctorCategoryLocalizationTarget C :=
  CategoryTheory.Localization.whiskeringRight_isLocalization_of_fixedTargetFields
    (J := WalkingParallelPair) (Dbounded.localization C) (boundedExactWeakEquivalence C)
    hTarget hModel

/--
After the formal inversion field, these are the two remaining target categories whose
`lift`, `fac`, and `uniq` fields must be built.
-/
def remainingFixedTargetCategories : List String :=
  ["WalkingParallelPair ⥤ Dbounded C",
    "((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair).Localization"]

theorem remainingFixedTargetCategories_count :
    remainingFixedTargetCategories.length = 2 := rfl

/-- Reproducible route state for this worker. -/
structure FixedTargetUpState : Type where
  selectedRoute : Nat
  seedHash : String
  formalInversionField : String
  exactFieldNames : List String
  targetCategories : List String
  nextProbe : String
  productSuccessClaimed : Bool

/-- Route-0 result: name the fields and keep the proof search at the fixed targets. -/
def currentState : FixedTargetUpState where
  selectedRoute := 0
  seedHash := "df2a41beac4f1aad0dc2cbcc73d594f0341382fa7fb230ded57128c61b3a6d01"
  formalInversionField :=
    "CategoryTheory.Localization.whiskeringRightObjectwise_inverts"
  exactFieldNames := ["inverts", "lift", "fac", "uniq"]
  targetCategories := remainingFixedTargetCategories
  nextProbe :=
    "construct lift/fac/uniq for WalkingParallelPair by presenting a functor out of parallel-pair diagrams as compatible data on objects plus the two parallel arrows"
  productSuccessClaimed := false

theorem currentState_route :
    currentState.selectedRoute = 0 := rfl

theorem currentState_productSuccess :
    currentState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W227. -/
def declarationNames : List String :=
  ["CategoryTheory.Localization.WhiskeringRightObjectwiseFunctor",
    "CategoryTheory.Localization.whiskeringRightObjectwise_inverts",
    "CategoryTheory.Localization.WhiskeringRightFixedTargetFields",
    "CategoryTheory.Localization.WhiskeringRightFixedTargetFields.toStrictUniversalProperty",
    "CategoryTheory.Localization.whiskeringRight_isLocalization_of_fixedTargetFields",
    "CategoryTheory.Localization.WhiskeringRightRemainingFixedTargetData",
    "WalkingParallelPairObjectwiseFunctor",
    "WalkingParallelPairFixedTargetFields",
    "WalkingParallelPairFunctorCategoryLocalizationTarget",
    "walkingParallelPairTarget_of_fixedTargetFields",
    "currentState"]

theorem declarationNames_count :
    declarationNames.length = 11 := rfl

section Checks

#check CategoryTheory.Localization.WhiskeringRightObjectwiseFunctor
#check CategoryTheory.Localization.whiskeringRightObjectwise_inverts
#check CategoryTheory.Localization.WhiskeringRightFixedTargetFields
#check CategoryTheory.Localization.WhiskeringRightFixedTargetFields.toStrictUniversalProperty
#check CategoryTheory.Localization.whiskeringRight_isLocalization_of_fixedTargetFields
#check CategoryTheory.Localization.WhiskeringRightRemainingFixedTargetData
#check WalkingParallelPairObjectwiseFunctor
#check WalkingParallelPairFixedTargetFields
#check WalkingParallelPairFunctorCategoryLocalizationTarget
#check walkingParallelPairTarget_of_fixedTargetFields
#check remainingFixedTargetCategories
#check currentState
#check currentState_route
#check currentState_productSuccess
#check declarationNames
#check declarationNames_count

end Checks

end WhiskeringRightFixedTargetUpW227

end LeanLCAExactChallenge
