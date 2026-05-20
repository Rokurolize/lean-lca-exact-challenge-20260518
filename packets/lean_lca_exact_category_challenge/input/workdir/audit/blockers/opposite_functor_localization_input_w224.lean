import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W224: opposite `WalkingParallelPair` functor-category localization input.

W219 isolates the general non-discrete functor-category localization shape needed to
transfer `WalkingParallelPair` limits through a localization. W220 then needs that shape
for the opposite bounded weak-equivalence localizer.

This file specializes the W219 shape to the opposite localizer and records the smallest
conditional package that can feed W220. It does not prove the missing non-discrete
functor-category localization theorem.
-/

set_option autoImplicit false

noncomputable section

universe w v v₁ v₂ u₁ u₂ u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- W224-local name for the W219 non-discrete functor-category localization input. -/
abbrev W224FunctorCategoryLocalizationInput
    (J : Type w) [Category.{v} J] (L : C ⥤ D) (W : MorphismProperty C) : Prop :=
  ((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)

variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace W224HasLimitsOfShapeFromFunctorCategoryLocalization

variable (J)
variable [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [W224FunctorCategoryLocalizationInput J L W]

/-- The localized limit functor induced by `lim ⋙ L`. -/
noncomputable abbrev limitFunctor :
    (J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts (L := L) (W := W) J) ((whiskeringRight J C D).obj L)

/-- `limitFunctor` is induced by the source limit functor. -/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight J C D).obj L) ⋙ limitFunctor (L := L) (W := W) J ≅ lim ⋙ L := by
  apply Localization.fac

instance :
    CatCommSq (Functor.const J) L
      ((whiskeringRight J C D).obj L) (Functor.const J) where
  iso := (Functor.compConstIso J L).symm

noncomputable instance :
    CatCommSq lim ((whiskeringRight J C D).obj L) L
      (limitFunctor (L := L) (W := W) J) where
  iso := (compLimitFunctorIso (L := L) (W := W) J).symm

/-- The constant/limit adjunction descends through the two localization functors. -/
noncomputable def adj :
    Functor.const J ⊣ limitFunctor (L := L) (W := W) J :=
  constLimAdj.localization L W ((whiskeringRight J C D).obj L)
    (W.functorCategory J) (Functor.const J) (limitFunctor (L := L) (W := W) J)

end W224HasLimitsOfShapeFromFunctorCategoryLocalization

include L W in
/--
Generic transfer of limits of shape `J` through a localization, conditional on the
corresponding functor-category localization input.
-/
lemma hasLimitsOfShape_of_w224FunctorCategoryLocalization
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [W224FunctorCategoryLocalizationInput J L W] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (W224HasLimitsOfShapeFromFunctorCategoryLocalization.adj
      (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFunctorLocalizationInputW224

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- Abbreviation for the opposite bounded weak-equivalence localizer. -/
abbrev oppositeWeakEquivalence : MorphismProperty (BoundedComplexCategory C)ᵒᵖ :=
  (boundedExactWeakEquivalence C).op

/--
The W220 missing input, expressed as the W219 general functor-category localization shape.
-/
abbrev OppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  CategoryTheory.Localization.W224FunctorCategoryLocalizationInput
    WalkingParallelPair ((oppositeWeakEquivalence C).Q) (oppositeWeakEquivalence C)

/-- The same input unfolded into W220's exact objectwise-localization statement. -/
theorem oppositeWalkingParallelPairFunctorCategoryLocalizationInput_iff :
    OppositeWalkingParallelPairFunctorCategoryLocalizationInput C ↔
      ((Functor.whiskeringRight WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ)
          ((oppositeWeakEquivalence C).Localization)).obj
          ((oppositeWeakEquivalence C).Q)).IsLocalization
        ((oppositeWeakEquivalence C).functorCategory WalkingParallelPair) :=
  Iff.rfl

/--
Conditional transfer of `WalkingParallelPair` limits to W220's abstract opposite
localization model.
-/
noncomputable abbrev oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization
    [HasLimitsOfShape WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasLimitsOfShape WalkingParallelPair ((oppositeWeakEquivalence C).Localization) :=
  CategoryTheory.Localization.hasLimitsOfShape_of_w224FunctorCategoryLocalization
    ((oppositeWeakEquivalence C).Q) (oppositeWeakEquivalence C) WalkingParallelPair

/-- The direct opposite of the existing `Dbounded` localization functor is a localization. -/
theorem dboundedLocalization_op_isLocalization :
    ((Dbounded.localization C).op).IsLocalization (oppositeWeakEquivalence C) := by
  infer_instance

/--
The corresponding direct-model input for `(Dbounded C)ᵒᵖ`. This is a concrete variant of
the W219 shape, but it is still the same missing non-discrete functor-category theorem.
-/
abbrev DirectOppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  CategoryTheory.Localization.W224FunctorCategoryLocalizationInput
    WalkingParallelPair ((Dbounded.localization C).op) (oppositeWeakEquivalence C)

/-- Conditional transfer of `WalkingParallelPair` limits to the direct opposite model. -/
noncomputable abbrev dboundedOpHasWalkingParallelPairLimits_of_directFunctorCategoryLocalization
    [HasLimitsOfShape WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [DirectOppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasLimitsOfShape WalkingParallelPair (Dbounded C)ᵒᵖ :=
  CategoryTheory.Localization.hasLimitsOfShape_of_w224FunctorCategoryLocalization
    ((Dbounded.localization C).op) (oppositeWeakEquivalence C) WalkingParallelPair

/-- Equalizers in W220's abstract opposite model, conditional on the named input. -/
noncomputable abbrev oppositeLocalizationHasEqualizers_of_functorCategoryLocalization
    [HasEqualizers ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasEqualizers ((oppositeWeakEquivalence C).Localization) := by
  haveI : HasLimitsOfShape WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ) := by
    infer_instance
  exact oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization C

/-- Named assumptions for the W220-facing opposite functor-category route. -/
def oppositeFunctorLocalizationInputHypothesisNames : List String :=
  ["HasLimitsOfShape WalkingParallelPair (BoundedComplexCategory C)^op",
    "((boundedExactWeakEquivalence C).op).IsStableUnderLimitsOfShape WalkingParallelPair",
    "OppositeWalkingParallelPairFunctorCategoryLocalizationInput C"]

theorem oppositeFunctorLocalizationInputHypothesisNames_count :
    oppositeFunctorLocalizationInputHypothesisNames.length = 3 := rfl

/-- Audit state for this frontier. -/
structure OppositeFunctorLocalizationInputState : Type where
  selectedRoute : Nat
  previousWorkers : List String
  generalShape : String
  abstractInput : String
  directModelInput : String
  firstUnavailableProof : String
  w220Feed : String
  productSuccessClaimed : Bool

/-- Reproducible boundary state for this worker. -/
def currentOppositeFunctorLocalizationInputState : OppositeFunctorLocalizationInputState where
  selectedRoute := 2
  previousWorkers := ["W219", "W220"]
  generalShape := "CategoryTheory.Localization.W224FunctorCategoryLocalizationInput"
  abstractInput := "OppositeWalkingParallelPairFunctorCategoryLocalizationInput C"
  directModelInput := "DirectOppositeWalkingParallelPairFunctorCategoryLocalizationInput C"
  firstUnavailableProof :=
    "non-discrete WalkingParallelPair functor-category localization for the opposite localizer"
  w220Feed := "oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization"
  productSuccessClaimed := false

theorem currentOppositeFunctorLocalizationInputState_route :
    currentOppositeFunctorLocalizationInputState.selectedRoute = 2 := rfl

theorem currentOppositeFunctorLocalizationInputState_productSuccess :
    currentOppositeFunctorLocalizationInputState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeFunctorLocalizationInputDeclarationNames : List String :=
  ["CategoryTheory.Localization.W224FunctorCategoryLocalizationInput",
    "CategoryTheory.Localization.hasLimitsOfShape_of_w224FunctorCategoryLocalization",
    "oppositeWeakEquivalence",
    "OppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "oppositeWalkingParallelPairFunctorCategoryLocalizationInput_iff",
    "oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization",
    "dboundedLocalization_op_isLocalization",
    "DirectOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "dboundedOpHasWalkingParallelPairLimits_of_directFunctorCategoryLocalization",
    "oppositeLocalizationHasEqualizers_of_functorCategoryLocalization",
    "currentOppositeFunctorLocalizationInputState"]

theorem oppositeFunctorLocalizationInputDeclarationNames_count :
    oppositeFunctorLocalizationInputDeclarationNames.length = 11 := rfl

section Checks

#check CategoryTheory.Localization.W224FunctorCategoryLocalizationInput
#check CategoryTheory.Localization.hasLimitsOfShape_of_w224FunctorCategoryLocalization
#check oppositeWeakEquivalence
#check OppositeWalkingParallelPairFunctorCategoryLocalizationInput
#check oppositeWalkingParallelPairFunctorCategoryLocalizationInput_iff
#check oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization
#check dboundedLocalization_op_isLocalization
#check DirectOppositeWalkingParallelPairFunctorCategoryLocalizationInput
#check dboundedOpHasWalkingParallelPairLimits_of_directFunctorCategoryLocalization
#check oppositeLocalizationHasEqualizers_of_functorCategoryLocalization
#check oppositeFunctorLocalizationInputHypothesisNames
#check oppositeFunctorLocalizationInputHypothesisNames_count
#check OppositeFunctorLocalizationInputState
#check currentOppositeFunctorLocalizationInputState
#check currentOppositeFunctorLocalizationInputState_route
#check currentOppositeFunctorLocalizationInputState_productSuccess
#check oppositeFunctorLocalizationInputDeclarationNames
#check oppositeFunctorLocalizationInputDeclarationNames_count

end Checks

end OppositeFunctorLocalizationInputW224

end LeanLCAExactChallenge
