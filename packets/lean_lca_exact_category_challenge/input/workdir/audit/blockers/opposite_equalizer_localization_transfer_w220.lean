import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import LeanLCAExactChallenge.Derived.Bounded

/-!
Opposite equalizer localization transfer boundary.

Support worker w220 specialized the equalizer localization-transfer route to
`(boundedExactWeakEquivalence C).op.Localization`. This is the opposite-side input needed by
the finite-colimits route after v237 reduced `HasFiniteColimits (Dbounded C)` to finite limits
on the abstract opposite localization.

This file does not claim the missing functor-category localization input. It names that
input and records the conditional finite-limit consumer.
-/

set_option autoImplicit false

noncomputable section

universe w v₁ v₂ u₁ u₂ v u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace W220HasLimitsOfShapeAux

variable (J) [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

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

/-- The constant/limit adjunction descends through the localization functors. -/
noncomputable def adj :
    Functor.const J ⊣ limitFunctor (L := L) (W := W) J :=
  constLimAdj.localization L W ((whiskeringRight J C D).obj L)
    (W.functorCategory J) (Functor.const J) (limitFunctor (L := L) (W := W) J)

end W220HasLimitsOfShapeAux

include L W in
/--
Generic transfer of limits of shape `J` through a localization, conditional on the
corresponding functor-category localization.
-/
lemma hasLimitsOfShape_of_functorCategoryLocalization
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (W220HasLimitsOfShapeAux.adj (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeEqualizerLocalizationTransferW220

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- Abbreviation for the opposite bounded weak-equivalence localizer. -/
abbrev oppositeWeakEquivalence : MorphismProperty (BoundedComplexCategory C)ᵒᵖ :=
  (boundedExactWeakEquivalence C).op

/--
The precise opposite-side `WalkingParallelPair` functor-category localization input.

This is the v238 missing input after replacing `BoundedComplexCategory C` by its opposite
and the localization functor by `((boundedExactWeakEquivalence C).op).Q`.
-/
abbrev OppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ)
      ((oppositeWeakEquivalence C).Localization)).obj
      ((oppositeWeakEquivalence C).Q)).IsLocalization
    ((oppositeWeakEquivalence C).functorCategory WalkingParallelPair)

/-- Conditional transfer of `WalkingParallelPair` limits to the opposite localization model. -/
noncomputable abbrev oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization
    [HasLimitsOfShape WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasLimitsOfShape WalkingParallelPair ((oppositeWeakEquivalence C).Localization) :=
  CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
    ((oppositeWeakEquivalence C).Q) (oppositeWeakEquivalence C) WalkingParallelPair

/--
Equalizers in the opposite localization follow from source equalizers, opposite
`WalkingParallelPair` stability, and the named functor-category localization input.
-/
noncomputable abbrev oppositeLocalizationHasEqualizers_of_functorCategoryLocalization
    [HasEqualizers ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).HasLeftCalculusOfFractions]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasEqualizers ((oppositeWeakEquivalence C).Localization) := by
  haveI : HasLimitsOfShape WalkingParallelPair ((BoundedComplexCategory C)ᵒᵖ) := by
    infer_instance
  exact oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization C

/--
The equalizer-transfer theorem shape requested by the opposite finite-colimits route,
discharged by the functor-category-localization route.
-/
abbrev OppositeEqualizerLocalizationTransferTheorem : Prop :=
  ∀ [HasEqualizers ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).HasLeftCalculusOfFractions]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C],
      HasEqualizers ((oppositeWeakEquivalence C).Localization)

/-- The conditional transfer theorem, with the equalizer-transfer hypotheses exposed. -/
theorem oppositeEqualizerLocalizationTransferTheorem
    [HasEqualizers ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).HasLeftCalculusOfFractions]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasEqualizers ((oppositeWeakEquivalence C).Localization) :=
  oppositeLocalizationHasEqualizers_of_functorCategoryLocalization C

/--
Finite limits on the opposite localization reduce to finite-product input plus the
opposite-side functor-category localization input.
-/
noncomputable abbrev oppositeLocalizationHasFiniteLimits_of_equalizerLocalizationTransfer
    [HasFiniteProducts ((BoundedComplexCategory C)ᵒᵖ)]
    [HasEqualizers ((BoundedComplexCategory C)ᵒᵖ)]
    [(oppositeWeakEquivalence C).ContainsIdentities]
    [(oppositeWeakEquivalence C).HasLeftCalculusOfFractions]
    [(oppositeWeakEquivalence C).IsStableUnderFiniteProducts]
    [(oppositeWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [OppositeWalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasFiniteLimits ((oppositeWeakEquivalence C).Localization) := by
  letI : HasFiniteProducts ((oppositeWeakEquivalence C).Localization) := by
    infer_instance
  letI : HasEqualizers ((oppositeWeakEquivalence C).Localization) :=
    oppositeLocalizationHasEqualizers_of_functorCategoryLocalization C
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Named assumptions for the selected equalizer route. -/
def oppositeEqualizerRouteHypothesisNames : List String :=
  ["HasFiniteProducts (BoundedComplexCategory C)^op",
    "HasEqualizers (BoundedComplexCategory C)^op",
    "((boundedExactWeakEquivalence C).op).ContainsIdentities",
    "((boundedExactWeakEquivalence C).op).HasLeftCalculusOfFractions",
    "((boundedExactWeakEquivalence C).op).IsStableUnderFiniteProducts",
    "((boundedExactWeakEquivalence C).op).IsStableUnderLimitsOfShape WalkingParallelPair",
    "OppositeWalkingParallelPairFunctorCategoryLocalizationInput C"]

theorem oppositeEqualizerRouteHypothesisNames_count :
    oppositeEqualizerRouteHypothesisNames.length = 7 := rfl

/-- Audit state for this opposite equalizer transfer frontier. -/
structure OppositeEqualizerLocalizationTransferState : Type where
  selectedRoute : Nat
  previousWorkers : List String
  formalTransferTheorem : String
  sourceShape : String
  targetShape : String
  firstUnavailableInput : String
  finiteLimitConsumer : String
  productSuccessClaimed : Bool

/-- Reproducible boundary state for this opposite equalizer transfer. -/
def currentOppositeEqualizerLocalizationTransferState :
    OppositeEqualizerLocalizationTransferState where
  selectedRoute := 1
  previousWorkers := ["W218", "W213"]
  formalTransferTheorem :=
    "CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization"
  sourceShape := "WalkingParallelPair -> (BoundedComplexCategory C)^op"
  targetShape :=
    "WalkingParallelPair -> ((boundedExactWeakEquivalence C).op).Localization"
  firstUnavailableInput :=
    "OppositeWalkingParallelPairFunctorCategoryLocalizationInput C"
  finiteLimitConsumer :=
    "oppositeLocalizationHasFiniteLimits_of_equalizerLocalizationTransfer"
  productSuccessClaimed := false

theorem currentOppositeEqualizerLocalizationTransferState_route :
    currentOppositeEqualizerLocalizationTransferState.selectedRoute = 1 := rfl

theorem currentOppositeEqualizerLocalizationTransferState_productSuccess :
    currentOppositeEqualizerLocalizationTransferState.productSuccessClaimed = false := rfl

/-- Named declarations produced by this audit file. -/
def oppositeEqualizerLocalizationTransferDeclarationNames : List String :=
  ["CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization",
    "OppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization",
    "oppositeLocalizationHasEqualizers_of_functorCategoryLocalization",
    "OppositeEqualizerLocalizationTransferTheorem",
    "oppositeEqualizerLocalizationTransferTheorem",
    "oppositeLocalizationHasFiniteLimits_of_equalizerLocalizationTransfer",
    "currentOppositeEqualizerLocalizationTransferState"]

theorem oppositeEqualizerLocalizationTransferDeclarationNames_count :
    oppositeEqualizerLocalizationTransferDeclarationNames.length = 8 := rfl

section Checks

#check CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
#check CategoryTheory.Localization.W220HasLimitsOfShapeAux.limitFunctor
#check CategoryTheory.Localization.W220HasLimitsOfShapeAux.compLimitFunctorIso
#check CategoryTheory.Localization.W220HasLimitsOfShapeAux.adj
#check oppositeWeakEquivalence
#check OppositeWalkingParallelPairFunctorCategoryLocalizationInput
#check oppositeLocalizationHasWalkingParallelPairLimits_of_functorCategoryLocalization
#check oppositeLocalizationHasEqualizers_of_functorCategoryLocalization
#check OppositeEqualizerLocalizationTransferTheorem
#check oppositeEqualizerLocalizationTransferTheorem
#check oppositeLocalizationHasFiniteLimits_of_equalizerLocalizationTransfer
#check oppositeEqualizerRouteHypothesisNames
#check oppositeEqualizerRouteHypothesisNames_count
#check OppositeEqualizerLocalizationTransferState
#check currentOppositeEqualizerLocalizationTransferState
#check currentOppositeEqualizerLocalizationTransferState_route
#check currentOppositeEqualizerLocalizationTransferState_productSuccess
#check oppositeEqualizerLocalizationTransferDeclarationNames
#check oppositeEqualizerLocalizationTransferDeclarationNames_count
#check CategoryTheory.Localization.hasFiniteProducts
#check CategoryTheory.MorphismProperty.IsStableUnderFiniteProducts
#check CategoryTheory.MorphismProperty.IsStableUnderLimitsOfShape
#check WalkingParallelPair
#check HasEqualizers
#check HasFiniteLimits

end Checks

end OppositeEqualizerLocalizationTransferW220

end LeanLCAExactChallenge
