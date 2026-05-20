import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Audit boundary for equalizer localization transfer into `Dbounded`.

The finite-limit route needs equalizers in the localized category. This file records the
formal transfer theorem: once the non-discrete functor category localization for
`WalkingParallelPair` is available, equalizers transfer to `Dbounded C`, and finite products
then assemble finite limits.
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

namespace HasLimitsOfShapeAux

variable (J) [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

/-- The candidate limit functor on the localized category, induced by `lim ⋙ L`. -/
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

end HasLimitsOfShapeAux

include L W in
/--
Generic limit transfer through a localization, conditional on the corresponding
functor-category localization.

Mathlib already supplies the finite discrete case used for finite products. This audit
isolates the analogous non-discrete finite-shape input needed for equalizers.
-/
lemma hasLimitsOfShape
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasLimitsOfShapeAux.adj (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace EqualizerLocalizationTransferBoundary

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- The precise functor-category localization input still missing for the equalizer route. -/
abbrev WalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair (BoundedComplexCategory C) (Dbounded C)).obj
      (Dbounded.localization C)).IsLocalization
    ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair)

/-- Conditional transfer of `WalkingParallelPair` limits into `Dbounded C`. -/
noncomputable abbrev dboundedHasWalkingParallelPairLimits_of_functorCategoryLocalization
    [HasLimitsOfShape WalkingParallelPair (BoundedComplexCategory C)]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [WalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasLimitsOfShape WalkingParallelPair (Dbounded C) :=
  CategoryTheory.Localization.hasLimitsOfShape
    (Dbounded.localization C) (boundedExactWeakEquivalence C) WalkingParallelPair

/--
Equalizers follow from the generic transfer plus the missing `WalkingParallelPair`
functor-category localization input.
-/
noncomputable abbrev dboundedHasEqualizers_of_functorCategoryLocalization
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [WalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasEqualizers (Dbounded C) := by
  haveI : HasLimitsOfShape WalkingParallelPair (BoundedComplexCategory C) := by
    infer_instance
  exact dboundedHasWalkingParallelPairLimits_of_functorCategoryLocalization C

/--
Equalizers plus the existing finite-product localization route give finite limits, once
product stability, parallel-pair stability, and the functor-category localization input are
available.
-/
noncomputable abbrev dboundedHasFiniteLimits_of_equalizerLocalizationTransfer
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts]
    [(boundedExactWeakEquivalence C).IsStableUnderLimitsOfShape WalkingParallelPair]
    [WalkingParallelPairFunctorCategoryLocalizationInput C] :
    HasFiniteLimits (Dbounded C) := by
  letI : HasFiniteProducts (Dbounded C) := Dbounded.hasFiniteProductsOfStableFiniteProducts C
  letI : HasEqualizers (Dbounded C) :=
    dboundedHasEqualizers_of_functorCategoryLocalization C
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Current state for the equalizer localization-transfer boundary. -/
structure EqualizerLocalizationTransferState : Type where
  formalTransferTheorem : String
  sourceShape : String
  targetShape : String
  firstUnavailableApi : String
  productConsumer : String

/-- The current frontier identifies non-discrete functor-category localization as missing. -/
def currentEqualizerLocalizationTransferState : EqualizerLocalizationTransferState where
  formalTransferTheorem := "CategoryTheory.Localization.hasLimitsOfShape"
  sourceShape := "WalkingParallelPair ⥤ BoundedComplexCategory C"
  targetShape := "WalkingParallelPair ⥤ Dbounded C"
  firstUnavailableApi :=
    "((whiskeringRight WalkingParallelPair _ _).obj (Dbounded.localization C)).IsLocalization ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair)"
  productConsumer := "dboundedHasFiniteLimits_of_equalizerLocalizationTransfer"

theorem currentEqualizerLocalizationTransferState_firstUnavailable :
    currentEqualizerLocalizationTransferState.firstUnavailableApi =
      "((whiskeringRight WalkingParallelPair _ _).obj (Dbounded.localization C)).IsLocalization ((boundedExactWeakEquivalence C).functorCategory WalkingParallelPair)" :=
  rfl

def equalizerLocalizationTransferDeclarationNames : List String :=
  ["CategoryTheory.Localization.hasLimitsOfShape",
    "WalkingParallelPairFunctorCategoryLocalizationInput",
    "dboundedHasWalkingParallelPairLimits_of_functorCategoryLocalization",
    "dboundedHasEqualizers_of_functorCategoryLocalization",
    "dboundedHasFiniteLimits_of_equalizerLocalizationTransfer",
    "currentEqualizerLocalizationTransferState"]

theorem equalizerLocalizationTransferDeclarationNames_count :
    equalizerLocalizationTransferDeclarationNames.length = 6 := rfl

end EqualizerLocalizationTransferBoundary

end LeanLCAExactChallenge
