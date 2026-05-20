import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites

/-!
Bounded opposite localization equalizer transfer for `MetrizableLCA`.

This file combines the concrete source finite-limit input with the localization
transfer shape. The source equalizers and products are concrete; the remaining
assumptions are the opposite localizer stability and functor-category
localization inputs needed to move equalizers to the abstract opposite
localization model.
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

namespace W252HasLimitsOfShapeAux

variable (J) [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

noncomputable abbrev limitFunctor :
    (J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts (L := L) (W := W) J) ((whiskeringRight J C D).obj L)

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

noncomputable def adj :
    Functor.const J ⊣ limitFunctor (L := L) (W := W) J :=
  constLimAdj.localization L W ((whiskeringRight J C D).obj L)
    (W.functorCategory J) (Functor.const J) (limitFunctor (L := L) (W := W) J)

end W252HasLimitsOfShapeAux

include L W in
lemma hasLimitsOfShape_of_functorCategoryLocalization_w252
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (W252HasLimitsOfShapeAux.adj (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedOppositeLocalizationEqualizerW252

structure SourceFiniteColimitInput (C : Type u) [Category.{v} C] : Prop where
  finiteColimits : HasFiniteColimits C

theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits
    (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteColimits C] :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits (BoundedComplexCategory C) := inferInstance
  exact Limits.hasFiniteColimits_opposite_iff.mp inferInstance

theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
    (C : Type u) [Category.{v} C] [Preadditive C]
    (h : SourceFiniteColimitInput C) :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C

theorem metrizableLCA_sourceFiniteColimitInput :
    SourceFiniteColimitInput MetrizableLCA.{u} where
  finiteColimits := inferInstance

theorem metrizableLCA_boundedComplexOp_hasFiniteLimits :
    HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput MetrizableLCA
    metrizableLCA_sourceFiniteColimitInput

theorem metrizableLCA_boundedComplexOp_hasFiniteProducts :
    HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

theorem metrizableLCA_boundedComplexOp_hasEqualizers :
    HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

abbrev metrizableLCA_oppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{u}).op

abbrev MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair
      ((BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ)
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization)).obj
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Q)).IsLocalization
    ((metrizableLCA_oppositeWeakEquivalence.{u}).functorCategory WalkingParallelPair)

theorem metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits
    [(metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderLimitsOfShape WalkingParallelPair]
    [MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput.{u}] :
    HasLimitsOfShape WalkingParallelPair
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
  haveI : HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasEqualizers
  haveI : HasLimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
    infer_instance
  exact CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w252
    ((metrizableLCA_oppositeWeakEquivalence.{u}).Q)
    (metrizableLCA_oppositeWeakEquivalence.{u}) WalkingParallelPair

theorem metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
    [(metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderLimitsOfShape WalkingParallelPair]
    [MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput.{u}] :
    HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) :=
  metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits

theorem metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
    [(metrizableLCA_oppositeWeakEquivalence.{u}).ContainsIdentities]
    [(metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts]
    [(metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderLimitsOfShape WalkingParallelPair]
    [MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput.{u}] :
    HasFiniteLimits ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
  haveI : HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteProducts
  letI : HasFiniteProducts ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
    infer_instance
  letI : HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) :=
    metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

def metrizableLCAOppositeEqualizerTransferHypothesisNames : List String :=
  ["((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderLimitsOfShape WalkingParallelPair",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput"]

theorem metrizableLCAOppositeEqualizerTransferHypothesisNames_count :
    metrizableLCAOppositeEqualizerTransferHypothesisNames.length = 2 := rfl

def metrizableLCAOppositeFiniteLimitTransferHypothesisNames : List String :=
  ["((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities",
    "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderFiniteProducts",
    "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderLimitsOfShape WalkingParallelPair",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput"]

theorem metrizableLCAOppositeFiniteLimitTransferHypothesisNames_count :
    metrizableLCAOppositeFiniteLimitTransferHypothesisNames.length = 4 := rfl

structure BoundedOppositeLocalizationEqualizerState : Type where
  seed : String
  sourceInput : String
  concreteSourceOutput : String
  targetType : String
  equalizerTransferTheorem : String
  finiteLimitTransferTheorem : String
  missingTheorem : String
  productSuccessClaimed : Bool

def currentBoundedOppositeLocalizationEqualizerState :
    BoundedOppositeLocalizationEqualizerState where
  seed := "77f7c3f8c4e6ee03ee265799adc28b89"
  sourceInput := "SourceFiniteColimitInput MetrizableLCA"
  concreteSourceOutput :=
    "HasFiniteLimits, HasFiniteProducts, HasEqualizers on (BoundedComplexCategory MetrizableLCA)^op"
  targetType := "((boundedExactWeakEquivalence MetrizableLCA).op).Localization"
  equalizerTransferTheorem :=
    "metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs"
  finiteLimitTransferTheorem :=
    "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs"
  missingTheorem :=
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput plus opposite stability instances"
  productSuccessClaimed := false

theorem currentBoundedOppositeLocalizationEqualizerState_productSuccess :
    currentBoundedOppositeLocalizationEqualizerState.productSuccessClaimed = false := rfl

def boundedOppositeLocalizationEqualizerDeclarationNames : List String :=
  ["metrizableLCA_sourceFiniteColimitInput",
    "metrizableLCA_boundedComplexOp_hasFiniteLimits",
    "metrizableLCA_boundedComplexOp_hasFiniteProducts",
    "metrizableLCA_boundedComplexOp_hasEqualizers",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits",
    "metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs",
    "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs",
    "currentBoundedOppositeLocalizationEqualizerState"]

theorem boundedOppositeLocalizationEqualizerDeclarationNames_count :
    boundedOppositeLocalizationEqualizerDeclarationNames.length = 9 := rfl

section Checks

#check MetrizableLCA.instHasFiniteColimits
#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits
#check boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
#check metrizableLCA_sourceFiniteColimitInput
#check metrizableLCA_boundedComplexOp_hasFiniteLimits
#check metrizableLCA_boundedComplexOp_hasFiniteProducts
#check metrizableLCA_boundedComplexOp_hasEqualizers
#check metrizableLCA_oppositeWeakEquivalence
#check MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput
#check metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits
#check metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
#check metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
#check metrizableLCAOppositeEqualizerTransferHypothesisNames
#check metrizableLCAOppositeEqualizerTransferHypothesisNames_count
#check metrizableLCAOppositeFiniteLimitTransferHypothesisNames
#check metrizableLCAOppositeFiniteLimitTransferHypothesisNames_count
#check currentBoundedOppositeLocalizationEqualizerState
#check currentBoundedOppositeLocalizationEqualizerState_productSuccess
#check boundedOppositeLocalizationEqualizerDeclarationNames
#check boundedOppositeLocalizationEqualizerDeclarationNames_count
#check CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w252

end Checks

end BoundedOppositeLocalizationEqualizerW252

end LeanLCAExactChallenge
