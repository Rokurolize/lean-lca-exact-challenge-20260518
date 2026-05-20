import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites

/-!
Concrete finite-limit transfer inputs for the opposite localization.

This continues the W248/W252 route for `MetrizableLCA`. It records the concrete
source finite-limit facts on `(BoundedComplexCategory MetrizableLCA)ᵒᵖ`, packages
the exact opposite-side transfer inputs, and states the strongest conditional
finite-limit theorem currently available.
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

namespace W255HasLimitsOfShapeAux

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

end W255HasLimitsOfShapeAux

include L W in
lemma hasLimitsOfShape_of_functorCategoryLocalization_w255
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (W255HasLimitsOfShapeAux.adj (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizationFiniteLimitTransferInputsW255

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

structure MetrizableLCAConcreteSourceFiniteLimitFacts : Prop where
  finiteLimits : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ
  finiteProducts : HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ
  equalizers : HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ

theorem metrizableLCA_concreteSourceFiniteLimitFacts :
    MetrizableLCAConcreteSourceFiniteLimitFacts.{u} where
  finiteLimits := metrizableLCA_boundedComplexOp_hasFiniteLimits
  finiteProducts := metrizableLCA_boundedComplexOp_hasFiniteProducts
  equalizers := metrizableLCA_boundedComplexOp_hasEqualizers

abbrev metrizableLCA_oppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{u}).op

abbrev MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair
      ((BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ)
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization)).obj
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Q)).IsLocalization
    ((metrizableLCA_oppositeWeakEquivalence.{u}).functorCategory WalkingParallelPair)

structure MetrizableLCAOppositeFiniteProductTransferInputs : Prop where
  containsIdentities : (metrizableLCA_oppositeWeakEquivalence.{u}).ContainsIdentities
  stableFiniteProducts : (metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts

structure MetrizableLCAOppositeEqualizerTransferInputs : Prop where
  stableWalkingParallelPair :
    (metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderLimitsOfShape WalkingParallelPair
  functorCategoryLocalization :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput.{u}

structure MetrizableLCAOppositeFiniteLimitTransferInputs : Prop where
  finiteProducts : MetrizableLCAOppositeFiniteProductTransferInputs.{u}
  equalizers : MetrizableLCAOppositeEqualizerTransferInputs.{u}

theorem metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{u})
    (htransfer : MetrizableLCAOppositeEqualizerTransferInputs.{u}) :
    HasLimitsOfShape WalkingParallelPair
      ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
  haveI : HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := hsource.equalizers
  haveI :
      (metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderLimitsOfShape
        WalkingParallelPair := htransfer.stableWalkingParallelPair
  haveI : MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput.{u} :=
    htransfer.functorCategoryLocalization
  haveI : HasLimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
    infer_instance
  exact CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w255
    ((metrizableLCA_oppositeWeakEquivalence.{u}).Q)
    (metrizableLCA_oppositeWeakEquivalence.{u}) WalkingParallelPair

theorem metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{u})
    (htransfer : MetrizableLCAOppositeEqualizerTransferInputs.{u}) :
    HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) :=
  metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits hsource htransfer

theorem metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{u})
    (htransfer : MetrizableLCAOppositeFiniteProductTransferInputs.{u}) :
    HasFiniteProducts ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
  haveI : HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    hsource.finiteProducts
  haveI : (metrizableLCA_oppositeWeakEquivalence.{u}).ContainsIdentities :=
    htransfer.containsIdentities
  haveI : (metrizableLCA_oppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts :=
    htransfer.stableFiniteProducts
  infer_instance

theorem metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{u})
    (htransfer : MetrizableLCAOppositeFiniteLimitTransferInputs.{u}) :
    HasFiniteLimits ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) := by
  letI : HasFiniteProducts ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) :=
    metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs
      hsource htransfer.finiteProducts
  letI : HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{u}).Localization) :=
    metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
      hsource htransfer.equalizers
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

def metrizableLCAOppositeFiniteLimitTransferHypothesisNames : List String :=
  ["MetrizableLCAConcreteSourceFiniteLimitFacts",
    "((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities",
    "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderFiniteProducts",
    "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderLimitsOfShape WalkingParallelPair",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput"]

theorem metrizableLCAOppositeFiniteLimitTransferHypothesisNames_count :
    metrizableLCAOppositeFiniteLimitTransferHypothesisNames.length = 5 := rfl

structure LocalizationFiniteLimitTransferInputState : Type where
  seed : String
  selectedRoute : String
  sourceFacts : String
  targetType : String
  finiteProductConsumer : String
  equalizerConsumer : String
  finiteLimitConsumer : String
  firstUnavailableDeclaration : String
  missingStabilityInstances : List String
  calculusOfFractionsRequired : Bool
  productSuccessClaimed : Bool

def currentLocalizationFiniteLimitTransferInputState :
    LocalizationFiniteLimitTransferInputState where
  seed := "cf89b66ad14dae1dece2a36047c139ca"
  selectedRoute := "opposite-side finite-limit transfer via finite products plus WalkingParallelPair equalizers"
  sourceFacts :=
    "HasFiniteLimits, HasFiniteProducts, HasEqualizers on (BoundedComplexCategory MetrizableLCA)^op"
  targetType := "((boundedExactWeakEquivalence MetrizableLCA).op).Localization"
  finiteProductConsumer := "metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs"
  equalizerConsumer := "metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs"
  finiteLimitConsumer := "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs"
  firstUnavailableDeclaration :=
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput"
  missingStabilityInstances :=
    ["((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderFiniteProducts",
      "((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderLimitsOfShape WalkingParallelPair"]
  calculusOfFractionsRequired := false
  productSuccessClaimed := false

theorem currentLocalizationFiniteLimitTransferInputState_productSuccess :
    currentLocalizationFiniteLimitTransferInputState.productSuccessClaimed = false := rfl

theorem currentLocalizationFiniteLimitTransferInputState_noCalculusOfFractions :
    currentLocalizationFiniteLimitTransferInputState.calculusOfFractionsRequired = false := rfl

def localizationFiniteLimitTransferInputDeclarationNames : List String :=
  ["CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w255",
    "metrizableLCA_boundedComplexOp_hasFiniteLimits",
    "metrizableLCA_boundedComplexOp_hasFiniteProducts",
    "metrizableLCA_boundedComplexOp_hasEqualizers",
    "MetrizableLCAConcreteSourceFiniteLimitFacts",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "MetrizableLCAOppositeFiniteProductTransferInputs",
    "MetrizableLCAOppositeEqualizerTransferInputs",
    "MetrizableLCAOppositeFiniteLimitTransferInputs",
    "metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs",
    "metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs",
    "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs",
    "currentLocalizationFiniteLimitTransferInputState"]

theorem localizationFiniteLimitTransferInputDeclarationNames_count :
    localizationFiniteLimitTransferInputDeclarationNames.length = 13 := rfl

section Checks

#check MetrizableLCA.instHasFiniteColimits
#check metrizableLCA_concreteSourceFiniteLimitFacts
#check MetrizableLCAOppositeFiniteProductTransferInputs
#check MetrizableLCAOppositeEqualizerTransferInputs
#check MetrizableLCAOppositeFiniteLimitTransferInputs
#check metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs
#check metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
#check metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
#check metrizableLCAOppositeFiniteLimitTransferHypothesisNames_count
#check currentLocalizationFiniteLimitTransferInputState_productSuccess
#check currentLocalizationFiniteLimitTransferInputState_noCalculusOfFractions
#check localizationFiniteLimitTransferInputDeclarationNames_count
#check CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w255
#check CategoryTheory.Localization.hasFiniteProducts
#check Limits.hasFiniteColimits_opposite_iff
#check hasFiniteLimits_of_hasEqualizers_and_finite_products

end Checks

end LocalizationFiniteLimitTransferInputsW255

end LeanLCAExactChallenge
