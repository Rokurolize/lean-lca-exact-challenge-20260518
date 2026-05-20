import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W269: opposite `WalkingParallelPair` functor-category localization boundary.

W224 names the missing opposite non-discrete functor-category localization input.
W227 reduces the general whiskering-right localization problem to two fixed-target
field packages. W231 constructs a checked `lift` functor from coherent strict source
representatives.

This file specializes those two fixed-target fields to the opposite bounded weak
equivalence localizer and records a checked conditional `lift` constructor for the
opposite abstract localization model. It does not prove the missing fixed-target
`fac`/`uniq` fields, nor does it claim product completion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe w v v₁ v₂ u₁ u₂ u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- W269-local spelling of the objectwise functor induced by a localization functor. -/
abbrev W269WhiskeringRightObjectwiseFunctor (J : Type w) [Category.{v} J]
    (L : C ⥤ D) : (J ⥤ C) ⥤ (J ⥤ D) :=
  (whiskeringRight J C D).obj L

/--
The formal `inverts` field for objectwise whiskering. This is the one fixed-target
field that follows directly from the base localization.
-/
lemma w269WhiskeringRightObjectwise_inverts (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] :
    (W.functorCategory J).IsInvertedBy (W269WhiskeringRightObjectwiseFunctor J L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso (((W269WhiskeringRightObjectwiseFunctor J L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/-- The four fixed-target fields needed by `Functor.IsLocalization.mk'`. -/
structure W269WhiskeringRightFixedTargetFields (L : C ⥤ D) (W : MorphismProperty C)
    (E : Type*) [Category E] where
  inverts :
    (W.functorCategory J).IsInvertedBy (W269WhiskeringRightObjectwiseFunctor J L)
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      W269WhiskeringRightObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      W269WhiskeringRightObjectwiseFunctor J L ⋙ F₁ =
        W269WhiskeringRightObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace W269WhiskeringRightFixedTargetFields

variable {L : C ⥤ D} {W : MorphismProperty C}
variable {E : Type*} [Category E]

/-- Convert the expanded W269 field package into mathlib's fixed-target property. -/
def toStrictUniversalProperty
    (h : W269WhiskeringRightFixedTargetFields (J := J) L W E) :
    StrictUniversalPropertyFixedTarget (W269WhiskeringRightObjectwiseFunctor J L)
      (W.functorCategory J) E where
  inverts := h.inverts
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end W269WhiskeringRightFixedTargetFields

/--
After the formal inversion field, the remaining data for each fixed target is exactly
`lift`, `fac`, and `uniq`.
-/
structure W269WhiskeringRightRemainingFixedTargetData (L : C ⥤ D)
    (W : MorphismProperty C) [L.IsLocalization W] (E : Type*) [Category E] where
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      W269WhiskeringRightObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      W269WhiskeringRightObjectwiseFunctor J L ⋙ F₁ =
        W269WhiskeringRightObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace W269WhiskeringRightRemainingFixedTargetData

variable {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
variable {E : Type*} [Category E]

/-- Add the formal `inverts` field to a remaining-field package. -/
def toFixedTargetFields
    (h : W269WhiskeringRightRemainingFixedTargetData (J := J) L W E) :
    W269WhiskeringRightFixedTargetFields (J := J) L W E where
  inverts := w269WhiskeringRightObjectwise_inverts (J := J) L W
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end W269WhiskeringRightRemainingFixedTargetData

/--
The two-target theorem boundary for objectwise functor-category localization:
one remaining-field package for `J ⥤ D`, and one for the localization model.
-/
structure W269TwoFixedTargetBoundary (J : Type w) [Category.{v} J]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] where
  target :
    W269WhiskeringRightRemainingFixedTargetData (J := J) L W (J ⥤ D)
  model :
    W269WhiskeringRightRemainingFixedTargetData (J := J) L W
      ((W.functorCategory J).Localization)

/-- The checked consumer for the W269 two-target boundary. -/
lemma w269WhiskeringRight_isLocalization_of_twoFixedTargetBoundary
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (h : W269TwoFixedTargetBoundary J L W) :
    (W269WhiskeringRightObjectwiseFunctor J L).IsLocalization (W.functorCategory J) :=
  Functor.IsLocalization.mk'
    (L := W269WhiskeringRightObjectwiseFunctor J L) (W := W.functorCategory J)
    h.target.toFixedTargetFields.toStrictUniversalProperty
    h.model.toFixedTargetFields.toStrictUniversalProperty

/--
Coherent strict source representatives for target `WalkingParallelPair` diagrams.
This is the checked data needed to construct a fixed-target `lift` field.
-/
structure W269WalkingParallelPairLiftBlueprint (L : C ⥤ D) where
  objDiagram : ∀ (Y : WalkingParallelPair ⥤ D), WalkingParallelPair ⥤ C
  comparisonIso : ∀ (Y : WalkingParallelPair ⥤ D),
    (W269WhiskeringRightObjectwiseFunctor WalkingParallelPair L).obj (objDiagram Y) ≅ Y
  mapDiagram : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    objDiagram Y ⟶ objDiagram Z
  map_id : ∀ (Y : WalkingParallelPair ⥤ D),
    mapDiagram (𝟙 Y) = 𝟙 (objDiagram Y)
  map_comp : ∀ {Y Z T : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z) (σ : Z ⟶ T),
    mapDiagram (τ ≫ σ) = mapDiagram τ ≫ mapDiagram σ

namespace W269WalkingParallelPairLiftBlueprint

variable {L : C ⥤ D}
variable {E : Type u} [Category E]

/-- A checked `lift` functor from coherent strict representatives. -/
def liftFunctor (B : W269WalkingParallelPairLiftBlueprint L)
    (F : (WalkingParallelPair ⥤ C) ⥤ E) :
    (WalkingParallelPair ⥤ D) ⥤ E where
  obj Y := F.obj (B.objDiagram Y)
  map {Y Z} τ := F.map (B.mapDiagram τ)
  map_id Y := by
    rw [B.map_id Y]
    exact F.map_id _
  map_comp τ σ := by
    rw [B.map_comp τ σ]
    exact F.map_comp _ _

end W269WalkingParallelPairLiftBlueprint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFunctorCategoryLocalizationW269

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- The opposite bounded weak-equivalence localizer. -/
abbrev oppositeWeakEquivalence : MorphismProperty (BoundedComplexCategory C)ᵒᵖ :=
  (boundedExactWeakEquivalence C).op

/-- The opposite objectwise functor for `WalkingParallelPair` diagrams. -/
abbrev OppositeWalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ (BoundedComplexCategory C)ᵒᵖ) ⥤
      (WalkingParallelPair ⥤ (oppositeWeakEquivalence C).Localization) :=
  CategoryTheory.Localization.W269WhiskeringRightObjectwiseFunctor WalkingParallelPair
    ((oppositeWeakEquivalence C).Q)

/-- The formal `inverts` field for the opposite objectwise functor. -/
theorem oppositeWalkingParallelPairObjectwise_inverts :
    ((oppositeWeakEquivalence C).functorCategory WalkingParallelPair).IsInvertedBy
      (OppositeWalkingParallelPairObjectwiseFunctor C) :=
  CategoryTheory.Localization.w269WhiskeringRightObjectwise_inverts
    (J := WalkingParallelPair) ((oppositeWeakEquivalence C).Q) (oppositeWeakEquivalence C)

/-- First fixed target: diagrams in the abstract opposite localization. -/
abbrev OppositeDiagramFixedTarget : Type _ :=
  WalkingParallelPair ⥤ (oppositeWeakEquivalence C).Localization

/-- Second fixed target: the canonical localization model for source parallel-pair diagrams. -/
abbrev OppositeModelFixedTarget : Type _ :=
  ((oppositeWeakEquivalence C).functorCategory WalkingParallelPair).Localization

/-- Remaining fixed-target fields for the opposite objectwise localization problem. -/
abbrev OppositeRemainingFixedTargetData (E : Type*) [Category E] : Type _ :=
  CategoryTheory.Localization.W269WhiskeringRightRemainingFixedTargetData
    (J := WalkingParallelPair) ((oppositeWeakEquivalence C).Q)
    (oppositeWeakEquivalence C) E

/-- The exact two target categories whose `lift`, `fac`, and `uniq` fields remain. -/
structure OppositeWalkingParallelPairTwoTargetBoundary : Type _ where
  target : OppositeRemainingFixedTargetData C (OppositeDiagramFixedTarget C)
  model : OppositeRemainingFixedTargetData C (OppositeModelFixedTarget C)

/--
The checked consumer for the two opposite fixed-target packages. Supplying this boundary
proves the W224/W220 functor-category localization input.
-/
theorem oppositeFunctorCategoryLocalization_of_twoTargetBoundary
    (h : OppositeWalkingParallelPairTwoTargetBoundary C) :
    (OppositeWalkingParallelPairObjectwiseFunctor C).IsLocalization
      ((oppositeWeakEquivalence C).functorCategory WalkingParallelPair) :=
  CategoryTheory.Localization.w269WhiskeringRight_isLocalization_of_twoFixedTargetBoundary
    (J := WalkingParallelPair) ((oppositeWeakEquivalence C).Q)
    (oppositeWeakEquivalence C)
    { target := h.target, model := h.model }

/-- Coherent strict-preimage data sufficient to build the opposite abstract `lift` field. -/
abbrev OppositeWalkingParallelPairLiftBlueprint : Type _ :=
  CategoryTheory.Localization.W269WalkingParallelPairLiftBlueprint
    ((oppositeWeakEquivalence C).Q)

/-- A checked candidate `lift` field for arbitrary fixed target `E`. -/
abbrev oppositeCandidateLiftFromBlueprint
    (B : OppositeWalkingParallelPairLiftBlueprint C)
    (E : Type u) [Category E] :
    ((WalkingParallelPair ⥤ (BoundedComplexCategory C)ᵒᵖ) ⥤ E) →
      (WalkingParallelPair ⥤ (oppositeWeakEquivalence C).Localization) ⥤ E :=
  fun F => B.liftFunctor F

/-- Machine-readable W269 frontier state. -/
structure OppositeFunctorCategoryLocalizationState : Type where
  seedHash : String
  provedFields : List String
  theoremBoundary : String
  fixedTargetCategories : List String
  conditionalLiftConstructor : String
  remainingFields : List String
  productSuccessClaimed : Bool

/-- Reproducible W269 state. -/
def currentOppositeFunctorCategoryLocalizationState :
    OppositeFunctorCategoryLocalizationState where
  seedHash := "a595e2697cf5572d2ea0c45873410abed8cc12dddded00dd8eaf674b9bebfe95"
  provedFields := ["oppositeWalkingParallelPairObjectwise_inverts"]
  theoremBoundary := "oppositeFunctorCategoryLocalization_of_twoTargetBoundary"
  fixedTargetCategories :=
    ["WalkingParallelPair ⥤ ((boundedExactWeakEquivalence C).op).Localization",
      "(((boundedExactWeakEquivalence C).op).functorCategory WalkingParallelPair).Localization"]
  conditionalLiftConstructor := "oppositeCandidateLiftFromBlueprint"
  remainingFields := ["fac", "uniq", "existence of coherent opposite lift blueprints"]
  productSuccessClaimed := false

theorem currentOppositeFunctorCategoryLocalizationState_productSuccess :
    currentOppositeFunctorCategoryLocalizationState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W269. -/
def oppositeFunctorCategoryLocalizationDeclarationNames : List String :=
  ["CategoryTheory.Localization.W269WhiskeringRightObjectwiseFunctor",
    "CategoryTheory.Localization.w269WhiskeringRightObjectwise_inverts",
    "CategoryTheory.Localization.W269WhiskeringRightFixedTargetFields",
    "CategoryTheory.Localization.W269WhiskeringRightRemainingFixedTargetData",
    "CategoryTheory.Localization.W269TwoFixedTargetBoundary",
    "CategoryTheory.Localization.w269WhiskeringRight_isLocalization_of_twoFixedTargetBoundary",
    "CategoryTheory.Localization.W269WalkingParallelPairLiftBlueprint",
    "CategoryTheory.Localization.W269WalkingParallelPairLiftBlueprint.liftFunctor",
    "oppositeWalkingParallelPairObjectwise_inverts",
    "OppositeWalkingParallelPairTwoTargetBoundary",
    "oppositeFunctorCategoryLocalization_of_twoTargetBoundary",
    "oppositeCandidateLiftFromBlueprint",
    "currentOppositeFunctorCategoryLocalizationState"]

theorem oppositeFunctorCategoryLocalizationDeclarationNames_count :
    oppositeFunctorCategoryLocalizationDeclarationNames.length = 13 := rfl

section Checks

#check CategoryTheory.Localization.W269WhiskeringRightObjectwiseFunctor
#check CategoryTheory.Localization.w269WhiskeringRightObjectwise_inverts
#check CategoryTheory.Localization.W269WhiskeringRightFixedTargetFields
#check CategoryTheory.Localization.W269WhiskeringRightFixedTargetFields.toStrictUniversalProperty
#check CategoryTheory.Localization.W269WhiskeringRightRemainingFixedTargetData
#check CategoryTheory.Localization.W269WhiskeringRightRemainingFixedTargetData.toFixedTargetFields
#check CategoryTheory.Localization.W269TwoFixedTargetBoundary
#check CategoryTheory.Localization.w269WhiskeringRight_isLocalization_of_twoFixedTargetBoundary
#check CategoryTheory.Localization.W269WalkingParallelPairLiftBlueprint
#check CategoryTheory.Localization.W269WalkingParallelPairLiftBlueprint.liftFunctor
#check oppositeWeakEquivalence
#check OppositeWalkingParallelPairObjectwiseFunctor
#check oppositeWalkingParallelPairObjectwise_inverts
#check OppositeDiagramFixedTarget
#check OppositeModelFixedTarget
#check OppositeRemainingFixedTargetData
#check OppositeWalkingParallelPairTwoTargetBoundary
#check oppositeFunctorCategoryLocalization_of_twoTargetBoundary
#check OppositeWalkingParallelPairLiftBlueprint
#check oppositeCandidateLiftFromBlueprint
#check OppositeFunctorCategoryLocalizationState
#check currentOppositeFunctorCategoryLocalizationState
#check currentOppositeFunctorCategoryLocalizationState_productSuccess
#check oppositeFunctorCategoryLocalizationDeclarationNames
#check oppositeFunctorCategoryLocalizationDeclarationNames_count

end Checks

end OppositeFunctorCategoryLocalizationW269

end LeanLCAExactChallenge
