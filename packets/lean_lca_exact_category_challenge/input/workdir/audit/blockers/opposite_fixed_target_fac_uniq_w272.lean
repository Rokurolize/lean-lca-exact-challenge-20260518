import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W272: opposite fixed-target `fac`/`uniq` boundary.

W269 specialized objectwise `WalkingParallelPair` localization to the opposite
bounded weak-equivalence localizer. This file narrows the remaining handoff to the
two fixed targets used by `Functor.IsLocalization.mk'`: each target needs a `lift`
plus the corresponding `fac` and `uniq` equalities. It also records the coherent
strict representative data that supplies the candidate `lift` field.

No product completion is claimed here.
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

/-- W272-local spelling of objectwise postcomposition by a localization functor. -/
abbrev W272ObjectwiseFunctor (J : Type w) [Category.{v} J] (L : C ⥤ D) :
    (J ⥤ C) ⥤ (J ⥤ D) :=
  (whiskeringRight J C D).obj L

/-- Objectwise postcomposition inverts objectwise weak equivalences. -/
lemma w272Objectwise_inverts (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] :
    (W.functorCategory J).IsInvertedBy (W272ObjectwiseFunctor J L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso (((W272ObjectwiseFunctor J L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/-- The post-inversion fixed-target data that remains after the formal objectwise
inversion field is supplied. -/
structure W272FixedTargetFacUniqBoundary (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (E : Type*) [Category E] where
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      W272ObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      W272ObjectwiseFunctor J L ⋙ F₁ =
        W272ObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace W272FixedTargetFacUniqBoundary

variable {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
variable {E : Type*} [Category E]

/-- Convert the explicit `lift`/`fac`/`uniq` boundary to mathlib's fixed-target API. -/
def toStrictUniversalProperty
    (h : W272FixedTargetFacUniqBoundary (J := J) L W E) :
    StrictUniversalPropertyFixedTarget (W272ObjectwiseFunctor J L)
      (W.functorCategory J) E where
  inverts := w272Objectwise_inverts (J := J) L W
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end W272FixedTargetFacUniqBoundary

/-- The two fixed targets required by `Functor.IsLocalization.mk'`. -/
structure W272TwoFixedTargetFacUniqBoundary (J : Type w) [Category.{v} J]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] where
  target :
    W272FixedTargetFacUniqBoundary (J := J) L W (J ⥤ D)
  model :
    W272FixedTargetFacUniqBoundary (J := J) L W
      ((W.functorCategory J).Localization)

/-- Checked consumer: the two explicit fixed-target packages prove objectwise localization. -/
lemma w272Objectwise_isLocalization_of_facUniqBoundary
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (h : W272TwoFixedTargetFacUniqBoundary J L W) :
    (W272ObjectwiseFunctor J L).IsLocalization (W.functorCategory J) :=
  Functor.IsLocalization.mk'
    (L := W272ObjectwiseFunctor J L) (W := W.functorCategory J)
    h.target.toStrictUniversalProperty
    h.model.toStrictUniversalProperty

/-- Coherent strict representatives for target parallel-pair diagrams. This is exactly
the data needed to define a candidate fixed-target `lift` for any codomain `E`. -/
structure W272WalkingParallelPairLiftBlueprint (L : C ⥤ D) where
  objDiagram : ∀ (Y : WalkingParallelPair ⥤ D), WalkingParallelPair ⥤ C
  comparisonIso : ∀ (Y : WalkingParallelPair ⥤ D),
    (W272ObjectwiseFunctor WalkingParallelPair L).obj (objDiagram Y) ≅ Y
  mapDiagram : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    objDiagram Y ⟶ objDiagram Z
  map_id : ∀ (Y : WalkingParallelPair ⥤ D),
    mapDiagram (𝟙 Y) = 𝟙 (objDiagram Y)
  map_comp : ∀ {Y Z T : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z) (σ : Z ⟶ T),
    mapDiagram (τ ≫ σ) = mapDiagram τ ≫ mapDiagram σ

namespace W272WalkingParallelPairLiftBlueprint

variable {L : C ⥤ D}
variable {E : Type u} [Category E]

/-- The checked candidate `lift` produced by a coherent strict representative blueprint. -/
def liftFunctor (B : W272WalkingParallelPairLiftBlueprint L)
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

end W272WalkingParallelPairLiftBlueprint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFixedTargetFacUniqW272

/-- The opposite bounded weak-equivalence localizer for `MetrizableLCA`. -/
abbrev metrizableLCAOppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).op

/-- The objectwise opposite `WalkingParallelPair` functor whose localization remains blocked. -/
abbrev MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) :=
  CategoryTheory.Localization.W272ObjectwiseFunctor WalkingParallelPair
    (metrizableLCAOppositeWeakEquivalence.Q)

/-- The exact W252/W266 functor-category localization input. -/
abbrev MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  (MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor).IsLocalization
    (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair)

/-- First fixed target: opposite-localized parallel-pair diagrams. -/
abbrev OppositeDiagramFixedTarget : Type _ :=
  WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization

/-- Second fixed target: the canonical localization of source parallel-pair diagrams. -/
abbrev OppositeModelFixedTarget : Type _ :=
  (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).Localization

/-- Remaining fixed-target package for a chosen codomain `E`. -/
abbrev OppositeFixedTargetBoundary (E : Type*) [Category E] : Type _ :=
  CategoryTheory.Localization.W272FixedTargetFacUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence E

/-- The two fixed-target packages whose `fac` and `uniq` fields are still missing. -/
abbrev OppositeTwoFixedTargetBoundary : Type _ :=
  CategoryTheory.Localization.W272TwoFixedTargetFacUniqBoundary WalkingParallelPair
    (metrizableLCAOppositeWeakEquivalence.Q) metrizableLCAOppositeWeakEquivalence

/-- Checked consumer for the MetrizableLCA opposite fixed-target boundary. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
    (h : OppositeTwoFixedTargetBoundary) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  CategoryTheory.Localization.w272Objectwise_isLocalization_of_facUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence h

/-- Coherent opposite strict representatives sufficient to define the candidate `lift`. -/
abbrev OppositeWalkingParallelPairLiftBlueprint : Type _ :=
  CategoryTheory.Localization.W272WalkingParallelPairLiftBlueprint
    (metrizableLCAOppositeWeakEquivalence.Q)

/-- A checked candidate `lift` field for any fixed target, assuming a coherent blueprint. -/
def oppositeLiftFieldFromBlueprint
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (E : Type u) [Category E] :
    ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤ E),
      (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F →
        (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤ E :=
  fun F _ => B.liftFunctor F

/-- The explicit `fac` obligation for the diagram fixed target. -/
abbrev OppositeDiagramFixedTargetFacObligation
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop :=
  ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤
        OppositeDiagramFixedTarget)
    (hF : (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F),
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙
          oppositeLiftFieldFromBlueprint B OppositeDiagramFixedTarget F hF = F

/-- The explicit `uniq` obligation for the diagram fixed target. -/
abbrev OppositeDiagramFixedTargetUniqObligation : Prop :=
  ∀ (F₁ F₂ :
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤
        OppositeDiagramFixedTarget),
    MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₁ =
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₂ →
    F₁ = F₂

/-- The explicit `fac` obligation for the model fixed target. -/
abbrev OppositeModelFixedTargetFacObligation
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop :=
  ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤
        OppositeModelFixedTarget)
    (hF : (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F),
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙
          oppositeLiftFieldFromBlueprint B OppositeModelFixedTarget F hF = F

/-- The explicit `uniq` obligation for the model fixed target. -/
abbrev OppositeModelFixedTargetUniqObligation : Prop :=
  ∀ (F₁ F₂ :
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤
        OppositeModelFixedTarget),
    MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₁ =
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₂ →
    F₁ = F₂

/-- Smallest checked handoff around the candidate blueprint: once the four named
`fac`/`uniq` obligations are supplied, the opposite functor-category localization
input follows. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (hTargetFac : OppositeDiagramFixedTargetFacObligation B)
    (hTargetUniq : OppositeDiagramFixedTargetUniqObligation)
    (hModelFac : OppositeModelFixedTargetFacObligation B)
    (hModelUniq : OppositeModelFixedTargetUniqObligation) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput := by
  refine metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary ?_
  refine
    { target :=
        { lift := oppositeLiftFieldFromBlueprint B OppositeDiagramFixedTarget
          fac := hTargetFac
          uniq := hTargetUniq }
      model :=
        { lift := oppositeLiftFieldFromBlueprint B OppositeModelFixedTarget
          fac := hModelFac
          uniq := hModelUniq } }

/-- Machine-readable frontier state for W272. -/
structure OppositeFixedTargetFacUniqState : Type where
  seedHash : String
  route : String
  constructedField : String
  theoremBoundary : String
  fixedTargetCategories : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W272 state. -/
def currentOppositeFixedTargetFacUniqState :
    OppositeFixedTargetFacUniqState where
  seedHash := "079fb57d654d6dfaacb87f77315b7e7f4e4fa4d6c08945e4363dafd1f1109542"
  route := "opposite fixed-target fac/uniq boundary with blueprint-supplied lift"
  constructedField := "oppositeLiftFieldFromBlueprint"
  theoremBoundary :=
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq"
  fixedTargetCategories :=
    ["WalkingParallelPair ⥤ ((boundedExactWeakEquivalence MetrizableLCA).op).Localization",
      "(((boundedExactWeakEquivalence MetrizableLCA).op).functorCategory WalkingParallelPair).Localization"]
  remainingInputs :=
    ["OppositeWalkingParallelPairLiftBlueprint",
      "OppositeDiagramFixedTargetFacObligation",
      "OppositeDiagramFixedTargetUniqObligation",
      "OppositeModelFixedTargetFacObligation",
      "OppositeModelFixedTargetUniqObligation"]
  productSuccessClaimed := false

theorem currentOppositeFixedTargetFacUniqState_productSuccess :
    currentOppositeFixedTargetFacUniqState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W272. -/
def oppositeFixedTargetFacUniqDeclarationNames : List String :=
  ["CategoryTheory.Localization.W272ObjectwiseFunctor",
    "CategoryTheory.Localization.w272Objectwise_inverts",
    "CategoryTheory.Localization.W272FixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.W272FixedTargetFacUniqBoundary.toStrictUniversalProperty",
    "CategoryTheory.Localization.W272TwoFixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.w272Objectwise_isLocalization_of_facUniqBoundary",
    "CategoryTheory.Localization.W272WalkingParallelPairLiftBlueprint",
    "CategoryTheory.Localization.W272WalkingParallelPairLiftBlueprint.liftFunctor",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "OppositeWalkingParallelPairLiftBlueprint",
    "oppositeLiftFieldFromBlueprint",
    "OppositeDiagramFixedTargetFacObligation",
    "OppositeDiagramFixedTargetUniqObligation",
    "OppositeModelFixedTargetFacObligation",
    "OppositeModelFixedTargetUniqObligation",
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq",
    "currentOppositeFixedTargetFacUniqState"]

theorem oppositeFixedTargetFacUniqDeclarationNames_count :
    oppositeFixedTargetFacUniqDeclarationNames.length = 17 := rfl

section Checks

#check CategoryTheory.Localization.W272ObjectwiseFunctor
#check CategoryTheory.Localization.w272Objectwise_inverts
#check CategoryTheory.Localization.W272FixedTargetFacUniqBoundary
#check CategoryTheory.Localization.W272FixedTargetFacUniqBoundary.toStrictUniversalProperty
#check CategoryTheory.Localization.W272TwoFixedTargetFacUniqBoundary
#check CategoryTheory.Localization.w272Objectwise_isLocalization_of_facUniqBoundary
#check CategoryTheory.Localization.W272WalkingParallelPairLiftBlueprint
#check CategoryTheory.Localization.W272WalkingParallelPairLiftBlueprint.liftFunctor
#check metrizableLCAOppositeWeakEquivalence
#check MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor
#check MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput
#check OppositeDiagramFixedTarget
#check OppositeModelFixedTarget
#check OppositeFixedTargetBoundary
#check OppositeTwoFixedTargetBoundary
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
#check OppositeWalkingParallelPairLiftBlueprint
#check oppositeLiftFieldFromBlueprint
#check OppositeDiagramFixedTargetFacObligation
#check OppositeDiagramFixedTargetUniqObligation
#check OppositeModelFixedTargetFacObligation
#check OppositeModelFixedTargetUniqObligation
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq
#check currentOppositeFixedTargetFacUniqState
#check currentOppositeFixedTargetFacUniqState_productSuccess
#check oppositeFixedTargetFacUniqDeclarationNames
#check oppositeFixedTargetFacUniqDeclarationNames_count

end Checks

end OppositeFixedTargetFacUniqW272

end LeanLCAExactChallenge
