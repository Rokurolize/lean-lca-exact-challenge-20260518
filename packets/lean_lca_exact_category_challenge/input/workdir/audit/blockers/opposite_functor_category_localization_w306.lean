import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W306: uniform fixed-target obligations for opposite `WalkingParallelPair`.

W269/W272/W274 reduced the opposite functor-category localization input to a
coherent strict-representative blueprint plus separate `fac`/`uniq` obligations
for the diagram target and the localization-model target.  This file sharpens that
handoff by replacing the four target-specific obligations with two uniform schemas,
quantified over all fixed targets.  The checked consumer specializes those schemas
to the two targets required by `Functor.IsLocalization.mk'`.

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

/-- W306-local spelling of objectwise postcomposition by a localization functor. -/
abbrev W306ObjectwiseFunctor (J : Type w) [Category.{v} J] (L : C ⥤ D) :
    (J ⥤ C) ⥤ (J ⥤ D) :=
  (whiskeringRight J C D).obj L

/-- Objectwise postcomposition inverts objectwise weak equivalences. -/
lemma w306Objectwise_inverts (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] :
    (W.functorCategory J).IsInvertedBy (W306ObjectwiseFunctor J L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso (((W306ObjectwiseFunctor J L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/-- Fixed-target data after the formal inversion field has been supplied. -/
structure W306FixedTargetFacUniqBoundary (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (E : Type*) [Category E] where
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      W306ObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      W306ObjectwiseFunctor J L ⋙ F₁ =
        W306ObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace W306FixedTargetFacUniqBoundary

variable {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
variable {E : Type*} [Category E]

/-- Convert explicit `lift`/`fac`/`uniq` data to mathlib's fixed-target API. -/
def toStrictUniversalProperty
    (h : W306FixedTargetFacUniqBoundary (J := J) L W E) :
    StrictUniversalPropertyFixedTarget (W306ObjectwiseFunctor J L)
      (W.functorCategory J) E where
  inverts := w306Objectwise_inverts (J := J) L W
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end W306FixedTargetFacUniqBoundary

/-- The two fixed targets required by `Functor.IsLocalization.mk'`. -/
structure W306TwoFixedTargetFacUniqBoundary (J : Type w) [Category.{v} J]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] where
  target :
    W306FixedTargetFacUniqBoundary (J := J) L W (J ⥤ D)
  model :
    W306FixedTargetFacUniqBoundary (J := J) L W
      ((W.functorCategory J).Localization)

/-- Checked consumer: two fixed-target packages prove objectwise localization. -/
lemma w306Objectwise_isLocalization_of_facUniqBoundary
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (h : W306TwoFixedTargetFacUniqBoundary J L W) :
    (W306ObjectwiseFunctor J L).IsLocalization (W.functorCategory J) :=
  Functor.IsLocalization.mk'
    (L := W306ObjectwiseFunctor J L) (W := W.functorCategory J)
    h.target.toStrictUniversalProperty
    h.model.toStrictUniversalProperty

/-- Coherent strict representatives for target parallel-pair diagrams. -/
structure W306WalkingParallelPairLiftBlueprint (L : C ⥤ D) where
  objDiagram : ∀ (Y : WalkingParallelPair ⥤ D), WalkingParallelPair ⥤ C
  comparisonIso : ∀ (Y : WalkingParallelPair ⥤ D),
    (W306ObjectwiseFunctor WalkingParallelPair L).obj (objDiagram Y) ≅ Y
  mapDiagram : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    objDiagram Y ⟶ objDiagram Z
  map_id : ∀ (Y : WalkingParallelPair ⥤ D),
    mapDiagram (𝟙 Y) = 𝟙 (objDiagram Y)
  map_comp : ∀ {Y Z T : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z) (σ : Z ⟶ T),
    mapDiagram (τ ≫ σ) = mapDiagram τ ≫ mapDiagram σ

namespace W306WalkingParallelPairLiftBlueprint

variable {L : C ⥤ D}
variable {E : Type u} [Category E]

/-- The checked candidate `lift` produced by a coherent strict representative blueprint. -/
def liftFunctor (B : W306WalkingParallelPairLiftBlueprint L)
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

end W306WalkingParallelPairLiftBlueprint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFunctorCategoryLocalizationW306

/-- The opposite bounded weak-equivalence localizer for `MetrizableLCA`. -/
abbrev metrizableLCAOppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).op

/-- The objectwise opposite `WalkingParallelPair` functor whose localization remains blocked. -/
abbrev MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) :=
  CategoryTheory.Localization.W306ObjectwiseFunctor WalkingParallelPair
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
  CategoryTheory.Localization.W306FixedTargetFacUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence E

/-- The two fixed-target packages whose `fac` and `uniq` fields are still missing. -/
abbrev OppositeTwoFixedTargetBoundary : Type _ :=
  CategoryTheory.Localization.W306TwoFixedTargetFacUniqBoundary WalkingParallelPair
    (metrizableLCAOppositeWeakEquivalence.Q) metrizableLCAOppositeWeakEquivalence

/-- Checked consumer for the MetrizableLCA opposite fixed-target boundary. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
    (h : OppositeTwoFixedTargetBoundary) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  CategoryTheory.Localization.w306Objectwise_isLocalization_of_facUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence h

/-- Coherent opposite strict representatives sufficient to define the candidate `lift`. -/
abbrev OppositeWalkingParallelPairLiftBlueprint : Type _ :=
  CategoryTheory.Localization.W306WalkingParallelPairLiftBlueprint
    (metrizableLCAOppositeWeakEquivalence.Q)

/-- A checked candidate `lift` field for any fixed target, assuming a coherent blueprint. -/
def oppositeLiftFieldFromBlueprint
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (E : Type u) [Category E] :
    ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤ E),
      (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F →
        (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤ E :=
  fun F _ => B.liftFunctor F

/-- Uniform fixed-target `fac` schema for the blueprint-produced lift. -/
abbrev OppositeUniformFixedTargetFacObligation
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop :=
  ∀ (E : Type 1) [Category.{1} E]
    (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤ E)
    (hF : (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F),
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙
          oppositeLiftFieldFromBlueprint B E F hF = F

/-- Uniform fixed-target `uniq` schema for objectwise opposite postcomposition. -/
abbrev OppositeUniformFixedTargetUniqObligation : Prop :=
  ∀ (E : Type 1) [Category.{1} E]
    (F₁ F₂ :
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤ E),
    MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₁ =
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₂ →
    F₁ = F₂

/--
Uniform handoff: one `fac` schema and one `uniq` schema, quantified over the fixed
target universe used by the W274 diagram and model targets, specialize to the two
targets required by `Functor.IsLocalization.mk'`.
-/
structure OppositeUniformFixedTargetObligationBoundary
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop where
  fac : OppositeUniformFixedTargetFacObligation B
  uniq : OppositeUniformFixedTargetUniqObligation

namespace OppositeUniformFixedTargetObligationBoundary

variable {B : OppositeWalkingParallelPairLiftBlueprint}

/-- Specialize the uniform obligations to the two fixed targets. -/
def toFixedTargetBoundary
    (h : OppositeUniformFixedTargetObligationBoundary B) :
    OppositeTwoFixedTargetBoundary where
  target :=
    { lift := oppositeLiftFieldFromBlueprint B OppositeDiagramFixedTarget
      fac := h.fac OppositeDiagramFixedTarget
      uniq := h.uniq OppositeDiagramFixedTarget }
  model :=
    { lift := oppositeLiftFieldFromBlueprint B OppositeModelFixedTarget
      fac := h.fac OppositeModelFixedTarget
      uniq := h.uniq OppositeModelFixedTarget }

end OppositeUniformFixedTargetObligationBoundary

/-- Checked consumer for the uniform fixed-target obligation boundary. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_obligations
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (h : OppositeUniformFixedTargetObligationBoundary B) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
    h.toFixedTargetBoundary

/-- Direct constructor from the two uniform schemas. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_fac_uniq
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (hFac : OppositeUniformFixedTargetFacObligation B)
    (hUniq : OppositeUniformFixedTargetUniqObligation) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_obligations B
    { fac := hFac
      uniq := hUniq }

/-- Machine-readable frontier state for W306. -/
structure OppositeUniformFixedTargetObligationState : Type where
  seedHash : String
  route : String
  constructedField : String
  uniformObligations : List String
  specializedTargets : List String
  theoremBoundary : String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

/-- Reproducible W306 state. -/
def currentOppositeUniformFixedTargetObligationState :
    OppositeUniformFixedTargetObligationState where
  seedHash := "8f8fe8fbde2955ac95119ce7a98c87ca93d8471e19cedd1aa0e830f3d005b3a4"
  route := "uniform fixed-target obligation schema for W269/W272/W274 opposite WalkingParallelPair"
  constructedField := "oppositeLiftFieldFromBlueprint"
  uniformObligations :=
    ["OppositeUniformFixedTargetFacObligation",
      "OppositeUniformFixedTargetUniqObligation"]
  specializedTargets :=
    ["OppositeDiagramFixedTarget",
      "OppositeModelFixedTarget"]
  theoremBoundary :=
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_obligations"
  remainingInputs :=
    ["OppositeWalkingParallelPairLiftBlueprint",
      "real fac fields for the two fixed targets",
      "real uniq fields for the two fixed targets",
      "or a nontrivial universe-polymorphic uniform fac/uniq theorem"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentOppositeUniformFixedTargetObligationState_subgoalSuccess :
    currentOppositeUniformFixedTargetObligationState.subgoalSuccessClaimed = true := rfl

theorem currentOppositeUniformFixedTargetObligationState_productSuccess :
    currentOppositeUniformFixedTargetObligationState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W306. -/
def oppositeUniformFixedTargetObligationDeclarationNames : List String :=
  ["CategoryTheory.Localization.W306ObjectwiseFunctor",
    "CategoryTheory.Localization.w306Objectwise_inverts",
    "CategoryTheory.Localization.W306FixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.W306FixedTargetFacUniqBoundary.toStrictUniversalProperty",
    "CategoryTheory.Localization.W306TwoFixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.w306Objectwise_isLocalization_of_facUniqBoundary",
    "CategoryTheory.Localization.W306WalkingParallelPairLiftBlueprint",
    "CategoryTheory.Localization.W306WalkingParallelPairLiftBlueprint.liftFunctor",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "OppositeWalkingParallelPairLiftBlueprint",
    "oppositeLiftFieldFromBlueprint",
    "OppositeUniformFixedTargetFacObligation",
    "OppositeUniformFixedTargetUniqObligation",
    "OppositeUniformFixedTargetObligationBoundary",
    "OppositeUniformFixedTargetObligationBoundary.toFixedTargetBoundary",
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_obligations",
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_fac_uniq",
    "currentOppositeUniformFixedTargetObligationState"]

theorem oppositeUniformFixedTargetObligationDeclarationNames_count :
    oppositeUniformFixedTargetObligationDeclarationNames.length = 18 := rfl

section Checks

#check CategoryTheory.Localization.W306ObjectwiseFunctor
#check CategoryTheory.Localization.w306Objectwise_inverts
#check CategoryTheory.Localization.W306FixedTargetFacUniqBoundary
#check CategoryTheory.Localization.W306FixedTargetFacUniqBoundary.toStrictUniversalProperty
#check CategoryTheory.Localization.W306TwoFixedTargetFacUniqBoundary
#check CategoryTheory.Localization.w306Objectwise_isLocalization_of_facUniqBoundary
#check CategoryTheory.Localization.W306WalkingParallelPairLiftBlueprint
#check CategoryTheory.Localization.W306WalkingParallelPairLiftBlueprint.liftFunctor
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
#check OppositeUniformFixedTargetFacObligation
#check OppositeUniformFixedTargetUniqObligation
#check OppositeUniformFixedTargetObligationBoundary
#check OppositeUniformFixedTargetObligationBoundary.toFixedTargetBoundary
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_obligations
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_uniform_fac_uniq
#check currentOppositeUniformFixedTargetObligationState
#check currentOppositeUniformFixedTargetObligationState_subgoalSuccess
#check currentOppositeUniformFixedTargetObligationState_productSuccess
#check oppositeUniformFixedTargetObligationDeclarationNames
#check oppositeUniformFixedTargetObligationDeclarationNames_count

end Checks

end OppositeFunctorCategoryLocalizationW306

end LeanLCAExactChallenge
