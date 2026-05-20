import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W274: opposite fixed-target obligations for `WalkingParallelPair`.

This file sharpens the W272 fixed-target boundary.  The remaining target-specific
fields are expressed as two reusable schemas, specialized to the diagram target and
to the model target used by `Functor.IsLocalization.mk'`.

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

/-- W274-local spelling of objectwise postcomposition by a localization functor. -/
abbrev W274ObjectwiseFunctor (J : Type w) [Category.{v} J] (L : C ⥤ D) :
    (J ⥤ C) ⥤ (J ⥤ D) :=
  (whiskeringRight J C D).obj L

/-- Objectwise postcomposition inverts objectwise weak equivalences. -/
lemma w274Objectwise_inverts (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] :
    (W.functorCategory J).IsInvertedBy (W274ObjectwiseFunctor J L) :=
  fun _ _ f hf => by
    haveI : ∀ j : J, IsIso (((W274ObjectwiseFunctor J L).map f).app j) := by
      intro j
      exact Localization.inverts L W (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/--
The post-inversion fixed-target data that remains after the formal objectwise
inversion field is supplied.
-/
structure W274FixedTargetFacUniqBoundary (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] (E : Type*) [Category E] where
  lift :
    ∀ (F : (J ⥤ C) ⥤ E), (W.functorCategory J).IsInvertedBy F → (J ⥤ D) ⥤ E
  fac :
    ∀ (F : (J ⥤ C) ⥤ E) (hF : (W.functorCategory J).IsInvertedBy F),
      W274ObjectwiseFunctor J L ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (J ⥤ D) ⥤ E),
      W274ObjectwiseFunctor J L ⋙ F₁ =
        W274ObjectwiseFunctor J L ⋙ F₂ →
      F₁ = F₂

namespace W274FixedTargetFacUniqBoundary

variable {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
variable {E : Type*} [Category E]

/-- Convert the explicit `lift`/`fac`/`uniq` boundary to mathlib's fixed-target API. -/
def toStrictUniversalProperty
    (h : W274FixedTargetFacUniqBoundary (J := J) L W E) :
    StrictUniversalPropertyFixedTarget (W274ObjectwiseFunctor J L)
      (W.functorCategory J) E where
  inverts := w274Objectwise_inverts (J := J) L W
  lift := h.lift
  fac := h.fac
  uniq := h.uniq

end W274FixedTargetFacUniqBoundary

/-- The two fixed targets required by `Functor.IsLocalization.mk'`. -/
structure W274TwoFixedTargetFacUniqBoundary (J : Type w) [Category.{v} J]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] where
  target :
    W274FixedTargetFacUniqBoundary (J := J) L W (J ⥤ D)
  model :
    W274FixedTargetFacUniqBoundary (J := J) L W
      ((W.functorCategory J).Localization)

/-- Checked consumer: the two explicit fixed-target packages prove objectwise localization. -/
lemma w274Objectwise_isLocalization_of_facUniqBoundary
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (h : W274TwoFixedTargetFacUniqBoundary J L W) :
    (W274ObjectwiseFunctor J L).IsLocalization (W.functorCategory J) :=
  Functor.IsLocalization.mk'
    (L := W274ObjectwiseFunctor J L) (W := W.functorCategory J)
    h.target.toStrictUniversalProperty
    h.model.toStrictUniversalProperty

/--
Coherent strict representatives for target parallel-pair diagrams.  This is exactly
the data needed to define a candidate fixed-target `lift` for any codomain `E`.
-/
structure W274WalkingParallelPairLiftBlueprint (L : C ⥤ D) where
  objDiagram : ∀ (Y : WalkingParallelPair ⥤ D), WalkingParallelPair ⥤ C
  comparisonIso : ∀ (Y : WalkingParallelPair ⥤ D),
    (W274ObjectwiseFunctor WalkingParallelPair L).obj (objDiagram Y) ≅ Y
  mapDiagram : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    objDiagram Y ⟶ objDiagram Z
  map_id : ∀ (Y : WalkingParallelPair ⥤ D),
    mapDiagram (𝟙 Y) = 𝟙 (objDiagram Y)
  map_comp : ∀ {Y Z T : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z) (σ : Z ⟶ T),
    mapDiagram (τ ≫ σ) = mapDiagram τ ≫ mapDiagram σ

namespace W274WalkingParallelPairLiftBlueprint

variable {L : C ⥤ D}
variable {E : Type u} [Category E]

/-- The checked candidate `lift` produced by a coherent strict representative blueprint. -/
def liftFunctor (B : W274WalkingParallelPairLiftBlueprint L)
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

end W274WalkingParallelPairLiftBlueprint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFixedTargetObligationsW274

/-- The opposite bounded weak-equivalence localizer for `MetrizableLCA`. -/
abbrev metrizableLCAOppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).op

/-- The objectwise opposite `WalkingParallelPair` functor whose localization remains blocked. -/
abbrev MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) :=
  CategoryTheory.Localization.W274ObjectwiseFunctor WalkingParallelPair
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
  CategoryTheory.Localization.W274FixedTargetFacUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence E

/-- The two fixed-target packages whose `fac` and `uniq` fields are still missing. -/
abbrev OppositeTwoFixedTargetBoundary : Type _ :=
  CategoryTheory.Localization.W274TwoFixedTargetFacUniqBoundary WalkingParallelPair
    (metrizableLCAOppositeWeakEquivalence.Q) metrizableLCAOppositeWeakEquivalence

/-- Checked consumer for the MetrizableLCA opposite fixed-target boundary. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
    (h : OppositeTwoFixedTargetBoundary) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  CategoryTheory.Localization.w274Objectwise_isLocalization_of_facUniqBoundary
    (J := WalkingParallelPair) (metrizableLCAOppositeWeakEquivalence.Q)
    metrizableLCAOppositeWeakEquivalence h

/-- Coherent opposite strict representatives sufficient to define the candidate `lift`. -/
abbrev OppositeWalkingParallelPairLiftBlueprint : Type _ :=
  CategoryTheory.Localization.W274WalkingParallelPairLiftBlueprint
    (metrizableLCAOppositeWeakEquivalence.Q)

/-- A checked candidate `lift` field for any fixed target, assuming a coherent blueprint. -/
def oppositeLiftFieldFromBlueprint
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (E : Type u) [Category E] :
    ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤ E),
      (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F →
        (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤ E :=
  fun F _ => B.liftFunctor F

/-- Reusable fixed-target `fac` schema for the blueprint-produced lift. -/
abbrev OppositeFixedTargetFacObligationFor
    (B : OppositeWalkingParallelPairLiftBlueprint) (E : Type u) [Category E] : Prop :=
  ∀ (F : (WalkingParallelPair ⥤ (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ) ⥤ E)
    (hF : (metrizableLCAOppositeWeakEquivalence.functorCategory WalkingParallelPair).IsInvertedBy F),
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙
          oppositeLiftFieldFromBlueprint B E F hF = F

/-- Reusable fixed-target `uniq` schema for objectwise opposite postcomposition. -/
abbrev OppositeFixedTargetUniqObligationFor (E : Type u) [Category E] : Prop :=
  ∀ (F₁ F₂ :
      (WalkingParallelPair ⥤ (metrizableLCAOppositeWeakEquivalence).Localization) ⥤ E),
    MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₁ =
      MetrizableLCAOppositeWalkingParallelPairObjectwiseFunctor ⋙ F₂ →
    F₁ = F₂

/-- The explicit `fac` obligation for the diagram fixed target. -/
abbrev OppositeDiagramFixedTargetFacObligation
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop :=
  OppositeFixedTargetFacObligationFor B OppositeDiagramFixedTarget

/-- The explicit `uniq` obligation for the diagram fixed target. -/
abbrev OppositeDiagramFixedTargetUniqObligation : Prop :=
  OppositeFixedTargetUniqObligationFor OppositeDiagramFixedTarget

/-- The explicit `fac` obligation for the model fixed target. -/
abbrev OppositeModelFixedTargetFacObligation
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop :=
  OppositeFixedTargetFacObligationFor B OppositeModelFixedTarget

/-- The explicit `uniq` obligation for the model fixed target. -/
abbrev OppositeModelFixedTargetUniqObligation : Prop :=
  OppositeFixedTargetUniqObligationFor OppositeModelFixedTarget

/--
The four named obligations are equivalent to two instances of the reusable schemas:
one `fac` schema and one `uniq` schema at each fixed target.
-/
structure OppositeFixedTargetObligationBoundary
    (B : OppositeWalkingParallelPairLiftBlueprint) : Prop where
  diagram_fac : OppositeDiagramFixedTargetFacObligation B
  diagram_uniq : OppositeDiagramFixedTargetUniqObligation
  model_fac : OppositeModelFixedTargetFacObligation B
  model_uniq : OppositeModelFixedTargetUniqObligation

namespace OppositeFixedTargetObligationBoundary

variable {B : OppositeWalkingParallelPairLiftBlueprint}

/-- Package the four obligations as the two fixed-target boundary records. -/
def toFixedTargetBoundary
    (h : OppositeFixedTargetObligationBoundary B) :
    OppositeTwoFixedTargetBoundary where
  target :=
    { lift := oppositeLiftFieldFromBlueprint B OppositeDiagramFixedTarget
      fac := h.diagram_fac
      uniq := h.diagram_uniq }
  model :=
    { lift := oppositeLiftFieldFromBlueprint B OppositeModelFixedTarget
      fac := h.model_fac
      uniq := h.model_uniq }

end OppositeFixedTargetObligationBoundary

/--
Smallest checked handoff around the candidate blueprint: once the four named
`fac`/`uniq` obligations are supplied, the opposite functor-category localization
input follows.
-/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_obligations
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (h : OppositeFixedTargetObligationBoundary B) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  metrizableLCA_oppositeFunctorCategoryLocalization_of_fixedTargetBoundary
    h.toFixedTargetBoundary

/-- Direct constructor when the four fixed-target obligations are passed separately. -/
theorem metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq
    (B : OppositeWalkingParallelPairLiftBlueprint)
    (hTargetFac : OppositeDiagramFixedTargetFacObligation B)
    (hTargetUniq : OppositeDiagramFixedTargetUniqObligation)
    (hModelFac : OppositeModelFixedTargetFacObligation B)
    (hModelUniq : OppositeModelFixedTargetUniqObligation) :
    MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput :=
  metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_obligations B
    { diagram_fac := hTargetFac
      diagram_uniq := hTargetUniq
      model_fac := hModelFac
      model_uniq := hModelUniq }

/-- Machine-readable frontier state for W274. -/
structure OppositeFixedTargetObligationState : Type where
  seedHash : String
  route : String
  constructedField : String
  schemaObligations : List String
  fixedTargetObligations : List String
  theoremBoundary : String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

/-- Reproducible W274 state. -/
def currentOppositeFixedTargetObligationState :
    OppositeFixedTargetObligationState where
  seedHash := "8f8fe8fbde2955ac95119ce7a98c87ca93d8471e19cedd1aa0e830f3d005b3a4"
  route := "v293 fixed-target obligation schema: blueprint lift plus fac/uniq schemas"
  constructedField := "oppositeLiftFieldFromBlueprint"
  schemaObligations :=
    ["OppositeFixedTargetFacObligationFor",
      "OppositeFixedTargetUniqObligationFor"]
  fixedTargetObligations :=
    ["OppositeDiagramFixedTargetFacObligation",
      "OppositeDiagramFixedTargetUniqObligation",
      "OppositeModelFixedTargetFacObligation",
      "OppositeModelFixedTargetUniqObligation"]
  theoremBoundary :=
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_obligations"
  remainingInputs :=
    ["OppositeWalkingParallelPairLiftBlueprint",
      "OppositeFixedTargetFacObligationFor B OppositeDiagramFixedTarget",
      "OppositeFixedTargetUniqObligationFor OppositeDiagramFixedTarget",
      "OppositeFixedTargetFacObligationFor B OppositeModelFixedTarget",
      "OppositeFixedTargetUniqObligationFor OppositeModelFixedTarget"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentOppositeFixedTargetObligationState_subgoalSuccess :
    currentOppositeFixedTargetObligationState.subgoalSuccessClaimed = true := rfl

theorem currentOppositeFixedTargetObligationState_productSuccess :
    currentOppositeFixedTargetObligationState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W274. -/
def oppositeFixedTargetObligationDeclarationNames : List String :=
  ["CategoryTheory.Localization.W274ObjectwiseFunctor",
    "CategoryTheory.Localization.w274Objectwise_inverts",
    "CategoryTheory.Localization.W274FixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.W274FixedTargetFacUniqBoundary.toStrictUniversalProperty",
    "CategoryTheory.Localization.W274TwoFixedTargetFacUniqBoundary",
    "CategoryTheory.Localization.w274Objectwise_isLocalization_of_facUniqBoundary",
    "CategoryTheory.Localization.W274WalkingParallelPairLiftBlueprint",
    "CategoryTheory.Localization.W274WalkingParallelPairLiftBlueprint.liftFunctor",
    "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput",
    "OppositeWalkingParallelPairLiftBlueprint",
    "oppositeLiftFieldFromBlueprint",
    "OppositeFixedTargetFacObligationFor",
    "OppositeFixedTargetUniqObligationFor",
    "OppositeDiagramFixedTargetFacObligation",
    "OppositeDiagramFixedTargetUniqObligation",
    "OppositeModelFixedTargetFacObligation",
    "OppositeModelFixedTargetUniqObligation",
    "OppositeFixedTargetObligationBoundary",
    "OppositeFixedTargetObligationBoundary.toFixedTargetBoundary",
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_obligations",
    "metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq",
    "currentOppositeFixedTargetObligationState"]

theorem oppositeFixedTargetObligationDeclarationNames_count :
    oppositeFixedTargetObligationDeclarationNames.length = 22 := rfl

section Checks

#check CategoryTheory.Localization.W274ObjectwiseFunctor
#check CategoryTheory.Localization.w274Objectwise_inverts
#check CategoryTheory.Localization.W274FixedTargetFacUniqBoundary
#check CategoryTheory.Localization.W274FixedTargetFacUniqBoundary.toStrictUniversalProperty
#check CategoryTheory.Localization.W274TwoFixedTargetFacUniqBoundary
#check CategoryTheory.Localization.w274Objectwise_isLocalization_of_facUniqBoundary
#check CategoryTheory.Localization.W274WalkingParallelPairLiftBlueprint
#check CategoryTheory.Localization.W274WalkingParallelPairLiftBlueprint.liftFunctor
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
#check OppositeFixedTargetFacObligationFor
#check OppositeFixedTargetUniqObligationFor
#check OppositeDiagramFixedTargetFacObligation
#check OppositeDiagramFixedTargetUniqObligation
#check OppositeModelFixedTargetFacObligation
#check OppositeModelFixedTargetUniqObligation
#check OppositeFixedTargetObligationBoundary
#check OppositeFixedTargetObligationBoundary.toFixedTargetBoundary
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_obligations
#check metrizableLCA_oppositeFunctorCategoryLocalization_of_blueprint_fac_uniq
#check currentOppositeFixedTargetObligationState
#check currentOppositeFixedTargetObligationState_subgoalSuccess
#check currentOppositeFixedTargetObligationState_productSuccess
#check oppositeFixedTargetObligationDeclarationNames
#check oppositeFixedTargetObligationDeclarationNames_count

end Checks

end OppositeFixedTargetObligationsW274

end LeanLCAExactChallenge
