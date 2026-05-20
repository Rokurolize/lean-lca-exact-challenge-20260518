import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
W231 audit: object and arrow data needed for the `WalkingParallelPair` fixed-target
`lift` field.

W227 isolated the `lift`, `fac`, and `uniq` fields for the objectwise localization
functor

```
  (WalkingParallelPair ⥤ BoundedComplexCategory C) ⥤
    (WalkingParallelPair ⥤ Dbounded C).
```

This file does not prove the missing non-discrete functor-category localization theorem.
It exposes a strict blueprint for the `lift` field: to evaluate a functor out of
source parallel-pair diagrams on a target parallel-pair diagram, it is enough to choose
source representatives for the two endpoints and source representatives for the two
parallel arrows, together with compatible source representatives for natural
transformations.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/--
A strict source representative for one `WalkingParallelPair` diagram after applying a
localization functor objectwise.

For a target diagram `Y : WalkingParallelPair ⥤ D`, this records source endpoint
objects and source representatives for both parallel arrows.  The two equations are the
exact arrow-compatibility data needed to regard the chosen source parallel pair as a
strict preimage of `Y`.
-/
structure WalkingParallelPairStrictPreimageData (L : C ⥤ D)
    (Y : WalkingParallelPair ⥤ D) where
  zeroSrc : C
  oneSrc : C
  zeroIso : L.obj zeroSrc ≅ Y.obj WalkingParallelPair.zero
  oneIso : L.obj oneSrc ≅ Y.obj WalkingParallelPair.one
  leftSrc : zeroSrc ⟶ oneSrc
  rightSrc : zeroSrc ⟶ oneSrc
  left_fac :
    L.map leftSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.left ≫ oneIso.inv
  right_fac :
    L.map rightSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.right ≫ oneIso.inv

namespace WalkingParallelPairStrictPreimageData

variable {L : C ⥤ D} {Y : WalkingParallelPair ⥤ D}

/-- The source parallel-pair diagram represented by strict preimage data. -/
def diagram (d : WalkingParallelPairStrictPreimageData L Y) :
    WalkingParallelPair ⥤ C :=
  parallelPair d.leftSrc d.rightSrc

/-- The objectwise comparison from the localized strict preimage to the target diagram. -/
def comparisonIso (d : WalkingParallelPairStrictPreimageData L Y) :
    ((Functor.whiskeringRight WalkingParallelPair C D).obj L).obj d.diagram ≅ Y :=
  parallelPairIsoMk d.zeroIso d.oneIso
    (by
      dsimp [diagram]
      rw [d.left_fac]
      simp [Category.assoc])
    (by
      dsimp [diagram]
      rw [d.right_fac]
      simp [Category.assoc])

end WalkingParallelPairStrictPreimageData

/--
Strict source representative for a natural transformation between two target
parallel-pair diagrams, relative to chosen strict preimages.

The endpoint equations say the two source component maps really represent the target
components after localization.  The final two equations say those components form a
natural transformation between the chosen source parallel pairs.
-/
structure WalkingParallelPairStrictPreimageMapData (L : C ⥤ D)
    {Y Z : WalkingParallelPair ⥤ D}
    (dY : WalkingParallelPairStrictPreimageData L Y)
    (dZ : WalkingParallelPairStrictPreimageData L Z)
    (τ : Y ⟶ Z) where
  zeroMap : dY.zeroSrc ⟶ dZ.zeroSrc
  oneMap : dY.oneSrc ⟶ dZ.oneSrc
  zero_fac :
    L.map zeroMap =
      dY.zeroIso.hom ≫ τ.app WalkingParallelPair.zero ≫ dZ.zeroIso.inv
  one_fac :
    L.map oneMap =
      dY.oneIso.hom ≫ τ.app WalkingParallelPair.one ≫ dZ.oneIso.inv
  left_naturality : dY.leftSrc ≫ oneMap = zeroMap ≫ dZ.leftSrc
  right_naturality : dY.rightSrc ≫ oneMap = zeroMap ≫ dZ.rightSrc

namespace WalkingParallelPairStrictPreimageMapData

variable {L : C ⥤ D} {Y Z : WalkingParallelPair ⥤ D}
variable {dY : WalkingParallelPairStrictPreimageData L Y}
variable {dZ : WalkingParallelPairStrictPreimageData L Z}
variable {τ : Y ⟶ Z}

/-- The source natural transformation represented by strict map data. -/
def natTrans (m : WalkingParallelPairStrictPreimageMapData L dY dZ τ) :
    dY.diagram ⟶ dZ.diagram :=
  parallelPairHomMk m.zeroMap m.oneMap
    (by
      dsimp [WalkingParallelPairStrictPreimageData.diagram]
      exact m.left_naturality)
    (by
      dsimp [WalkingParallelPairStrictPreimageData.diagram]
      exact m.right_naturality)

end WalkingParallelPairStrictPreimageMapData

/--
Coherent strict source data for all objects and morphisms of the target parallel-pair
functor category.

The last two fields are the functoriality obligations for the chosen source
representatives.  They are the remaining bookkeeping needed before any fixed target
`F : (WalkingParallelPair ⥤ C) ⥤ E` can be precomposed with these representatives.
-/
structure WalkingParallelPairLiftBlueprint (L : C ⥤ D) where
  objData : ∀ (Y : WalkingParallelPair ⥤ D),
    WalkingParallelPairStrictPreimageData L Y
  mapData : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    WalkingParallelPairStrictPreimageMapData L (objData Y) (objData Z) τ
  map_id : ∀ (Y : WalkingParallelPair ⥤ D),
    (mapData (𝟙 Y)).natTrans = 𝟙 (objData Y).diagram
  map_comp : ∀ {Y Z T : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z) (σ : Z ⟶ T),
    (mapData (τ ≫ σ)).natTrans = (mapData τ).natTrans ≫ (mapData σ).natTrans

namespace WalkingParallelPairLiftBlueprint

variable {L : C ⥤ D}
variable {E : Type u} [Category E]

/--
The candidate `lift` functor on any fixed target `E`, assuming coherent strict
representatives for all target parallel-pair diagrams and their morphisms.
-/
@[simps obj map]
def liftFunctor (B : WalkingParallelPairLiftBlueprint L)
    (F : (WalkingParallelPair ⥤ C) ⥤ E) :
    (WalkingParallelPair ⥤ D) ⥤ E where
  obj Y := F.obj (B.objData Y).diagram
  map {Y Z} τ := F.map ((B.mapData τ).natTrans)
  map_id Y := by
    rw [B.map_id Y]
    exact F.map_id _
  map_comp τ σ := by
    rw [B.map_comp τ σ]
    exact F.map_comp _ _

end WalkingParallelPairLiftBlueprint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WalkingParallelPairLiftFieldsW231

variable (C : Type u) [Category.{v₁} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/-- The objectwise functor whose fixed-target `lift`, `fac`, and `uniq` fields remain. -/
abbrev WalkingParallelPairObjectwiseFunctor :
    (WalkingParallelPair ⥤ BoundedComplexCategory C) ⥤ (WalkingParallelPair ⥤ Dbounded C) :=
  (Functor.whiskeringRight WalkingParallelPair (BoundedComplexCategory C) (Dbounded C)).obj
    (Dbounded.localization C)

/-- The strict data exposed by this worker for the `Dbounded.localization C` model. -/
abbrev WalkingParallelPairDboundedLiftBlueprint : Type _ :=
  CategoryTheory.Localization.WalkingParallelPairLiftBlueprint
    (Dbounded.localization C)

/-- The candidate `lift` field obtained from a coherent strict blueprint. -/
abbrev candidateLiftFromBlueprint (B : WalkingParallelPairDboundedLiftBlueprint C)
    (E : Type u) [Category E] :
    ((WalkingParallelPair ⥤ BoundedComplexCategory C) ⥤ E) →
      (WalkingParallelPair ⥤ Dbounded C) ⥤ E :=
  fun F => B.liftFunctor F

/-- Named frontier state for the fixed-target field decomposition. -/
structure WalkingParallelPairLiftFieldsState : Type where
  selectedRoute : Nat
  seedHash : String
  upstreamWorker : String
  objectData : List String
  arrowData : List String
  morphismCompatibilityData : List String
  constructedField : String
  remainingFields : List String
  productSuccessClaimed : Bool

/-- Route-3 state: strict object/arrow representatives are enough to define `lift`. -/
def currentState : WalkingParallelPairLiftFieldsState where
  selectedRoute := 3
  seedHash := "3681d07369e6ce62dca7370938c4715a42386389672084375be3b679693dd14c"
  upstreamWorker := "W227"
  objectData :=
    ["zeroSrc",
      "oneSrc",
      "zeroIso : L.obj zeroSrc ~= Y.obj zero",
      "oneIso : L.obj oneSrc ~= Y.obj one"]
  arrowData :=
    ["leftSrc : zeroSrc -> oneSrc with localized left_fac",
      "rightSrc : zeroSrc -> oneSrc with localized right_fac"]
  morphismCompatibilityData :=
    ["zeroMap and oneMap represent target natural-transformation components",
      "left_naturality",
      "right_naturality",
      "map_id",
      "map_comp"]
  constructedField :=
    "CategoryTheory.Localization.WalkingParallelPairLiftBlueprint.liftFunctor"
  remainingFields := ["fac", "uniq", "existence of coherent strict blueprints"]
  productSuccessClaimed := false

theorem currentState_route :
    currentState.selectedRoute = 3 := rfl

theorem currentState_productSuccess :
    currentState.productSuccessClaimed = false := rfl

/-- Named declarations produced by W231. -/
def declarationNames : List String :=
  ["CategoryTheory.Localization.WalkingParallelPairStrictPreimageData",
    "CategoryTheory.Localization.WalkingParallelPairStrictPreimageData.diagram",
    "CategoryTheory.Localization.WalkingParallelPairStrictPreimageData.comparisonIso",
    "CategoryTheory.Localization.WalkingParallelPairStrictPreimageMapData",
    "CategoryTheory.Localization.WalkingParallelPairStrictPreimageMapData.natTrans",
    "CategoryTheory.Localization.WalkingParallelPairLiftBlueprint",
    "CategoryTheory.Localization.WalkingParallelPairLiftBlueprint.liftFunctor",
    "WalkingParallelPairObjectwiseFunctor",
    "WalkingParallelPairDboundedLiftBlueprint",
    "candidateLiftFromBlueprint",
    "currentState"]

theorem declarationNames_count :
    declarationNames.length = 11 := rfl

section Checks

#check CategoryTheory.Localization.WalkingParallelPairStrictPreimageData
#check CategoryTheory.Localization.WalkingParallelPairStrictPreimageData.diagram
#check CategoryTheory.Localization.WalkingParallelPairStrictPreimageData.comparisonIso
#check CategoryTheory.Localization.WalkingParallelPairStrictPreimageMapData
#check CategoryTheory.Localization.WalkingParallelPairStrictPreimageMapData.natTrans
#check CategoryTheory.Localization.WalkingParallelPairLiftBlueprint
#check CategoryTheory.Localization.WalkingParallelPairLiftBlueprint.liftFunctor
#check WalkingParallelPairObjectwiseFunctor
#check WalkingParallelPairDboundedLiftBlueprint
#check candidateLiftFromBlueprint
#check currentState
#check currentState_route
#check currentState_productSuccess
#check declarationNames
#check declarationNames_count

end Checks

end WalkingParallelPairLiftFieldsW231

end LeanLCAExactChallenge
