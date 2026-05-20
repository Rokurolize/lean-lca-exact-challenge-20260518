import Mathlib.CategoryTheory.Localization.FiniteProducts
import LeanLCAExactChallenge.Derived.Bounded

/-!
W236 audit: roof-style data for the `WalkingParallelPair` fixed-target lift field.

Roof representatives in the localized target are weaker than the strict source
parallel-pair diagrams needed by the W231 lift blueprint.  This file records the
missing common-denominator strictification layer.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

structure WalkingParallelPairArrowRoofData (L : C ⥤ D)
    {X Y : D} (src tgt : C) (srcIso : L.obj src ≅ X) (tgtIso : L.obj tgt ≅ Y)
    (f : X ⟶ Y) where
  apex : C
  denom : apex ⟶ src
  num : apex ⟶ tgt
  [denom_isIso : IsIso (L.map denom)]
  fac : srcIso.hom ≫ f ≫ tgtIso.inv = inv (L.map denom) ≫ L.map num

structure WalkingParallelPairRoofPreimageData (L : C ⥤ D)
    (Y : WalkingParallelPair ⥤ D) where
  zeroSrc : C
  oneSrc : C
  zeroIso : L.obj zeroSrc ≅ Y.obj WalkingParallelPair.zero
  oneIso : L.obj oneSrc ≅ Y.obj WalkingParallelPair.one
  leftRoof :
    WalkingParallelPairArrowRoofData L zeroSrc oneSrc zeroIso oneIso
      (Y.map WalkingParallelPairHom.left)
  rightRoof :
    WalkingParallelPairArrowRoofData L zeroSrc oneSrc zeroIso oneIso
      (Y.map WalkingParallelPairHom.right)

structure WalkingParallelPairRoofPreimageMapData (L : C ⥤ D)
    {Y Z : WalkingParallelPair ⥤ D}
    (dY : WalkingParallelPairRoofPreimageData L Y)
    (dZ : WalkingParallelPairRoofPreimageData L Z)
    (τ : Y ⟶ Z) where
  zeroRoof :
    WalkingParallelPairArrowRoofData L dY.zeroSrc dZ.zeroSrc dY.zeroIso dZ.zeroIso
      (τ.app WalkingParallelPair.zero)
  oneRoof :
    WalkingParallelPairArrowRoofData L dY.oneSrc dZ.oneSrc dY.oneIso dZ.oneIso
      (τ.app WalkingParallelPair.one)
  naturalityRefinementData : List String

structure WalkingParallelPairRoofBlueprint (L : C ⥤ D) where
  objRoofData : ∀ (Y : WalkingParallelPair ⥤ D),
    WalkingParallelPairRoofPreimageData L Y
  mapRoofData : ∀ {Y Z : WalkingParallelPair ⥤ D} (τ : Y ⟶ Z),
    WalkingParallelPairRoofPreimageMapData L (objRoofData Y) (objRoofData Z) τ
  commonDenominatorData : List String
  strictificationData : List String
  functorialCoherenceData : List String

def walkingParallelPairRoofStrictificationChecklist : List String :=
  ["common refinements turning the left and right arrow roofs into strict maps",
    "proofs that those strict maps represent the target arrows after localization",
    "strict zero and one component maps for target natural transformations",
    "naturality equations for the strict component maps against both strict arrows",
    "identity and composition coherence for the selected strict representatives"]

theorem walkingParallelPairRoofStrictificationChecklist_count :
    walkingParallelPairRoofStrictificationChecklist.length = 5 := rfl

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WPPRoofBlueprintW236

variable (C : Type u) [Category.{v₁} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

abbrev WalkingParallelPairDboundedRoofBlueprint : Type _ :=
  CategoryTheory.Localization.WalkingParallelPairRoofBlueprint
    (Dbounded.localization C)

structure WPPRoofBlueprintState : Type where
  selectedRoute : Nat
  feedsW231StrictBlueprintDirectly : Bool
  productSuccessClaimed : Bool

def currentState : WPPRoofBlueprintState where
  selectedRoute := 2
  feedsW231StrictBlueprintDirectly := false
  productSuccessClaimed := false

theorem currentState_doesNotDirectlyFeedStrictBlueprint :
    currentState.feedsW231StrictBlueprintDirectly = false := rfl

theorem currentState_productSuccess :
    currentState.productSuccessClaimed = false := rfl

section Checks

#check CategoryTheory.Localization.WalkingParallelPairArrowRoofData
#check CategoryTheory.Localization.WalkingParallelPairRoofPreimageData
#check CategoryTheory.Localization.WalkingParallelPairRoofPreimageMapData
#check CategoryTheory.Localization.WalkingParallelPairRoofBlueprint
#check CategoryTheory.Localization.walkingParallelPairRoofStrictificationChecklist_count
#check WalkingParallelPairDboundedRoofBlueprint
#check currentState_doesNotDirectlyFeedStrictBlueprint
#check currentState_productSuccess

end Checks

end WPPRoofBlueprintW236

end LeanLCAExactChallenge
