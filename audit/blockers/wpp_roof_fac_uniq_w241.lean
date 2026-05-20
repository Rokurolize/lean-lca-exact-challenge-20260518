import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import LeanLCAExactChallenge.Derived.Bounded

/-!
W241 audit: bridge from roof data toward strict `WalkingParallelPair` lift data.

If each roof arrow can be strictified to a selected source arrow, the strict
parallel-pair data and naturality fields required by the W231 lift frontier follow.
The missing theorem is the coherent roof-to-selected-endpoint strictification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

structure W241ArrowRoofData (L : C ⥤ D)
    {X Y : D} (src tgt : C) (srcIso : L.obj src ≅ X) (tgtIso : L.obj tgt ≅ Y)
    (f : X ⟶ Y) where
  apex : C
  denom : apex ⟶ src
  num : apex ⟶ tgt
  [denom_isIso : IsIso (L.map denom)]
  roof_fac :
    srcIso.hom ≫ f ≫ tgtIso.inv = inv (L.map denom) ≫ L.map num

attribute [instance] W241ArrowRoofData.denom_isIso

structure W241StrictArrowRep (L : C ⥤ D)
    {X Y : D} {src tgt : C} {srcIso : L.obj src ≅ X} {tgtIso : L.obj tgt ≅ Y}
    {f : X ⟶ Y} (roof : W241ArrowRoofData L src tgt srcIso tgtIso f) where
  strict : src ⟶ tgt
  strict_fac :
    L.map strict = srcIso.hom ≫ f ≫ tgtIso.inv

namespace W241StrictArrowRep

variable {L : C ⥤ D}
variable {X Y : D} {src tgt : C} {srcIso : L.obj src ≅ X} {tgtIso : L.obj tgt ≅ Y}
variable {f : X ⟶ Y} {roof : W241ArrowRoofData L src tgt srcIso tgtIso f}

theorem fac (r : W241StrictArrowRep L roof) :
    L.map r.strict = srcIso.hom ≫ f ≫ tgtIso.inv :=
  r.strict_fac

end W241StrictArrowRep

structure W241RoofPairData (L : C ⥤ D) (Y : WalkingParallelPair ⥤ D) where
  zeroSrc : C
  oneSrc : C
  zeroIso : L.obj zeroSrc ≅ Y.obj WalkingParallelPair.zero
  oneIso : L.obj oneSrc ≅ Y.obj WalkingParallelPair.one
  leftRoof :
    W241ArrowRoofData L zeroSrc oneSrc zeroIso oneIso
      (Y.map WalkingParallelPairHom.left)
  rightRoof :
    W241ArrowRoofData L zeroSrc oneSrc zeroIso oneIso
      (Y.map WalkingParallelPairHom.right)

structure W241RoofPairStrictification (L : C ⥤ D) {Y : WalkingParallelPair ⥤ D}
    (d : W241RoofPairData L Y) where
  leftRep : W241StrictArrowRep L d.leftRoof
  rightRep : W241StrictArrowRep L d.rightRoof

structure W241StrictPairData (L : C ⥤ D) (Y : WalkingParallelPair ⥤ D) where
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

namespace W241StrictPairData

variable {L : C ⥤ D} {Y : WalkingParallelPair ⥤ D}

def diagram (d : W241StrictPairData L Y) : WalkingParallelPair ⥤ C :=
  parallelPair d.leftSrc d.rightSrc

def comparisonIso (d : W241StrictPairData L Y) :
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

end W241StrictPairData

namespace W241RoofPairStrictification

variable {L : C ⥤ D} {Y : WalkingParallelPair ⥤ D}

def toStrictPairData {d : W241RoofPairData L Y} (s : W241RoofPairStrictification L d) :
    W241StrictPairData L Y where
  zeroSrc := d.zeroSrc
  oneSrc := d.oneSrc
  zeroIso := d.zeroIso
  oneIso := d.oneIso
  leftSrc := s.leftRep.strict
  rightSrc := s.rightRep.strict
  left_fac := s.leftRep.fac
  right_fac := s.rightRep.fac

theorem toStrictPairData_left_fac {d : W241RoofPairData L Y}
    (s : W241RoofPairStrictification L d) :
    L.map (s.toStrictPairData.leftSrc) =
      s.toStrictPairData.zeroIso.hom ≫ Y.map WalkingParallelPairHom.left ≫
        s.toStrictPairData.oneIso.inv :=
  s.toStrictPairData.left_fac

theorem toStrictPairData_right_fac {d : W241RoofPairData L Y}
    (s : W241RoofPairStrictification L d) :
    L.map (s.toStrictPairData.rightSrc) =
      s.toStrictPairData.zeroIso.hom ≫ Y.map WalkingParallelPairHom.right ≫
        s.toStrictPairData.oneIso.inv :=
  s.toStrictPairData.right_fac

end W241RoofPairStrictification

structure W241StrictNatComponentData (L : C ⥤ D)
    {Y Z : WalkingParallelPair ⥤ D}
    (dY : W241StrictPairData L Y) (dZ : W241StrictPairData L Z)
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

namespace W241StrictNatComponentData

variable {L : C ⥤ D} {Y Z : WalkingParallelPair ⥤ D}
variable {dY : W241StrictPairData L Y} {dZ : W241StrictPairData L Z}
variable {τ : Y ⟶ Z}

def natTrans (m : W241StrictNatComponentData L dY dZ τ) :
    dY.diagram ⟶ dZ.diagram :=
  parallelPairHomMk m.zeroMap m.oneMap
    (by
      dsimp [W241StrictPairData.diagram]
      exact m.left_naturality)
    (by
      dsimp [W241StrictPairData.diagram]
      exact m.right_naturality)

theorem left_naturality_fac (m : W241StrictNatComponentData L dY dZ τ) :
    dY.leftSrc ≫ m.oneMap = m.zeroMap ≫ dZ.leftSrc :=
  m.left_naturality

theorem right_naturality_fac (m : W241StrictNatComponentData L dY dZ τ) :
    dY.rightSrc ≫ m.oneMap = m.zeroMap ≫ dZ.rightSrc :=
  m.right_naturality

end W241StrictNatComponentData

abbrev W241RoofToStrictArrowTheorem (L : C ⥤ D) : Prop :=
  ∀ {X Y : D} {src tgt : C} {srcIso : L.obj src ≅ X} {tgtIso : L.obj tgt ≅ Y}
    {f : X ⟶ Y} (roof : W241ArrowRoofData L src tgt srcIso tgtIso f),
    Nonempty (W241StrictArrowRep L roof)

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WPPRoofFacUniqW241

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

abbrev DboundedRoofToStrictArrowTheorem : Prop :=
  CategoryTheory.Localization.W241RoofToStrictArrowTheorem (Dbounded.localization C)

def missingTheoremName : String :=
  "Dbounded.localization roof-to-selected-endpoint strict arrow theorem"

structure WPPRoofFacUniqState : Type where
  strictBridgeConstructed : Bool
  productSuccessClaimed : Bool

def currentState : WPPRoofFacUniqState where
  strictBridgeConstructed := false
  productSuccessClaimed := false

theorem currentState_bridgeNotConstructed :
    currentState.strictBridgeConstructed = false := rfl

theorem currentState_productSuccess :
    currentState.productSuccessClaimed = false := rfl

section Checks

#check CategoryTheory.Localization.W241StrictArrowRep.fac
#check CategoryTheory.Localization.W241StrictPairData.comparisonIso
#check CategoryTheory.Localization.W241RoofPairStrictification.toStrictPairData_left_fac
#check CategoryTheory.Localization.W241RoofPairStrictification.toStrictPairData_right_fac
#check CategoryTheory.Localization.W241StrictNatComponentData.natTrans
#check CategoryTheory.Localization.W241StrictNatComponentData.left_naturality_fac
#check CategoryTheory.Localization.W241StrictNatComponentData.right_naturality_fac
#check CategoryTheory.Localization.W241RoofToStrictArrowTheorem
#check DboundedRoofToStrictArrowTheorem
#check missingTheoremName
#check currentState_bridgeNotConstructed
#check currentState_productSuccess

end Checks

end WPPRoofFacUniqW241

end LeanLCAExactChallenge
