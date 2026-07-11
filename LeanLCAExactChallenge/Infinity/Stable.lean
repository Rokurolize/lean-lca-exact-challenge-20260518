import LeanLCAExactChallenge.Infinity.Limits
import LeanLCAExactChallenge.Infinity.Relative
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# Stable quasicategories

This file formulates cartesian and cocartesian squares by Kan extension in the strict
bicategory of quasicategories.  A stable structure is pointed, finitely bicomplete, and has
the same cartesian and cocartesian squares.

The internal-Hom fields remain explicit to record the chosen mapping objects, although mathlib
v4.31 supplies their quasicategory structures. The Kan-extension fields are still genuine data
not derived from finite infinity-(co)completeness.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open Simplicial

universe u

/-- The base poset underlying the walking commutative square. -/
abbrev BaseSquareIndex := Fin 2 × Fin 2

-- Use the preorder category rather than the distinct product-category instance.
local instance baseSquareIndexCategory : Category.{0} BaseSquareIndex :=
  Preorder.smallCategory BaseSquareIndex

private def sq00 : BaseSquareIndex := (0, 0)
private def sq10 : BaseSquareIndex := (1, 0)
private def sq01 : BaseSquareIndex := (0, 1)
private def sq11 : BaseSquareIndex := (1, 1)

/-- The cospan corner includes into the square by omitting its initial vertex. -/
def basePullbackCornerFunctor : WalkingCospan ⥤ BaseSquareIndex :=
  cospan
    (homOfLE (show sq10 ≤ sq11 by decide))
    (homOfLE (show sq01 ≤ sq11 by decide))

/-- The span corner includes into the square by omitting its terminal vertex. -/
def basePushoutCornerFunctor : WalkingSpan ⥤ BaseSquareIndex :=
  span
    (homOfLE (show sq00 ≤ sq10 by decide))
    (homOfLE (show sq00 ≤ sq01 by decide))

/-- Universe-lifted walking-square index. -/
abbrev SquareIndex := ULift.{u} BaseSquareIndex

/-- Universe-lifted walking-cospan index. -/
abbrev PullbackCornerIndex := ULift.{u} WalkingCospan

/-- Universe-lifted walking-span index. -/
abbrev PushoutCornerIndex := ULift.{u} WalkingSpan

local instance squareIndexCategory : Category.{0} SquareIndex :=
  CategoryTheory.uliftCategory BaseSquareIndex

local instance pullbackCornerIndexCategory : Category.{0} PullbackCornerIndex :=
  CategoryTheory.uliftCategory WalkingCospan

local instance pushoutCornerIndexCategory : Category.{0} PushoutCornerIndex :=
  CategoryTheory.uliftCategory WalkingSpan

/-- The cospan corner includes into the universe-lifted square. -/
def pullbackCornerFunctor : PullbackCornerIndex ⥤ SquareIndex :=
  ULift.downFunctor ⋙ basePullbackCornerFunctor ⋙ ULift.upFunctor

/-- The span corner includes into the universe-lifted square. -/
def pushoutCornerFunctor : PushoutCornerIndex ⥤ SquareIndex :=
  ULift.downFunctor ⋙ basePushoutCornerFunctor ⋙ ULift.upFunctor

/-- The simplicial walking-square shape. -/
abbrev SquareShape : SSet.{u} := CategoryTheory.nerve SquareIndex

/-- The simplicial cospan shape. -/
abbrev PullbackCornerShape : SSet.{u} := CategoryTheory.nerve PullbackCornerIndex

/-- The simplicial span shape. -/
abbrev PushoutCornerShape : SSet.{u} := CategoryTheory.nerve PushoutCornerIndex

/-- Inclusion of the cospan corner into the square. -/
def pullbackCornerInclusion : PullbackCornerShape ⟶ SquareShape :=
  CategoryTheory.nerveMap pullbackCornerFunctor

/-- Inclusion of the span corner into the square. -/
def pushoutCornerInclusion : PushoutCornerShape ⟶ SquareShape :=
  CategoryTheory.nerveMap pushoutCornerFunctor

/-- Restriction of square diagrams to their cospan corner. -/
def pullbackRestriction (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PullbackCornerShape).obj Q.obj)) :
    functorQCat SquareShape Q hSquare ⟶ functorQCat PullbackCornerShape Q hCorner :=
  ObjectProperty.homMk ((MonoidalClosed.pre pullbackCornerInclusion).app Q.obj)

/-- Restriction of square diagrams to their span corner. -/
def pushoutRestriction (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PushoutCornerShape).obj Q.obj)) :
    functorQCat SquareShape Q hSquare ⟶ functorQCat PushoutCornerShape Q hCorner :=
  ObjectProperty.homMk ((MonoidalClosed.pre pushoutCornerInclusion).app Q.obj)

/-- The image of a vertex under a map of quasicategories. -/
def mapVertex {X Y : SSet.QCat.{u}} (F : X ⟶ Y) (x : X.obj _⦋0⦌) : Y.obj _⦋0⦌ :=
  F.hom.app _ x

/-- A vertex lies in the essential image when it is equivalent to an image vertex. -/
def InEssentialImage {X Y : SSet.QCat.{u}} (F : X ⟶ Y) (y : Y.obj _⦋0⦌) : Prop :=
  ∃ x : X.obj _⦋0⦌, ∃ e : SSet.Edge (mapVertex F x) y, EdgeIsEquivalence e

/-- A square is cartesian when it is in the essential image of right Kan extension from
its cospan corner. -/
def IsPullbackSquare (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PullbackCornerShape).obj Q.obj))
    (hAdj : Bicategory.IsLeftAdjoint (pullbackRestriction Q hSquare hCorner))
    (sq : (functorQCat SquareShape Q hSquare).obj _⦋0⦌) : Prop :=
  letI := hAdj
  InEssentialImage (Bicategory.rightAdjoint (pullbackRestriction Q hSquare hCorner)) sq

/-- A square is cocartesian when it is in the essential image of left Kan extension from
its span corner. -/
def IsPushoutSquare (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PushoutCornerShape).obj Q.obj))
    (hAdj : Bicategory.IsRightAdjoint (pushoutRestriction Q hSquare hCorner))
    (sq : (functorQCat SquareShape Q hSquare).obj _⦋0⦌) : Prop :=
  letI := hAdj
  InEssentialImage (Bicategory.leftAdjoint (pushoutRestriction Q hSquare hCorner)) sq

/-- Every square produced by the chosen right Kan extension is cartesian. -/
theorem isPullbackSquare_rightAdjoint_obj (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PullbackCornerShape).obj Q.obj))
    (hAdj : Bicategory.IsLeftAdjoint (pullbackRestriction Q hSquare hCorner))
    (d : (functorQCat PullbackCornerShape Q hCorner).obj _⦋0⦌) :
    IsPullbackSquare Q hSquare hCorner hAdj
      (letI := hAdj
       mapVertex (Bicategory.rightAdjoint (pullbackRestriction Q hSquare hCorner)) d) := by
  letI := hAdj
  exact ⟨d, SSet.Edge.id _, edgeIsEquivalence_id _⟩

/-- Every square produced by the chosen left Kan extension is cocartesian. -/
theorem isPushoutSquare_leftAdjoint_obj (Q : SSet.QCat.{u})
    (hSquare : SSet.Quasicategory ((ihom SquareShape).obj Q.obj))
    (hCorner : SSet.Quasicategory ((ihom PushoutCornerShape).obj Q.obj))
    (hAdj : Bicategory.IsRightAdjoint (pushoutRestriction Q hSquare hCorner))
    (d : (functorQCat PushoutCornerShape Q hCorner).obj _⦋0⦌) :
    IsPushoutSquare Q hSquare hCorner hAdj
      (letI := hAdj
       mapVertex (Bicategory.leftAdjoint (pushoutRestriction Q hSquare hCorner)) d) := by
  letI := hAdj
  exact ⟨d, SSet.Edge.id _, edgeIsEquivalence_id _⟩

/-- Stable infinity-categorical structure, expressed by bicartesian squares.

The quasicategory and Kan-extension fields are explicit in the pinned mathlib version. -/
structure StableInfinityStructure (Q : SSet.QCat.{u}) where
  pointed : PointedStructure Q
  finiteBicomplete : HasFiniteInfinityBicompleteness Q
  squareQuasicategory : SSet.Quasicategory ((ihom SquareShape).obj Q.obj)
  pullbackCornerQuasicategory :
    SSet.Quasicategory ((ihom PullbackCornerShape).obj Q.obj)
  pushoutCornerQuasicategory :
    SSet.Quasicategory ((ihom PushoutCornerShape).obj Q.obj)
  pullbackKanExtension :
    Bicategory.IsLeftAdjoint
      (pullbackRestriction Q squareQuasicategory pullbackCornerQuasicategory)
  pushoutKanExtension :
    Bicategory.IsRightAdjoint
      (pushoutRestriction Q squareQuasicategory pushoutCornerQuasicategory)
  bicartesian : ∀ sq : (functorQCat SquareShape Q squareQuasicategory).obj _⦋0⦌,
    IsPullbackSquare Q squareQuasicategory pullbackCornerQuasicategory
        pullbackKanExtension sq ↔
      IsPushoutSquare Q squareQuasicategory pushoutCornerQuasicategory
        pushoutKanExtension sq

end Infinity
end LeanLCAExactChallenge
