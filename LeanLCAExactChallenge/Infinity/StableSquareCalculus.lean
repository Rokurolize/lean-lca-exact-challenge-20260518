import LeanLCAExactChallenge.Infinity.Stable
import LeanLCAExactChallenge.Infinity.FunctorQuasicategory

/-!
# A canonical square-calculus interface for stable quasicategories

The quasicategory structures on functor objects are canonical in the pinned mathlib version.
This file isolates the genuinely mathematical input needed to construct
`StableInfinityStructure`: pointedness, finite bicompleteness, the two corner-extension
adjunctions, and agreement of their essential images.

In particular, this interface does not infer infinity-categorical stability merely from a
triangulated homotopy category.  A dg nerve implementation must construct the adjunctions and
prove the bicartesian comparison below, normally from enriched zero objects and mapping cones.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.MonoidalClosed
open Simplicial

universe u

/-- The canonical quasicategory structure on a functor object with quasicategorical target. -/
abbrev canonicalFunctorQuasicategory (K : SSet.{u}) (Q : SSet.QCat.{u}) :
    SSet.Quasicategory ((ihom K).obj Q.obj) :=
  @quasicategory_ihom K Q.obj Q.property

/-- The mathematical square calculus required for stability, with all functor-quasicategory
structures chosen canonically.

This is the appropriate target for a construction from zero objects, shifts, and mapping
cones in a pretriangulated dg category: those constructions must supply the two Kan-extension
adjunctions and identify their essential images. -/
structure StableSquareCalculus (Q : SSet.QCat.{u}) where
  pointed : PointedStructure Q
  finiteBicomplete : HasFiniteInfinityBicompleteness Q
  pullbackKanExtension :
    Bicategory.IsLeftAdjoint
      (pullbackRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PullbackCornerShape Q))
  pushoutKanExtension :
    Bicategory.IsRightAdjoint
      (pushoutRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PushoutCornerShape Q))
  bicartesian :
    ∀ sq : (functorQCat SquareShape Q
        (canonicalFunctorQuasicategory SquareShape Q)).obj _⦋0⦌,
      IsPullbackSquare Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PullbackCornerShape Q)
          pullbackKanExtension sq ↔
        IsPushoutSquare Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PushoutCornerShape Q)
          pushoutKanExtension sq

/-- Package a canonical stable square calculus as the repository's full stable-infinity
structure.  No homotopy-category criterion or unverified stability implication is used. -/
def StableSquareCalculus.toStableInfinityStructure {Q : SSet.QCat.{u}}
    (h : StableSquareCalculus Q) : StableInfinityStructure Q where
  pointed := h.pointed
  finiteBicomplete := h.finiteBicomplete
  squareQuasicategory := canonicalFunctorQuasicategory SquareShape Q
  pullbackCornerQuasicategory := canonicalFunctorQuasicategory PullbackCornerShape Q
  pushoutCornerQuasicategory := canonicalFunctorQuasicategory PushoutCornerShape Q
  pullbackKanExtension := h.pullbackKanExtension
  pushoutKanExtension := h.pushoutKanExtension
  bicartesian := h.bicartesian

/-- Forget the noncanonical proof witnesses in an existing stable structure. -/
def StableSquareCalculus.ofStableInfinityStructure {Q : SSet.QCat.{u}}
    (h : StableInfinityStructure Q) : StableSquareCalculus Q := by
  cases Subsingleton.elim h.squareQuasicategory
    (canonicalFunctorQuasicategory SquareShape Q)
  cases Subsingleton.elim h.pullbackCornerQuasicategory
    (canonicalFunctorQuasicategory PullbackCornerShape Q)
  cases Subsingleton.elim h.pushoutCornerQuasicategory
    (canonicalFunctorQuasicategory PushoutCornerShape Q)
  exact
    { pointed := h.pointed
      finiteBicomplete := h.finiteBicomplete
      pullbackKanExtension := h.pullbackKanExtension
      pushoutKanExtension := h.pushoutKanExtension
      bicartesian := h.bicartesian }

/-- Canonicalizing the functor-quasicategory proofs does not change a stable structure. -/
theorem StableSquareCalculus.toStable_ofStable {Q : SSet.QCat.{u}}
    (h : StableInfinityStructure Q) :
    (StableSquareCalculus.ofStableInfinityStructure h).toStableInfinityStructure = h := by
  cases h
  rfl

/-- Packaging and then canonicalizing a square calculus returns its original data. -/
theorem StableSquareCalculus.ofStable_toStable {Q : SSet.QCat.{u}}
    (h : StableSquareCalculus Q) :
    StableSquareCalculus.ofStableInfinityStructure h.toStableInfinityStructure = h := by
  cases h
  rfl

end Infinity
end LeanLCAExactChallenge
