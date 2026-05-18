import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
Compile-checked interface for Quillen-style exact categories.

This is deliberately an interface, not a proof that the metrizable LCA category
satisfies the axioms.  The LCA instance in this project is exposed only from
explicit source-patch assumptions recorded in the gap analysis.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/-- A local Quillen exact-category interface over a category with zero morphisms. -/
class QuillenExactCategory (C : Type u) [Category.{v} C] [HasZeroMorphisms C] where
  /-- The distinguished kernel-cokernel pairs, represented as short complexes. -/
  Conflation : ShortComplex C → Prop
  /-- Conflations are invariant under isomorphism of short complexes. -/
  conflation_iso {S T : ShortComplex C} (e : S ≅ T) :
    Conflation S → Conflation T
  /-- Every short exact complex is a conflation in the local interface. -/
  split_conflation (S : ShortComplex C) : S.ShortExact → Conflation S
  /-- Pushouts of inflations remain inflations. -/
  pushout_inflation {S : ShortComplex C} (hS : Conflation S) {Y : C}
    (a : S.X₁ ⟶ Y) [HasPushout S.f a] :
    ∃ (Z : C) (g : pushout S.f a ⟶ Z) (zero : pushout.inr S.f a ≫ g = 0),
      Conflation (ShortComplex.mk (pushout.inr S.f a) g zero)
  /-- Pullbacks of deflations remain deflations. -/
  pullback_deflation {S : ShortComplex C} (hS : Conflation S) {Y : C}
    (a : Y ⟶ S.X₃) [HasPullback a S.g] :
    ∃ (X : C) (f : X ⟶ pullback a S.g) (zero : f ≫ pullback.fst a S.g = 0),
      Conflation (ShortComplex.mk f (pullback.fst a S.g) zero)

namespace QuillenExactCategory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [QuillenExactCategory C]

/-- An inflation is the first map of a conflation. -/
def inflation {X Y : C} (i : X ⟶ Y) : Prop :=
  ∃ (Z : C) (g : Y ⟶ Z) (zero : i ≫ g = 0),
    QuillenExactCategory.Conflation (ShortComplex.mk i g zero)

/-- A deflation is the second map of a conflation. -/
def deflation {X Y : C} (p : X ⟶ Y) : Prop :=
  ∃ (W : C) (f : W ⟶ X) (zero : f ≫ p = 0),
    QuillenExactCategory.Conflation (ShortComplex.mk f p zero)

end QuillenExactCategory

end LeanLCAExactChallenge
