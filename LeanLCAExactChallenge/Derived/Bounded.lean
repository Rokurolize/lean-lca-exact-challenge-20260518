import Mathlib.Algebra.Homology.DerivedCategory.Basic
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Bounded derived infinity-category frontier.

Mathlib has a checked derived category for abelian categories.  A bounded
derived infinity-category attached directly to a Quillen exact category is not
available here, so the exact-category version is represented as an explicit
construction interface for future source patches.
-/

set_option autoImplicit false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
A proposed interface for the bounded derived infinity-category of an exact
category.  Supplying this structure is part of the missing source patch.
-/
structure BoundedDerivedInfinityCategory (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [QuillenExactCategory C] : Type (max (u + 1) (v + 1)) where
  underlying : Type (max u v)
  [category : Category.{max u v} underlying]

attribute [instance] BoundedDerivedInfinityCategory.category

/-- The underlying category of a chosen bounded derived infinity-category construction. -/
abbrev Dbounded {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [QuillenExactCategory C]
    (D : BoundedDerivedInfinityCategory C) : Type (max u v) :=
  D.underlying

/-- Checked abelian-category comparison target provided by mathlib. -/
abbrev abelianDerivedCategory (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : Type (max u v) :=
  DerivedCategory C

end LeanLCAExactChallenge
