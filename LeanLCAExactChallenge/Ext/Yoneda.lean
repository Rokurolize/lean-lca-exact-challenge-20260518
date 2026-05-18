import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Ext frontier.

Mathlib currently provides derived-category Ext groups for abelian categories.
This file exposes a checked wrapper around that API.  Ext groups for a general
Quillen exact category remain a recorded source patch.
-/

set_option autoImplicit false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory

/-- Checked Yoneda-Ext frontier using mathlib's abelian-category Ext API. -/
abbrev YonedaExt {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (X Y : C) (n : ℕ) : Type w :=
  Abelian.Ext X Y n

namespace YonedaExt

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {X Y : C} {n : ℕ}

/-- Degree-zero Ext is equivalent to the hom type in the abelian-category frontier. -/
noncomputable def zero_equiv_hom : YonedaExt (C := C) X Y 0 ≃ (X ⟶ Y) :=
  Abelian.Ext.homEquiv₀

/-- Baer sum in the checked abelian-category frontier. -/
noncomputable def baer_sum (a b : YonedaExt (C := C) X Y n) : YonedaExt (C := C) X Y n :=
  a + b

/-- The checked additive group structure inherited from mathlib's Ext API. -/
noncomputable instance instAddCommGroup :
    AddCommGroup (YonedaExt (C := C) X Y n) :=
  Abelian.Ext.instAddCommGroup

end YonedaExt

end LeanLCAExactChallenge
