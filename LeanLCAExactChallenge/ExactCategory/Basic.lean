import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
Compile-checked interface for Quillen-style exact categories.

This local interface is instantiated by strict metrizable LCA sequences in
`LCA.ExactCategory`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/-- A local Quillen exact-category interface over a preadditive category. -/
class QuillenExactCategory (C : Type u) [Category.{v} C] [Preadditive C] where
  /-- The distinguished kernel-cokernel pairs, represented as short complexes. -/
  Conflation : ShortComplex C → Prop
  /-- Conflations are invariant under isomorphism of short complexes. -/
  conflation_iso {S T : ShortComplex C} (e : S ≅ T) :
    Conflation S → Conflation T
  /-- Every split short complex is a conflation in the local interface. -/
  split_conflation (S : ShortComplex C) : S.Splitting → Conflation S
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

variable {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Transport a conflation across an isomorphism of short complexes. -/
theorem conflation_iso_transport {S T : ShortComplex C} (e : S ≅ T)
    (hS : QuillenExactCategory.Conflation S) :
    QuillenExactCategory.Conflation T :=
  QuillenExactCategory.conflation_iso e hS

/-- An inflation is the first map of a conflation. -/
def inflation {X Y : C} (i : X ⟶ Y) : Prop :=
  ∃ (Z : C) (g : Y ⟶ Z) (zero : i ≫ g = 0),
    QuillenExactCategory.Conflation (ShortComplex.mk i g zero)

/-- A deflation is the second map of a conflation. -/
def deflation {X Y : C} (p : X ⟶ Y) : Prop :=
  ∃ (W : C) (f : W ⟶ X) (zero : f ≫ p = 0),
    QuillenExactCategory.Conflation (ShortComplex.mk f p zero)

/-- The first map of a conflation is an inflation. -/
theorem inflation_of_conflation {S : ShortComplex C}
    (hS : QuillenExactCategory.Conflation S) : inflation S.f :=
  ⟨S.X₃, S.g, S.zero, hS⟩

/-- The second map of a conflation is a deflation. -/
theorem deflation_of_conflation {S : ShortComplex C}
    (hS : QuillenExactCategory.Conflation S) : deflation S.g :=
  ⟨S.X₁, S.f, S.zero, hS⟩

/-- Split short complexes are conflations. -/
theorem conflation_of_splitting (S : ShortComplex C) (hS : S.Splitting) :
    QuillenExactCategory.Conflation S :=
  QuillenExactCategory.split_conflation S hS

/-- The first map of a split short complex is an inflation. -/
theorem inflation_of_splitting (S : ShortComplex C) (hS : S.Splitting) :
    inflation S.f :=
  inflation_of_conflation (conflation_of_splitting S hS)

/-- The second map of a split short complex is a deflation. -/
theorem deflation_of_splitting (S : ShortComplex C) (hS : S.Splitting) :
    deflation S.g :=
  deflation_of_conflation (conflation_of_splitting S hS)

end QuillenExactCategory

end LeanLCAExactChallenge
