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
  /-- Composites of inflations remain inflations. -/
  comp_inflation {X Y Z : C} {i : X ⟶ Y} {j : Y ⟶ Z} :
    (∃ (Zi : C) (gi : Y ⟶ Zi) (zeroi : i ≫ gi = 0),
      Conflation (ShortComplex.mk i gi zeroi)) →
    (∃ (Zj : C) (gj : Z ⟶ Zj) (zeroj : j ≫ gj = 0),
      Conflation (ShortComplex.mk j gj zeroj)) →
    ∃ (Zij : C) (gij : Z ⟶ Zij) (zeroij : (i ≫ j) ≫ gij = 0),
      Conflation (ShortComplex.mk (i ≫ j) gij zeroij)
  /-- Composites of deflations remain deflations. -/
  comp_deflation {X Y Z : C} {p : X ⟶ Y} {q : Y ⟶ Z} :
    (∃ (Wp : C) (fp : Wp ⟶ X) (zerop : fp ≫ p = 0),
      Conflation (ShortComplex.mk fp p zerop)) →
    (∃ (Wq : C) (fq : Wq ⟶ Y) (zeroq : fq ≫ q = 0),
      Conflation (ShortComplex.mk fq q zeroq)) →
    ∃ (Wpq : C) (fpq : Wpq ⟶ X) (zeropq : fpq ≫ (p ≫ q) = 0),
      Conflation (ShortComplex.mk fpq (p ≫ q) zeropq)

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

/-- Composites preserve the first-class inflation predicate. -/
theorem inflation_comp {X Y Z : C} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : inflation i) (hj : inflation j) : inflation (i ≫ j) :=
  QuillenExactCategory.comp_inflation hi hj

/-- Composites preserve the first-class deflation predicate. -/
theorem deflation_comp {X Y Z : C} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : deflation p) (hq : deflation q) : deflation (p ≫ q) :=
  QuillenExactCategory.comp_deflation hp hq

/-- Pushouts preserve the first-class inflation predicate. -/
theorem pushout_inflation_of_inflation {X Y : C} {i : X ⟶ Y}
    (hi : inflation i) {Y' : C} (a : X ⟶ Y') [HasPushout i a] :
    inflation (pushout.inr i a) := by
  rcases hi with ⟨Z, g, zero, hS⟩
  simpa [inflation] using
    (QuillenExactCategory.pushout_inflation
      (S := ShortComplex.mk i g zero) hS (Y := Y') a)

/-- Pullbacks preserve the first-class deflation predicate. -/
theorem pullback_deflation_of_deflation {X Y : C} {p : X ⟶ Y}
    (hp : deflation p) {Y' : C} (a : Y' ⟶ Y) [HasPullback a p] :
    deflation (pullback.fst a p) := by
  rcases hp with ⟨W, f, zero, hS⟩
  simpa [deflation] using
    (QuillenExactCategory.pullback_deflation
      (S := ShortComplex.mk f p zero) hS (Y := Y') a)

end QuillenExactCategory

end LeanLCAExactChallenge
