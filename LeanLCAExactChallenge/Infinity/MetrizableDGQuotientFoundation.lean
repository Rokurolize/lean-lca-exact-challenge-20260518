import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Object words for a corrected Drinfeld dg quotient

This file isolates the verified object-indexing part of a possible Drinfeld quotient of the dg
category of bounded metrizable complexes. A positive-length summand in a Drinfeld quotient Hom
complex is indexed by a finite word of objects in the dg subcategory being killed. Here that
subcategory is defined by the corrected cycle-object exact-acyclicity predicate.

No quotient carrier or localization claim is made in this file.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory

/-- Bounded metrizable complexes that the corrected derived localization must kill. -/
def CorrectedAcyclicObject : ObjectProperty ComplexCategory :=
  fun K ↦ exactAcyclicWithCycles MetrizableLCA.{0} K.obj

/-- The full dg-object subcategory to be killed by a corrected Drinfeld quotient. -/
abbrev CorrectedAcyclicComplexCategory : Type 1 :=
  CorrectedAcyclicObject.FullSubcategory

/-- A bar word indexing a summand of a Drinfeld quotient Hom complex from `X` to `Y`.

The `length` intermediate objects are required by their type to lie in the corrected acyclic
full subcategory. Length zero is the original, unlocalized Hom-complex summand.
-/
structure DrinfeldWord (X Y : ComplexCategory) where
  length : ℕ
  intermediate : Fin length → CorrectedAcyclicComplexCategory

namespace DrinfeldWord

open CategoryTheory.MonoidalCategory

/-- The length-zero word, indexing the original dg Hom complex. -/
def nil (X Y : ComplexCategory) : DrinfeldWord X Y where
  length := 0
  intermediate := Fin.elim0

/-- The one-letter word through a corrected acyclic object. -/
def singleton (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    DrinfeldWord X Y where
  length := 1
  intermediate := fun _ ↦ A

/-- Concatenation of the intermediate-object words.  The endpoint parameters are phantom at
this indexing layer; they become relevant when the tensor factors of a quotient Hom summand
are attached. -/
def append {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    DrinfeldWord X Z where
  length := w.length + v.length
  intermediate := Fin.addCases w.intermediate v.intermediate

@[simp]
theorem append_length {X Y Z : ComplexCategory}
    (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    (w.append v).length = w.length + v.length :=
  rfl

@[simp]
theorem singleton_length (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    (singleton X Y A).length = 1 :=
  rfl

/-- The underlying bounded complex at an intermediate position. -/
def object {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    ComplexCategory :=
  (w.intermediate i).obj

/-- The ordered vertices of a word, including its source and target endpoints. -/
def vertex {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    Fin (w.length + 2) → ComplexCategory :=
  Fin.cases X (Fin.lastCases Y w.object)

/-- Source vertex of the `i`-th ordinary Hom factor in a word summand. -/
def arrowSource {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin (w.length + 1)) : ComplexCategory :=
  w.vertex i.castSucc

/-- Target vertex of the `i`-th ordinary Hom factor in a word summand. -/
def arrowTarget {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin (w.length + 1)) : ComplexCategory :=
  w.vertex i.succ

@[simp]
theorem vertex_zero {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.vertex 0 = X :=
  rfl

@[simp]
theorem vertex_last {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.vertex (Fin.last (w.length + 1)) = Y := by
  change Fin.lastCases Y w.object (Fin.last w.length) = Y
  simp

/-- Degree choices for the tensor factors of a Drinfeld word summand.  Each inserted
contracting generator has cohomological degree `-1`, hence the total quotient degree is the
sum of the ordinary Hom degrees minus the word length. -/
structure DegreeProfile {X Y : ComplexCategory} (w : DrinfeldWord X Y) (n : ℤ) where
  arrowDegree : Fin (w.length + 1) → ℤ
  totalDegree : (∑ i, arrowDegree i) - w.length = n

/-- Degree profile of an internal-differential term: one ordinary Hom degree is raised by
one, so the total quotient degree is raised by one. -/
def DegreeProfile.raise {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : DegreeProfile w (n + 1) where
  arrowDegree j := d.arrowDegree j + if j = i then 1 else 0
  totalDegree := by
    rw [Finset.sum_add_distrib]
    have hi : (∑ j : Fin (w.length + 1), if j = i then (1 : ℤ) else 0) = 1 := by
      simp
    rw [hi]
    have hd := d.totalDegree
    omega

/-- The ordinary Hom-cochain module attached to one arrow of a degree-profiled word. -/
def factorModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).X
    (d.arrowDegree i)

/-- Right-associated tensor product of a finite list of integer modules. -/
def tensorModuleList : List (ModuleCat.{0} ℤ) → ModuleCat.{0} ℤ
  | [] => 𝟙_ (ModuleCat.{0} ℤ)
  | M :: Ms => M ⊗ tensorModuleList Ms

/-- The tensor-product module belonging to one word and one compatible degree profile. -/
def summandModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : ModuleCat.{0} ℤ :=
  tensorModuleList (List.ofFn (factorModule d))

/-- Index of a homogeneous summand of the corrected Drinfeld quotient. -/
abbrev GradedSummandIndex (X Y : ComplexCategory) (n : ℤ) :=
  Σ w : DrinfeldWord X Y, DegreeProfile w n

/-- A word summand lifted to the universe in which the family of all acyclic words is small. -/
def largeSummandModule {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1} ℤ).obj (summandModule s.2)

/-- The homogeneous carrier of the corrected Drinfeld quotient Hom complex.  This is the
actual coproduct over all acyclic words and all compatible allocations of ordinary Hom
degrees. -/
def quotientGradedModule (X Y : ComplexCategory) (n : ℤ) : ModuleCat.{1} ℤ :=
  ∐ fun s : GradedSummandIndex X Y n ↦ largeSummandModule s

@[simp]
theorem singleton_object (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton X Y A).length) : (singleton X Y A).object i = A.obj :=
  rfl

/-- Every intermediate object of a Drinfeld word is corrected exact-acyclic. -/
theorem object_exactAcyclicWithCycles {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) :
    exactAcyclicWithCycles MetrizableLCA.{0} (w.object i).obj :=
  (w.intermediate i).property

/-- A word with no intermediate objects is uniquely the length-zero word. -/
theorem eq_nil_of_length_eq_zero {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (h : w.length = 0) : w = nil X Y := by
  cases w with
  | mk n intermediate =>
      change n = 0 at h
      subst n
      congr
      funext i
      exact Fin.elim0 i

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
