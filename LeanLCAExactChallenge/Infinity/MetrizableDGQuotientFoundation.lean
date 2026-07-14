import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Logic.Equiv.Fin.Basic

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
open scoped TensorProduct

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
abbrev singleton (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
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

/-- Remove one intermediate acyclic object.  These are the target words of the contraction
terms in the Drinfeld differential. -/
def eraseIntermediate {X Y : ComplexCategory} :
    (w : DrinfeldWord X Y) → Fin w.length → DrinfeldWord X Y
  | ⟨0, _⟩, i => Fin.elim0 i
  | ⟨1, _⟩, _ => nil X Y
  | ⟨k + 2, intermediate⟩, i =>
      { length := k + 1
        intermediate := fun j ↦ intermediate (i.succAbove j) }

@[simp]
theorem eraseIntermediate_length {X Y : ComplexCategory}
    (w : DrinfeldWord X Y) (i : Fin w.length) :
    (eraseIntermediate w i).length + 1 = w.length := by
  cases w with
  | mk n intermediate =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k <;> rfl

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

/-- Adjacent arrow factors meet at the same intermediate vertex. -/
theorem arrowTarget_castSucc_eq_arrowSource_succ {X Y : ComplexCategory}
    (w : DrinfeldWord X Y) (i : Fin w.length) :
    w.arrowTarget i.castSucc = w.arrowSource i.succ := by
  unfold arrowTarget arrowSource
  congr 1

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

@[ext]
theorem DegreeProfile.ext {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    {d e : DegreeProfile w n} (h : d.arrowDegree = e.arrowDegree) : d = e := by
  cases d
  cases e
  cases h
  rfl

/-- Transport a degree profile along an equality of endpoint-compatible words. -/
def DegreeProfile.castWord {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    {n : ℤ} (h : w = v) (d : DegreeProfile w n) : DegreeProfile v n := by
  subst h
  exact d

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

theorem DegreeProfile.raise_comm {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) :
    (d.raise i).raise j = (d.raise j).raise i := by
  apply DegreeProfile.ext
  funext q
  simp only [DegreeProfile.raise]
  by_cases hqi : q = i <;> by_cases hqj : q = j <;> simp [hqi, hqj] <;> ring

/-- Merge the two ordinary Hom degrees adjacent to an intermediate object.  The chosen
`succAbove` enumeration omits the left factor and adds its degree to the surviving right
factor. -/
def contractedArrowDegree {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) : Fin k → ℤ :=
  fun j ↦ a (i.castSucc.succAbove j) + if j = i then a i.castSucc else 0

theorem contractedArrowDegree_raise_succAbove {k : ℕ}
    (a : Fin (k + 1) → ℤ) (i q : Fin k) :
    contractedArrowDegree
        (fun j ↦ a j + if j = i.castSucc.succAbove q then 1 else 0) i =
      fun r ↦ contractedArrowDegree a i r + if r = q then 1 else 0 := by
  funext r
  by_cases hrq : r = q
  · subst r
    simp [contractedArrowDegree, Fin.ne_succAbove]
    ring
  · have hsucc : i.castSucc.succAbove r ≠ i.castSucc.succAbove q := by
      exact fun h ↦ hrq (Fin.succAbove_right_injective h)
    simp [contractedArrowDegree, hrq, hsucc, Fin.ne_succAbove]

theorem contractedArrowDegree_raise_left {k : ℕ}
    (a : Fin (k + 1) → ℤ) (i : Fin k) :
    contractedArrowDegree
        (fun j ↦ a j + if j = i.castSucc then 1 else 0) i =
      fun r ↦ contractedArrowDegree a i r + if r = i then 1 else 0 := by
  funext r
  by_cases hri : r = i
  · subst r
    have hne : i.succ ≠ i.castSucc := by
      exact (Fin.ne_of_lt i.castSucc_lt_succ).symm
    simp [contractedArrowDegree, hne]
    ring
  · simp [contractedArrowDegree, hri]

theorem sum_contractedArrowDegree {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) :
    ∑ j, contractedArrowDegree a i j = ∑ j, a j := by
  rw [show (∑ j, contractedArrowDegree a i j) =
      (∑ j, a (i.castSucc.succAbove j)) +
        ∑ j, (if j = i then a i.castSucc else 0) by
    simp only [contractedArrowDegree, Finset.sum_add_distrib]]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fin.sum_univ_succAbove a i.castSucc]
  exact add_comm _ _

theorem sum_filter_contractedArrowDegree_gt_of_lt {k : ℕ}
    (a : Fin (k + 1) → ℤ) (i q : Fin k) (hqi : q < i) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin k ↦ q < r), contractedArrowDegree a i r =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) ↦ q.castSucc < j), a j := by
  let b : Fin (k + 1) → ℤ := fun j ↦ if q.castSucc < j then a j else 0
  have hsucc (r : Fin k) :
      q.castSucc < i.castSucc.succAbove r ↔ q < r := by
    rw [← Fin.succAbove_of_castSucc_lt i.castSucc q hqi]
    exact Fin.succAbove_lt_succAbove_iff
  calc
    ∑ r ∈ Finset.univ.filter (fun r : Fin k ↦ q < r), contractedArrowDegree a i r =
        ∑ r, if q < r then contractedArrowDegree a i r else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ r, contractedArrowDegree b i r := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hqr : q < r
      · simp [contractedArrowDegree, b, hqr, (hsucc r).2 hqr, hqi]
      · have hfirst : ¬q.castSucc < i.castSucc.succAbove r :=
          fun h ↦ hqr ((hsucc r).1 h)
        have hri : r ≠ i := by
          intro hri
          subst r
          exact hqr hqi
        simp [contractedArrowDegree, b, hqr, hfirst, hri]
    _ = ∑ j, b j := sum_contractedArrowDegree b i
    _ = ∑ j ∈ Finset.univ.filter
        (fun j : Fin (k + 1) ↦ q.castSucc < j), a j := by
      rw [Finset.sum_filter]

theorem sum_filter_contractedArrowDegree_gt_of_le {k : ℕ}
    (a : Fin (k + 1) → ℤ) (i q : Fin k) (hiq : i ≤ q) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin k ↦ q < r), contractedArrowDegree a i r =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (k + 1) ↦ q.succ < j), a j := by
  let b : Fin (k + 1) → ℤ := fun j ↦ if q.succ < j then a j else 0
  have hsucc (r : Fin k) : q.succ < i.castSucc.succAbove r ↔ q < r := by
    rw [← Fin.succAbove_of_le_castSucc i.castSucc q hiq]
    exact Fin.succAbove_lt_succAbove_iff
  calc
    ∑ r ∈ Finset.univ.filter (fun r : Fin k ↦ q < r), contractedArrowDegree a i r =
        ∑ r, if q < r then contractedArrowDegree a i r else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ r, contractedArrowDegree b i r := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hqr : q < r
      · have hri : r ≠ i := by
          intro hri
          subst r
          exact (not_lt_of_ge hiq) hqr
        simp [contractedArrowDegree, b, hqr, (hsucc r).2 hqr, hri]
      · have hfirst : ¬q.succ < i.castSucc.succAbove r :=
          fun h ↦ hqr ((hsucc r).1 h)
        have hleft : ¬q.succ < i.castSucc := by
          intro h
          change q.val + 1 < i.val at h
          omega
        simp [contractedArrowDegree, b, hqr, hfirst, hleft]
    _ = ∑ j, b j := sum_contractedArrowDegree b i
    _ = ∑ j ∈ Finset.univ.filter
        (fun j : Fin (k + 1) ↦ q.succ < j), a j := by
      rw [Finset.sum_filter]

/-- At the surviving contraction index, the new arrow degree is the sum of
the two adjacent original arrow degrees. -/
theorem contractedArrowDegree_self {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) :
    contractedArrowDegree a i i = a i.succ + a i.castSucc := by
  simp [contractedArrowDegree]

/-- Degree profile of the contraction term at an intermediate object.  Merging two adjacent
ordinary Hom factors preserves their degree sum, while deleting one degree-`-1` contracting
generator raises the total quotient degree by one. -/
def DegreeProfile.contract {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    DegreeProfile (eraseIntermediate w i) (n + 1) where
  arrowDegree j := contractedArrowDegree d.arrowDegree i
    (Fin.cast (eraseIntermediate_length w i) j)
  totalDegree := by
    have hs : (∑ j, contractedArrowDegree d.arrowDegree i
          (Fin.cast (eraseIntermediate_length w i) j)) =
        ∑ j, contractedArrowDegree d.arrowDegree i j := by
      apply Fintype.sum_equiv (finCongr (eraseIntermediate_length w i))
      intro j
      rfl
    rw [hs]
    rw [sum_contractedArrowDegree]
    have hd := d.totalDegree
    have hl := eraseIntermediate_length w i
    omega

/-- The ordinary Hom-cochain module attached to one arrow of a degree-profiled word. -/
def factorModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).X
    (d.arrowDegree i)

/-- Homogeneous composition of two adjacent factors before transporting its codomain to
the factor of the contracted word. -/
def adjacentFactorComposition {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) := by
  simp only [factorModule]
  exact dgCochainCompTensorOfEq
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
      (w.arrowSource i.succ) (w.arrowTarget i.succ)
      (arrowTarget_castSucc_eq_arrowSource_succ w i) rfl

def adjacentRightDifferentialPath {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1)) := by
  simp only [factorModule]
  exact
    (𝟙 ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).X
          (d.arrowDegree i.castSucc)) ⊗ₘ
      (dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).d
          (d.arrowDegree i.succ) (d.arrowDegree i.succ + 1)) ≫
    dgCochainCompTensorOfEq
      (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
      (w.arrowSource i.succ) (w.arrowTarget i.succ)
      (arrowTarget_castSucc_eq_arrowSource_succ w i) (by omega)

def adjacentLeftDifferentialPath {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) (i : Fin w.length) :
    Quiver.Hom (factorModule d i.castSucc ⊗ factorModule d i.succ)
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).X
          ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1)) := by
  simp only [factorModule]
  exact
    ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).d
          (d.arrowDegree i.castSucc) (d.arrowDegree i.castSucc + 1) ⊗ₘ
      𝟙 ((dgHomZModuleCochainComplex
        (w.arrowSource i.succ) (w.arrowTarget i.succ)).X
          (d.arrowDegree i.succ))) ≫
    dgCochainCompTensorOfEq
      (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
      (w.arrowSource i.succ) (w.arrowTarget i.succ)
      (arrowTarget_castSucc_eq_arrowSource_succ w i) (by omega)

theorem adjacentFactorComposition_comp_d {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) (i : Fin w.length) :
    adjacentFactorComposition d i ≫
        (dgHomZModuleCochainComplex
          (w.arrowSource i.castSucc) (w.arrowTarget i.succ)).d
            (d.arrowDegree i.castSucc + d.arrowDegree i.succ)
            ((d.arrowDegree i.castSucc + d.arrowDegree i.succ) + 1) =
      adjacentRightDifferentialPath d i +
        (d.arrowDegree i.succ).negOnePow • adjacentLeftDifferentialPath d i := by
  simp only [adjacentFactorComposition, adjacentRightDifferentialPath,
    adjacentLeftDifferentialPath, factorModule]
  exact dgCochainCompTensorOfEq_comp_d
    (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)
    (w.arrowSource i.succ) (w.arrowTarget i.succ)
    (arrowTarget_castSucc_eq_arrowSource_succ w i)
    (d.arrowDegree i.castSucc) (d.arrowDegree i.succ)

/-- The pointwise factor map contributing the internal differential at the chosen arrow;
all other tensor factors are identities. -/
def factorDifferential {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) :
    Quiver.Hom (factorModule d j) (factorModule (d.raise i) j) := by
  by_cases h : j = i
  · subst j
    exact (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).d
      (d.arrowDegree i) ((d.raise i).arrowDegree i)
  · have hdeg : (d.raise i).arrowDegree j = d.arrowDegree j := by
      simp [DegreeProfile.raise, h]
    rw [factorModule, factorModule, hdeg]
    exact 𝟙 _

theorem factorDifferential_self_comp {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    factorDifferential d i i ≫ factorDifferential (d.raise i) i i = 0 := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  exact (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).d_comp_d
    (d.arrowDegree i) ((d.raise i).arrowDegree i) (((d.raise i).raise i).arrowDegree i)

theorem factorDifferential_comm_heq_of_ne {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i j q : Fin (w.length + 1)) (hij : i ≠ j) :
    HEq (factorDifferential d i q ≫ factorDifferential (d.raise i) j q)
      (factorDifferential d j q ≫ factorDifferential (d.raise j) i q) := by
  by_cases hqi : q = i
  · subst q
    unfold factorDifferential
    have hdeg :
        (d.arrowDegree i + (if i = i then 1 else 0)) + (if i = j then 1 else 0) =
          (d.arrowDegree i + (if i = j then 1 else 0)) + (if i = i then 1 else 0) := by
      simp [hij]
    simpa [DegreeProfile.raise, factorModule, hij] using congr_arg_heq
      (fun r ↦ (dgHomZModuleCochainComplex
        (w.arrowSource i) (w.arrowTarget i)).d (d.arrowDegree i) r) hdeg
  · by_cases hqj : q = j
    · subst q
      unfold factorDifferential
      have hdeg :
          (d.arrowDegree j + (if j = i then 1 else 0)) + (if j = j then 1 else 0) =
            (d.arrowDegree j + (if j = j then 1 else 0)) + (if j = i then 1 else 0) := by
        simp [hqi]
      simpa [DegreeProfile.raise, factorModule, hqi] using congr_arg_heq
        (fun r ↦ (dgHomZModuleCochainComplex
          (w.arrowSource j) (w.arrowTarget j)).d (d.arrowDegree j) r) hdeg
    · unfold factorDifferential
      simpa [DegreeProfile.raise, factorModule, hqi, hqj] using
        ((eqToHom_heq_id_dom _ _ _).trans
          (eqToHom_heq_id_dom _ _ _).symm)

/-- A definitionally recursive list presentation of a finite family. -/
@[reducible]
def finFamilyList {α : Type*} : {k : ℕ} → (Fin k → α) → List α
  | 0, _ => []
  | k + 1, M => M 0 :: finFamilyList (fun i : Fin k ↦ M i.succ)

theorem finFamilyList_eq_ofFn {α : Type*} {k : ℕ} (M : Fin k → α) :
    finFamilyList M = List.ofFn M := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.ofFn_succ]
      exact congrArg (M 0 :: ·) (ih (fun i : Fin k ↦ M i.succ))

/-- Right-associated tensor product of a finite list of modules. -/
def tensorModuleListOver (R : Type) [CommRing R] :
    List (ModuleCat.{0} R) → ModuleCat.{0} R
  | [] => 𝟙_ (ModuleCat.{0} R)
  | M :: Ms => M ⊗ tensorModuleListOver R Ms

/-- Right-associated tensor product of a finite list of integer modules. -/
abbrev tensorModuleList := tensorModuleListOver ℤ

/-- Pointwise morphisms between two lists of tensor factors. -/
inductive TensorMapData :
    (source target : List (ModuleCat.{0} ℤ)) → Type 1
  | nil : TensorMapData [] []
  | cons {M N : ModuleCat.{0} ℤ} {Ms Ns : List (ModuleCat.{0} ℤ)}
      (f : Quiver.Hom M N) (fs : TensorMapData Ms Ns) :
      TensorMapData (M :: Ms) (N :: Ns)

def TensorMapData.comp : {source middle target : List (ModuleCat.{0} ℤ)} →
    TensorMapData source middle → TensorMapData middle target →
      TensorMapData source target
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons f fs, .cons g gs =>
      .cons (f ≫ g) (TensorMapData.comp fs gs)

/-- Assemble pointwise maps indexed by a finite ordinal into tensor-map data. -/
def TensorMapData.ofFn : {k : ℕ} →
    (M N : Fin k → ModuleCat.{0} ℤ) →
    ((i : Fin k) → Quiver.Hom (M i) (N i)) →
    TensorMapData (finFamilyList M) (finFamilyList N)
  | 0, _, _, _ => .nil
  | k + 1, M, N, f => .cons (f 0) (TensorMapData.ofFn
      (fun i : Fin k ↦ M i.succ) (fun i : Fin k ↦ N i.succ)
      (fun i ↦ f i.succ))

/-- Tensor a pointwise list of module morphisms. -/
def TensorMapData.tensorMap : {source target : List (ModuleCat.{0} ℤ)} →
    TensorMapData source target →
      Quiver.Hom (tensorModuleList source) (tensorModuleList target)
  | [], [], .nil =>
      (𝟙 (tensorModuleList []) :
        Quiver.Hom (tensorModuleList []) (tensorModuleList []))
  | M :: Ms, N :: Ns, @TensorMapData.cons _ _ _ _ f fs =>
      MonoidalCategoryStruct.tensorHom
        (C := ModuleCat.{0} ℤ)
        (X₁ := M) (Y₁ := N)
        (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ns)
        f fs.tensorMap

@[simp]
theorem TensorMapData.tensorMap_comp
    {source middle target : List (ModuleCat.{0} ℤ)}
    (f : TensorMapData source middle) (g : TensorMapData middle target) :
    f.tensorMap ≫ g.tensorMap = (f.comp g).tensorMap := by
  induction f generalizing target with
  | nil =>
      cases g
      simp [TensorMapData.tensorMap, TensorMapData.comp]
  | cons f fs ih =>
      cases g with
      | cons g gs =>
          simp only [TensorMapData.tensorMap, TensorMapData.comp]
          change (f ⊗ₘ fs.tensorMap) ≫ (g ⊗ₘ gs.tensorMap) =
            (f ≫ g) ⊗ₘ (fs.comp gs).tensorMap
          rw [MonoidalCategory.tensorHom_comp_tensorHom, ih gs]

theorem TensorMapData.ofFn_tensorMap_comp_eq_zero_of_component
    {k : ℕ} (M N P : Fin k → ModuleCat.{0} ℤ)
    (f : (i : Fin k) → M i ⟶ N i) (g : (i : Fin k) → N i ⟶ P i)
    (i : Fin k) (hi : f i ≫ g i = 0) :
    (TensorMapData.ofFn M N f).tensorMap ≫
        (TensorMapData.ofFn N P g).tensorMap = 0 := by
  rw [TensorMapData.tensorMap_comp]
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      cases i using Fin.cases with
      | zero =>
          simp only [TensorMapData.ofFn, TensorMapData.comp,
            TensorMapData.tensorMap]
          rw [hi]
          simp
          rfl
      | succ i =>
          simp only [TensorMapData.ofFn, TensorMapData.comp,
            TensorMapData.tensorMap]
          rw [ih (fun j : Fin k ↦ M j.succ) (fun j : Fin k ↦ N j.succ)
            (fun j : Fin k ↦ P j.succ) (fun j ↦ f j.succ)
            (fun j ↦ g j.succ) i hi]
          simp
          rfl

theorem TensorMapData.ofFn_tensorMap_comp_heq_of_pointwise
    {k : ℕ} (M N₁ P N₂ : Fin k → ModuleCat.{0} ℤ)
    (f₁ : (i : Fin k) → M i ⟶ N₁ i) (g₁ : (i : Fin k) → N₁ i ⟶ P i)
    (f₂ : (i : Fin k) → M i ⟶ N₂ i) (g₂ : (i : Fin k) → N₂ i ⟶ P i)
    (h : ∀ i, HEq (f₁ i ≫ g₁ i) (f₂ i ≫ g₂ i)) :
    (TensorMapData.ofFn M N₁ f₁).tensorMap ≫
        (TensorMapData.ofFn N₁ P g₁).tensorMap
      = (TensorMapData.ofFn M N₂ f₂).tensorMap ≫
        (TensorMapData.ofFn N₂ P g₂).tensorMap := by
  simp only [TensorMapData.tensorMap_comp]
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [TensorMapData.ofFn, TensorMapData.comp,
        TensorMapData.tensorMap]
      have hhead := h 0
      have htail := ih (fun i : Fin k ↦ M i.succ)
        (fun i : Fin k ↦ N₁ i.succ) (fun i : Fin k ↦ P i.succ)
        (fun i : Fin k ↦ N₂ i.succ)
        (fun i ↦ f₁ i.succ) (fun i ↦ g₁ i.succ)
        (fun i ↦ f₂ i.succ) (fun i ↦ g₂ i.succ) (fun i ↦ h i.succ)
      rw [eq_of_heq hhead, htail]

theorem TensorMapData.ofFn_tensorMap_comp_heq_of_pointwise_of_target_eq
    {k : ℕ} (M N₁ P₁ N₂ P₂ : Fin k → ModuleCat.{0} ℤ)
    (f₁ : (i : Fin k) → M i ⟶ N₁ i) (g₁ : (i : Fin k) → N₁ i ⟶ P₁ i)
    (f₂ : (i : Fin k) → M i ⟶ N₂ i) (g₂ : (i : Fin k) → N₂ i ⟶ P₂ i)
    (hP : P₁ = P₂) (h : ∀ i, HEq (f₁ i ≫ g₁ i) (f₂ i ≫ g₂ i)) :
    HEq ((TensorMapData.ofFn M N₁ f₁).tensorMap ≫
        (TensorMapData.ofFn N₁ P₁ g₁).tensorMap)
      ((TensorMapData.ofFn M N₂ f₂).tensorMap ≫
        (TensorMapData.ofFn N₂ P₂ g₂).tensorMap) := by
  subst P₂
  apply heq_of_eq
  exact TensorMapData.ofFn_tensorMap_comp_heq_of_pointwise
    M N₁ P₁ N₂ f₁ g₁ f₂ g₂ h

/-- Data for replacing two adjacent tensor factors by one factor. -/
inductive AdjacentMergeData :
    (source target : List (ModuleCat.{0} ℤ)) → Type 1
  | head {M N P : ModuleCat.{0} ℤ} {Ms : List (ModuleCat.{0} ℤ)}
      (f : Quiver.Hom (M ⊗ N) P) :
      AdjacentMergeData (M :: N :: Ms) (P :: Ms)
  | tail {M : ModuleCat.{0} ℤ} {Ms Ns : List (ModuleCat.{0} ℤ)}
      (f : AdjacentMergeData Ms Ns) :
      AdjacentMergeData (M :: Ms) (M :: Ns)

/-- Tensor morphism induced by an adjacent merge. -/
def AdjacentMergeData.tensorMap : {source target : List (ModuleCat.{0} ℤ)} →
    AdjacentMergeData source target →
      Quiver.Hom (tensorModuleList source) (tensorModuleList target)
  | _, _, @AdjacentMergeData.head M N P Ms f =>
      (α_ M N (tensorModuleList Ms)).inv ≫
        MonoidalCategoryStruct.tensorHom
          (C := ModuleCat.{0} ℤ)
          (X₁ := M ⊗ N) (Y₁ := P)
          (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ms)
          f (𝟙 _)
  | _, _, @AdjacentMergeData.tail M Ms Ns f =>
      MonoidalCategoryStruct.tensorHom
        (C := ModuleCat.{0} ℤ)
        (X₁ := M) (Y₁ := M)
        (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ns)
        (𝟙 _) f.tensorMap

inductive AdjacentMergeNaturality :
    {source target source' target' : List (ModuleCat.{0} ℤ)} →
      (f : AdjacentMergeData source target) →
      (f' : AdjacentMergeData source' target') →
      TensorMapData source source' → TensorMapData target target' → Prop
  | head {M N P M' N' P' : ModuleCat.{0} ℤ}
      {Ms Ms' : List (ModuleCat.{0} ℤ)}
      (f : Quiver.Hom (M ⊗ N) P) (f' : Quiver.Hom (M' ⊗ N') P')
      (a : Quiver.Hom M M') (b : Quiver.Hom N N') (c : Quiver.Hom P P')
      (tail : TensorMapData Ms Ms')
      (h : (a ⊗ₘ b) ≫ f' = f ≫ c) :
      AdjacentMergeNaturality (.head f) (.head f')
        (.cons a (.cons b tail)) (.cons c tail)
  | tail {M M' : ModuleCat.{0} ℤ}
      {source target source' target' : List (ModuleCat.{0} ℤ)}
      {f : AdjacentMergeData source target}
      {f' : AdjacentMergeData source' target'}
      {sourceMap : TensorMapData source source'}
      {targetMap : TensorMapData target target'}
      (a : Quiver.Hom M M')
      (h : AdjacentMergeNaturality f f' sourceMap targetMap) :
      AdjacentMergeNaturality (.tail f) (.tail f')
        (.cons a sourceMap) (.cons a targetMap)

theorem AdjacentMergeNaturality.tensorMap_comm :
    {source target source' target' : List (ModuleCat.{0} ℤ)} →
      {f : AdjacentMergeData source target} →
      {f' : AdjacentMergeData source' target'} →
      {sourceMap : TensorMapData source source'} →
      {targetMap : TensorMapData target target'} →
      AdjacentMergeNaturality f f' sourceMap targetMap →
      sourceMap.tensorMap ≫ f'.tensorMap =
        f.tensorMap ≫ targetMap.tensorMap
  | _, _, _, _, _, _, _, _, .head f f' a b c tailMap h => by
      simp only [TensorMapData.tensorMap, AdjacentMergeData.tensorMap,
        Category.assoc]
      dsimp only [tensorModuleList, tensorModuleListOver]
      slice_lhs 1 2 =>
        exact MonoidalCategory.associator_inv_naturality
          a b tailMap.tensorMap
      simp only [Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, h]
      simp
  | _, _, _, _, _, _, _, _, .tail a h => by
      simp only [TensorMapData.tensorMap, AdjacentMergeData.tensorMap]
      dsimp only [tensorModuleList, tensorModuleListOver]
      rw [MonoidalCategory.tensorHom_comp_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom, h.tensorMap_comm]
      simp

/-- The tensor-product module belonging to one word and one compatible degree profile. -/
abbrev summandModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : ModuleCat.{0} ℤ :=
  tensorModuleList (finFamilyList (factorModule d))

/-- Transport of a word gives the corresponding canonical identification of tensor
summands. -/
def summandModuleCastWordIso {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    {n : ℤ} (h : w = v) (d : DegreeProfile w n) :
    summandModule d ≅ summandModule (d.castWord h) := by
  subst h
  exact Iso.refl _

/-- The length-zero word summand is canonically the original homogeneous Hom module. -/
def nilSummandIsoOriginal (X Y : ComplexCategory) {n : ℤ}
    (d : DegreeProfile (nil X Y) n) :
    summandModule d ≅ (dgHomZModuleCochainComplex X Y).X n := by
  have hdeg : d.arrowDegree 0 = n := by
    have hd := d.totalDegree
    rw [Fin.sum_univ_succ] at hd
    simpa [nil] using hd
  have hsource : (nil X Y).arrowSource 0 = X := rfl
  have htarget : (nil X Y).arrowTarget 0 = Y := by
    change (nil X Y).vertex (0 : Fin 1).succ = Y
    exact vertex_last (nil X Y)
  have hfactor : factorModule d 0 = (dgHomZModuleCochainComplex X Y).X n := by
    simp only [factorModule]
    rw [hsource, htarget, hdeg]
  exact (ρ_ (factorModule d 0)) ≪≫
    eqToIso hfactor

/-- Canonical degree profile on the zero-length word. -/
def nilDegreeProfile (X Y : ComplexCategory) (n : ℤ) :
    DegreeProfile (nil X Y) n where
  arrowDegree _ := n
  totalDegree := by simp [nil]

theorem nilDegreeProfile_raise (X Y : ComplexCategory) (n : ℤ)
    (i : Fin ((nil X Y).length + 1)) :
    (nilDegreeProfile X Y n).raise i = nilDegreeProfile X Y (n + 1) := by
  apply DegreeProfile.ext
  funext j
  have hij : j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change i.val < 1 at hi
    change j.val < 1 at hj
    omega
  simp [DegreeProfile.raise, nilDegreeProfile, hij]

/-- Tensor map of an internal-differential summand before inserting the Koszul sign. -/
def internalDifferentialTensorMap {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    Quiver.Hom (summandModule d) (summandModule (d.raise i)) :=
  (TensorMapData.ofFn (factorModule d) (factorModule (d.raise i))
    (factorDifferential d i)).tensorMap

theorem internalDifferentialTensorMap_self_comp {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    internalDifferentialTensorMap d i ≫
      internalDifferentialTensorMap (d.raise i) i = 0 := by
  apply TensorMapData.ofFn_tensorMap_comp_eq_zero_of_component
    (factorModule d) (factorModule (d.raise i))
      (factorModule ((d.raise i).raise i)) (factorDifferential d i)
        (factorDifferential (d.raise i) i) i
  exact factorDifferential_self_comp d i

theorem internalDifferentialTensorMap_comm_heq_of_ne {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i j : Fin (w.length + 1)) (hij : i ≠ j) :
    HEq (internalDifferentialTensorMap d i ≫
        internalDifferentialTensorMap (d.raise i) j)
      (internalDifferentialTensorMap d j ≫
        internalDifferentialTensorMap (d.raise j) i) := by
  apply TensorMapData.ofFn_tensorMap_comp_heq_of_pointwise_of_target_eq
  · exact congrArg (fun e ↦ factorModule e) (d.raise_comm i j)
  · intro q
    exact factorDifferential_comm_heq_of_ne d i j q hij

/-- Index of a homogeneous summand of the corrected Drinfeld quotient. -/
abbrev GradedSummandIndex (X Y : ComplexCategory) (n : ℤ) :=
  Σ w : DrinfeldWord X Y, DegreeProfile w n

/-- A word summand lifted to the universe in which the family of all acyclic words is small. -/
abbrev largeSummandModule {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1} ℤ).obj (summandModule s.2)

@[simp]
theorem uliftFunctor_map_up {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (x : M) :
    ((ModuleCat.uliftFunctor.{1} ℤ).map f) (ULift.up x) = ULift.up (f x) :=
  rfl

/-- The homogeneous carrier of the corrected Drinfeld quotient Hom complex.  This is the
actual coproduct over all acyclic words and all compatible allocations of ordinary Hom
degrees. -/
abbrev quotientGradedModule (X Y : ComplexCategory) (n : ℤ) : ModuleCat.{1} ℤ :=
  ∐ fun s : GradedSummandIndex X Y n ↦ largeSummandModule s

/-- Inclusion of the original homogeneous Hom module as the zero-word summand of the
Drinfeld carrier (after the necessary universe lift). -/
def originalHomInclusion (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom
      ((ModuleCat.uliftFunctor.{1} ℤ).obj ((dgHomZModuleCochainComplex X Y).X n))
      (quotientGradedModule X Y n) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map
      (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
      ⟨nil X Y, nilDegreeProfile X Y n⟩

/-- One internal-differential term, included into the degree-`n+1` coproduct carrier.  The
Koszul coefficient is deliberately kept separate from this unsigned structural map. -/
def internalDifferentialLargeMap {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
      ⟨w, d.raise i⟩

/-- Total degree strictly preceding an arrow factor in the target-to-source DG word order. -/
def DegreeProfile.suffixTotal {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : ℤ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin (w.length + 1) ↦ i < j), d.arrowDegree j) -
    (w.length - i.val)

/-- The Koszul sign of the internal differential on the `i`-th arrow factor. -/
def DegreeProfile.internalSign {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) : ℤ :=
  if Even (d.suffixTotal i) then 1 else -1

def DegreeProfile.contractionSuffix {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin w.length) : ℤ :=
  (∑ j ∈ Finset.univ.filter
      (fun j : Fin (w.length + 1) ↦ i.val < j.val), d.arrowDegree j) -
    (w.length - (i.val + 1))

/-- Koszul sign of the contraction at the `i`-th degree-`-1` symbol in target-to-source order. -/
def DegreeProfile.contractionSign {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin w.length) : ℤ :=
  if Even (d.contractionSuffix i) then 1 else -1

/-- Sum of all signed internal-differential terms leaving one homogeneous word summand. -/
def internalDifferentialFromSummand {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  ∑ i, d.internalSign i • internalDifferentialLargeMap d i

/-- The internal-Hom part of the Drinfeld differential on the whole coproduct carrier. -/
def quotientInternalDifferential (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y (n + 1)) :=
  Limits.Sigma.desc fun s : GradedSummandIndex X Y n ↦
    internalDifferentialFromSummand s.2

@[reassoc (attr := simp)]
theorem quotientInternalDifferential_inclusion (X Y : ComplexCategory) (n : ℤ)
    (s : GradedSummandIndex X Y n) :
    Limits.Sigma.ι (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        quotientInternalDifferential X Y n =
      internalDifferentialFromSummand s.2 :=
  Limits.Sigma.ι_desc _ s

/-- An internal summand followed by the internal differential expands at the raised profile. -/
@[reassoc]
theorem internalDifferentialLargeMap_comp_internalDifferential
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) :
    internalDifferentialLargeMap d i ≫ quotientInternalDifferential X Y (n + 1) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
        internalDifferentialFromSummand (d.raise i) := by
  simp only [internalDifferentialLargeMap, Category.assoc]
  rw [quotientInternalDifferential_inclusion X Y (n + 1) ⟨w, d.raise i⟩]

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

@[simp]
theorem eraseIntermediate_singleton (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton X Y A).length) :
    eraseIntermediate (singleton X Y A) i = nil X Y := rfl

/-- The two arrow degrees of a one-letter word add to one more than its quotient degree. -/
theorem singleton_arrowDegree_sum (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    d.arrowDegree 0 + d.arrowDegree 1 = n + 1 := by
  have hd := d.totalDegree
  rw [Fin.sum_univ_succ] at hd
  have htail : (∑ j : Fin 1, d.arrowDegree j.succ) = d.arrowDegree 1 := by
    rw [Fin.sum_univ_succ]
    simp
  change d.arrowDegree 0 + (∑ j : Fin 1, d.arrowDegree j.succ) - 1 = n at hd
  rw [htail] at hd
  omega

/-- Identify a contracted one-letter summand with the exact homogeneous target used by
adjacent composition. -/
def singletonContractedSummandIsoAdjacentTarget (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    summandModule (d.contract i) ≅
      ((dgHomZModuleCochainComplex
        ((singleton X Y A).arrowSource i.castSucc)
        ((singleton X Y A).arrowTarget i.succ)).X
          (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) := by
  let i₀ : Fin (singleton X Y A).length := ⟨0, by simp⟩
  have hi : i = i₀ := Fin.ext (by simp [i₀])
  subst i
  have hfactor : factorModule (d.contract i₀) 0 =
      ((dgHomZModuleCochainComplex
        ((singleton X Y A).arrowSource i₀.castSucc)
        ((singleton X Y A).arrowTarget i₀.succ)).X
          (d.arrowDegree i₀.castSucc + d.arrowDegree i₀.succ)) := by
    simp [factorModule, DegreeProfile.contract, contractedArrowDegree,
      arrowSource, arrowTarget, vertex, singleton, i₀, add_comm]
    rfl
  exact (ρ_ (factorModule (d.contract i₀) 0)) ≪≫ eqToIso hfactor

/-- A contracted one-letter summand is canonically the nil-word original Hom summand in
degree one higher. -/
def singletonContractedSummandIsoOriginal (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    summandModule (d.contract i) ≅ (dgHomZModuleCochainComplex X Y).X (n + 1) := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  exact nilSummandIsoOriginal X Y (d.contract 0)

/-- Identify the adjacent-composition target with the original Hom module through the
canonical contracted summand, making the comparison triangle commute by construction. -/
def singletonAdjacentTargetIsoOriginal (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    ((dgHomZModuleCochainComplex
      ((singleton X Y A).arrowSource i.castSucc)
      ((singleton X Y A).arrowTarget i.succ)).X
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) ≅
      (dgHomZModuleCochainComplex X Y).X (n + 1) :=
  (singletonContractedSummandIsoAdjacentTarget X Y A d i).symm ≪≫
    singletonContractedSummandIsoOriginal X Y A d i

/-- Direct homogeneous identification of the adjacent target with the original Hom module. -/
def singletonAdjacentTargetIsoOriginalDirect (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    ((dgHomZModuleCochainComplex
      ((singleton X Y A).arrowSource i.castSucc)
      ((singleton X Y A).arrowTarget i.succ)).X
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ)) ≅
      (dgHomZModuleCochainComplex X Y).X (n + 1) := by
  let i₀ : Fin (singleton X Y A).length := ⟨0, by simp⟩
  have hi : i = i₀ := Fin.ext (by simp [i₀])
  subst i
  apply eqToIso
  have hs : (singleton X Y A).arrowSource i₀.castSucc = X := rfl
  have ht : (singleton X Y A).arrowTarget i₀.succ = Y :=
    vertex_last (singleton X Y A)
  rw [hs, ht]
  exact congrArg (fun z ↦ (dgHomZModuleCochainComplex X Y).X z)
    (singleton_arrowDegree_sum X Y A d)

theorem singletonAdjacentTargetIsoOriginal_eq_direct (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    singletonAdjacentTargetIsoOriginal X Y A d i =
      singletonAdjacentTargetIsoOriginalDirect X Y A d i := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  apply Iso.ext
  unfold singletonAdjacentTargetIsoOriginal
    singletonAdjacentTargetIsoOriginalDirect
    singletonContractedSummandIsoAdjacentTarget
    singletonContractedSummandIsoOriginal nilSummandIsoOriginal
  simp only [singleton_length, Fin.isValue, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, eraseIntermediate_singleton, Fin.zero_eta,
    Iso.trans_symm, Fin.cases_zero, Iso.trans_assoc, Iso.trans_hom,
    Iso.symm_hom, eqToIso.inv, eqToIso.hom]
  slice_lhs 2 3 =>
    exact (ρ_ (factorModule (d.contract 0) 0)).inv_hom_id
  slice_lhs 1 2 =>
    exact Category.comp_id _
  slice_lhs 1 2 =>
    exact eqToHom_trans _ _

/-- Reassociate a one-letter word summand to the binary tensor on which homogeneous
composition is defined. -/
def singletonSummandIsoTensor (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    summandModule d ≅ factorModule d 0 ⊗ factorModule d 1 := by
  change factorModule d 0 ⊗ (factorModule d 1 ⊗ 𝟙_ (ModuleCat.{0} ℤ)) ≅ _
  exact (α_ (factorModule d 0) (factorModule d 1) (𝟙_ (ModuleCat.{0} ℤ))).symm ≪≫
    ρ_ (factorModule d 0 ⊗ factorModule d 1)

/-- Reassociate a one-letter word at its actual contraction position. -/
def singletonSummandIsoTensorAt (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    summandModule d ≅ factorModule d i.castSucc ⊗ factorModule d i.succ := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  exact singletonSummandIsoTensor X Y A d

/-- The genuine contraction term for a one-letter word. -/
def singletonContractionTensorMap (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    Quiver.Hom (summandModule d) (summandModule (d.contract i)) := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  exact (singletonSummandIsoTensor X Y A d).hom ≫
    adjacentFactorComposition d 0 ≫
    (singletonContractedSummandIsoAdjacentTarget X Y A d 0).inv

/-- The signed singleton contraction included into the degree-`n+1` quotient carrier. -/
def singletonContractionLargeMap (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    Quiver.Hom
      (largeSummandModule
        (⟨singleton X Y A, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  d.contractionSign i •
    ((ModuleCat.uliftFunctor.{1} ℤ).map
        (singletonContractionTensorMap X Y A d i) ≫
      Limits.Sigma.ι
        (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
        ⟨eraseIntermediate (singleton X Y A) i, d.contract i⟩)

/-- The degree-zero identity cochain. -/
def identityCochain (K : ComplexCategory) :
    (dgHomZModuleCochainComplex K K).X 0 :=
  CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj)

/-- The degree profile of the formal contracting generator through one acyclic object. -/
def singletonContractingDegreeProfile (A : CorrectedAcyclicComplexCategory) :
    DegreeProfile (singleton A.obj A.obj A) (-1) where
  arrowDegree _ := 0
  totalDegree := by simp [singleton]

@[simp]
theorem singletonContractingDegreeProfile_contractionSign
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton A.obj A.obj A).length) :
    (singletonContractingDegreeProfile A).contractionSign i = 1 := by
  change Fin 1 at i
  have hi : i = (0 : Fin 1) := by
    apply Fin.ext
    have h := i.isLt
    omega
  rw [hi]
  simp [DegreeProfile.contractionSign, DegreeProfile.contractionSuffix,
    singletonContractingDegreeProfile]

/-- The unique contraction position of a one-letter word. -/
abbrev singletonIndex (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    Fin (singleton X Y A).length := ⟨0, by simp⟩

/-- The formal degree-`-1` contracting element before universe lift and coproduct inclusion. -/
def singletonContractingElement (A : CorrectedAcyclicComplexCategory) :
    summandModule (singletonContractingDegreeProfile A) := by
  exact (singletonSummandIsoTensor A.obj A.obj A
    (singletonContractingDegreeProfile A)).inv
      (identityCochain A.obj ⊗ₜ[ℤ] identityCochain A.obj)

/-- The formal contracting element as an element of the full quotient carrier. -/
def quotientContractingElement (A : CorrectedAcyclicComplexCategory) :
    quotientGradedModule A.obj A.obj (-1) :=
  Limits.Sigma.ι
      (fun s : GradedSummandIndex A.obj A.obj (-1) ↦ largeSummandModule s)
      ⟨singleton A.obj A.obj A, singletonContractingDegreeProfile A⟩
    (ULift.up (singletonContractingElement A))

/-- Reassociating the formal contracting element recovers its defining identity tensor. -/
theorem singletonSummandIsoTensorAt_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (singletonSummandIsoTensor A.obj A.obj A
      (singletonContractingDegreeProfile A)).hom
        (singletonContractingElement A) =
      identityCochain A.obj ⊗ₜ[ℤ] identityCochain A.obj := by
  unfold singletonContractingElement
  change ((singletonSummandIsoTensor A.obj A.obj A
      (singletonContractingDegreeProfile A)).inv ≫
        (singletonSummandIsoTensor A.obj A.obj A
          (singletonContractingDegreeProfile A)).hom).hom
      (identityCochain A.obj ⊗ₜ[ℤ] identityCochain A.obj) = _
  rw [Iso.inv_hom_id]
  rfl

/-- Contracting the formal one-letter generator gives the identity cochain. -/
theorem singletonContractionTensorMap_contractingElement
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton A.obj A.obj A).length) :
    (singletonContractedSummandIsoOriginal A.obj A.obj A
        (singletonContractingDegreeProfile A) i).hom
      (singletonContractionTensorMap A.obj A.obj A
        (singletonContractingDegreeProfile A) i
        (singletonContractingElement A)) = identityCochain A.obj := by
  let i₀ := singletonIndex A.obj A.obj A
  have hi : i = i₀ := Fin.ext (by simp [i₀])
  subst i
  have hmap : singletonContractionTensorMap A.obj A.obj A
        (singletonContractingDegreeProfile A) i₀ ≫
      (singletonContractedSummandIsoOriginal A.obj A.obj A
        (singletonContractingDegreeProfile A) i₀).hom =
      (singletonSummandIsoTensor A.obj A.obj A
        (singletonContractingDegreeProfile A)).hom ≫
        adjacentFactorComposition (singletonContractingDegreeProfile A) i₀ ≫
        (singletonAdjacentTargetIsoOriginal A.obj A.obj A
          (singletonContractingDegreeProfile A) i₀).hom := by
    simp [i₀, singletonContractionTensorMap,
      singletonAdjacentTargetIsoOriginal,
      singletonContractedSummandIsoOriginal,
      singletonContractedSummandIsoAdjacentTarget]
  have happ := congrArg (fun f ↦ f.hom (singletonContractingElement A)) hmap
  change (singletonContractedSummandIsoOriginal A.obj A.obj A
        (singletonContractingDegreeProfile A) i₀).hom
      (singletonContractionTensorMap A.obj A.obj A
        (singletonContractingDegreeProfile A) i₀
        (singletonContractingElement A)) = _ at happ
  have hsource : (singletonSummandIsoTensor A.obj A.obj A
      (singletonContractingDegreeProfile A)).hom (singletonContractingElement A) =
      identityCochain A.obj ⊗ₜ[ℤ] identityCochain A.obj := by
    exact singletonSummandIsoTensorAt_contractingElement A
  rw [happ]
  change (singletonAdjacentTargetIsoOriginal A.obj A.obj A
      (singletonContractingDegreeProfile A) i₀).hom
      (adjacentFactorComposition (singletonContractingDegreeProfile A) i₀
        ((singletonSummandIsoTensor A.obj A.obj A
          (singletonContractingDegreeProfile A)).hom
            (singletonContractingElement A))) = _
  rw [hsource]
  rw [singletonAdjacentTargetIsoOriginal_eq_direct]
  unfold adjacentFactorComposition singletonAdjacentTargetIsoOriginalDirect
    singletonContractingDegreeProfile
  simp only [Int.reduceNeg, Int.reduceAdd, singleton_length]
  change (CochainComplex.HomComplex.Cochain.ofHom (𝟙 A.obj.obj)).comp
      (CochainComplex.HomComplex.Cochain.ofHom (𝟙 A.obj.obj)) (by omega) = _
  simp [identityCochain]

theorem singletonContractionLargeMap_contractingElement
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton A.obj A.obj A).length) :
    (singletonContractionLargeMap A.obj A.obj A
        (singletonContractingDegreeProfile A) i).hom
        (ULift.up (singletonContractingElement A)) =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex A.obj A.obj (-1 + 1) ↦ largeSummandModule s)
        ⟨eraseIntermediate (singleton A.obj A.obj A) i,
          (singletonContractingDegreeProfile A).contract i⟩).hom
        (ULift.up
          ((singletonContractedSummandIsoOriginal A.obj A.obj A
            (singletonContractingDegreeProfile A) i).inv (identityCochain A.obj))) := by
  have hx : ((ModuleCat.uliftFunctor.{1} ℤ).map
        (singletonContractionTensorMap A.obj A.obj A
          (singletonContractingDegreeProfile A) i)).hom
        (ULift.up (singletonContractingElement A)) =
      ULift.up ((singletonContractedSummandIsoOriginal A.obj A.obj A
        (singletonContractingDegreeProfile A) i).inv (identityCochain A.obj)) := by
    rw [uliftFunctor_map_up]
    apply ULift.ext
    let e := singletonContractedSummandIsoOriginal A.obj A.obj A
      (singletonContractingDegreeProfile A) i
    exact calc
      _ = e.inv (e.hom (singletonContractionTensorMap A.obj A.obj A
          (singletonContractingDegreeProfile A) i
          (singletonContractingElement A))) := (e.hom_inv_id_apply _).symm
      _ = e.inv (identityCochain A.obj) := congrArg e.inv
        (singletonContractionTensorMap_contractingElement A i)
  unfold singletonContractionLargeMap
  rw [singletonContractingDegreeProfile_contractionSign]
  simp only [one_smul]
  change (Limits.Sigma.ι
      (fun s : GradedSummandIndex A.obj A.obj (-1 + 1) ↦ largeSummandModule s)
      ⟨eraseIntermediate (singleton A.obj A.obj A) i,
        (singletonContractingDegreeProfile A).contract i⟩).hom
      (((ModuleCat.uliftFunctor.{1} ℤ).map
        (singletonContractionTensorMap A.obj A.obj A
          (singletonContractingDegreeProfile A) i)).hom
        (ULift.up (singletonContractingElement A))) = _
  exact congrArg
    (fun z ↦ (Limits.Sigma.ι
      (fun s : GradedSummandIndex A.obj A.obj (-1 + 1) ↦ largeSummandModule s)
      ⟨eraseIntermediate (singleton A.obj A.obj A) i,
        (singletonContractingDegreeProfile A).contract i⟩).hom z) hx


end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
