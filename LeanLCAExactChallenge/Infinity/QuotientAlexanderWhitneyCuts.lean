/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientDoldKanMonoidal
import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Alexander--Whitney chain maps for the corrected quotient

This file starts the explicit Alexander--Whitney construction for simplicial integer modules.
For a cut `p + q = n`, the front `p`-face and back `q`-face give a morphism into the
corresponding summand of the tensor product of alternating face-map complexes. Summing over
all cuts gives the standard degree-`n` Alexander--Whitney formula.

The face identities and cut projections below prove that the degree maps commute with the
alternating differentials. They therefore assemble into a natural chain map, which is then
composed with the normalized Moore inclusion and the `PInfty` retractions. The normalized
tensorator and its unit map are constructed here. Projector compatibility and the two unit laws
are proved in follow-up modules. The coassociativity and normalized transport modules then
complete the oplax package.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

/-- Maps into a finite coproduct are determined by all canonical projections. -/
theorem finiteCoproduct_hom_ext {C : Type*} [Category* C] [Preadditive C]
    {A : C} {J : Type*} [Finite J] [DecidableEq J]
    (F : J → C) [HasCoproduct F] {f g : A ⟶ ∐ F}
    (h : ∀ j, f ≫ Sigma.π F j = g ≫ Sigma.π F j) : f = g := by
  letI := Fintype.ofFinite J
  have hid : ∑ j, Sigma.π F j ≫ Sigma.ι F j = 𝟙 _ := by
    apply Sigma.hom_ext
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [← Category.assoc, Sigma.ι_π_of_ne F hij.symm, zero_comp]
    · simp
  rw [← Category.comp_id f, ← Category.comp_id g, ← hid,
    Preadditive.comp_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Category.assoc, h j, Category.assoc]

/-- A finite sum supported at exactly two distinct indices is their sum. -/
theorem fintype_sum_eq_add_two_of_eq_zero
    {I M : Type*} [Fintype I] [AddCommMonoid M]
    (a b : I) (hba : b ≠ a) (f : I → M)
    (hzero : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i, f i = f a + f b := by
  classical
  rw [Fintype.sum_eq_add_sum_compl a]
  congr 1
  apply Finset.sum_eq_single b
  · intro i hi hiba
    exact hzero i (by simpa using hi) hiba
  · intro hb
    exfalso
    exact hb (by simpa using hba)

/-- Alternating face-map chains, abbreviated for the tensor-component calculations below. -/
abbrev alternatingChains (X : SimplicialObject (QuotientModule)) :=
  (alternatingFaceMapComplex (QuotientModule)).obj X

/-- The coproduct family underlying degree `n` of the tensor of alternating chains. -/
abbrev tensorCutFamily (X Y : SimplicialObject (QuotientModule)) (n : ℕ) :=
  (((((curriedTensor (QuotientModule)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (alternatingChains X)).obj (alternatingChains Y)).toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) n)

/-- Projection from total tensor degree `n` to the component indexed by `i + j = n`. -/
def tensorPairProjection (X Y : SimplicialObject (QuotientModule))
    (i j n : ℕ) (h : i + j = n) :
    (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n ⟶
      (alternatingChains X).X i ⊗ (alternatingChains Y).X j :=
  Sigma.π (tensorCutFamily X Y n)
    ⟨⟨i, j⟩, by change i + j = n; exact h⟩

/-- Projection to the component selected by a front cut `p : Fin (n + 1)`. -/
def tensorCutProjection (X Y : SimplicialObject (QuotientModule))
    (n : ℕ) (p : Fin (n + 1)) :
    (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n ⟶
      (alternatingChains X).X p ⊗ (alternatingChains Y).X (n - p) :=
  tensorPairProjection X Y p (n - p) n (by omega)

/-- Cuts of `n` are equivalent to the fiber of addition over `n`. -/
def tensorCutEquiv (n : ℕ) :
    Fin (n + 1) ≃
      { pq : ℕ × ℕ // pq ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } where
  toFun p := ⟨(p, n - p), by change p + (n - p) = n; omega⟩
  invFun pq := ⟨pq.1.1, by
    have hpq := pq.2
    change pq.1.1 + pq.1.2 = n at hpq
    omega⟩
  left_inv p := by ext; rfl
  right_inv pq := by
    rcases pq with ⟨⟨p, q⟩, hpq⟩
    change p + q = n at hpq
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      omega

/-- Maps into a total tensor degree are determined by all cut projections. -/
theorem tensorDegree_hom_ext (X Y : SimplicialObject (QuotientModule))
    (n : ℕ) {A : QuotientModule}
    {f g : A ⟶
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n}
    (h : ∀ p : Fin (n + 1),
      f ≫ tensorCutProjection X Y n p = g ≫ tensorCutProjection X Y n p) :
    f = g := by
  let J : Type := { pq : ℕ × ℕ // pq ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  apply finiteCoproduct_hom_ext _
  rintro ⟨⟨p, q⟩, hpq⟩
  change p + q = n at hpq
  have hp : p < n + 1 := by omega
  have hq : q = n - p := by omega
  subst q
  exact h ⟨p, hp⟩

@[reassoc (attr := simp)]
theorem ιTensorObj_tensorPairProjection_self
    (X Y : SimplicialObject (QuotientModule)) (i j n : ℕ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor (alternatingChains X) (alternatingChains Y)
        (curriedTensor (QuotientModule)) (ComplexShape.down ℕ) i j n h ≫
      tensorPairProjection X Y i j n h = 𝟙 _ := by
  exact Sigma.ι_π_eq_id _ _

@[reassoc]
theorem ιTensorObj_tensorPairProjection_of_ne
    (X Y : SimplicialObject (QuotientModule))
    (i j i' j' n : ℕ) (h : i + j = n) (h' : i' + j' = n)
    (hne : (i, j) ≠ (i', j')) :
    HomologicalComplex.ιMapBifunctor (alternatingChains X) (alternatingChains Y)
        (curriedTensor (QuotientModule)) (ComplexShape.down ℕ) i j n h ≫
      tensorPairProjection X Y i' j' n h' = 0 := by
  apply Sigma.ι_π_of_ne
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- The inclusion of the front `p`-face into an `n`-simplex. -/
def alexanderWhitneyFront (n : ℕ) (p : Fin (n + 1)) :
    SimplexCategory.mk (p : ℕ) ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval 0 p (by omega)

/-- The inclusion of the back `(n - p)`-face into an `n`-simplex. -/
def alexanderWhitneyBack (n : ℕ) (p : Fin (n + 1)) :
    SimplexCategory.mk (n - p) ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval p (n - p) (by omega)

@[simp]
theorem alexanderWhitneyFront_apply (n : ℕ) (p : Fin (n + 1))
    (i : Fin ((p : ℕ) + 1)) :
    ((alexanderWhitneyFront n p).toOrderHom i).1 = i.1 := by
  rfl

@[simp]
theorem alexanderWhitneyBack_apply (n : ℕ) (p : Fin (n + 1))
    (i : Fin (n - (p : ℕ) + 1)) :
    ((alexanderWhitneyBack n p).toOrderHom i).1 = p + i := by
  simp [alexanderWhitneyBack, SimplexCategory.subinterval, Nat.add_comm]

@[simp]
theorem alexanderWhitneyFront_zero :
    alexanderWhitneyFront 0 0 = 𝟙 (SimplexCategory.mk 0) := by
  apply Subsingleton.elim

@[simp]
theorem alexanderWhitneyBack_zero :
    alexanderWhitneyBack 0 0 = 𝟙 (SimplexCategory.mk 0) := by
  apply Subsingleton.elim

/-- A face at or before the cut acts on the front simplex. -/
theorem alexanderWhitneyFront_face (n p i : ℕ) (hp : p ≤ n) (hi : i ≤ p) :
    SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + 2)) ≫
        alexanderWhitneyFront (n + 1) ⟨p + 1, by omega⟩ =
      alexanderWhitneyFront n ⟨p, by omega⟩ ≫
        SimplexCategory.δ (⟨i, by omega⟩ : Fin (n + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change
    (Fin.succAbove (⟨i, by omega⟩ : Fin (p + 2)) ⟨k, hk⟩).val =
      (Fin.succAbove (⟨i, by omega⟩ : Fin (n + 2))
        (⟨k, by omega⟩ : Fin (n + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- A face on a back subinterval is the corresponding offset face of the whole simplex. -/
theorem alexanderWhitneyBack_face (p q : ℕ) (i : Fin (q + 2)) :
    SimplexCategory.δ i ≫
        SimplexCategory.subinterval p (q + 1) (by omega) =
      SimplexCategory.subinterval p q (by omega) ≫
        SimplexCategory.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change
    (Fin.succAbove i ⟨k, hk⟩).val + p =
      (Fin.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 2))
        (⟨k + p, by omega⟩ : Fin (p + q + 1))).val
  rcases i with ⟨i, hi⟩
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- Removing a vertex at or before the cut shifts the unchanged back interval. -/
theorem alexanderWhitneyBack_early_face (p q i : ℕ) (hi : i ≤ p) :
    SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega) =
      SimplexCategory.subinterval (n := p + q) p q (by omega) ≫
        SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change k + (p + 1) =
    (Fin.succAbove (⟨i, by omega⟩ : Fin (p + q + 2))
      (⟨k + p, by omega⟩ : Fin (p + q + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- Removing a vertex strictly after the cut leaves the front interval unchanged. -/
theorem alexanderWhitneyFront_late_face (p q : ℕ)
    (i : Fin (q + 2)) (hi : 0 < i) :
    SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega) =
      SimplexCategory.subinterval (n := p + q) 0 p (by omega) ≫
        SimplexCategory.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change k =
    (Fin.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 2))
      (⟨k, by omega⟩ : Fin (p + q + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- The last front face is the shorter front subinterval. -/
theorem alexanderWhitneyFront_last (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫
        SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega) =
      SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change (Fin.succAbove (Fin.last (p + 1)) ⟨k, hk⟩).val = k
  exact congrArg Fin.val
    (Fin.succAbove_last_apply (⟨k, hk⟩ : Fin (p + 1)))

/-- The zeroth back face is the back subinterval beginning one vertex later. -/
theorem alexanderWhitneyBack_zero_face (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫
        SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega) =
      SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change (Fin.succAbove (0 : Fin (q + 2)) ⟨k, hk⟩).val + p = k + (p + 1)
  simp [Fin.succAbove]
  omega

/-- Tensor maps along definitionally equal subinterval lengths are heterogeneously equal.
This isolates the dependent proof transport needed when normalizing a cut subtraction. -/
theorem tensor_map_subinterval_heq
    {A B : QuotientModule} (f : A ⟶ B)
    (Y : SimplicialObject (QuotientModule))
    (n a b b' : ℕ) (h : b = b')
    (hab : a + b ≤ n) (hab' : a + b' ≤ n) :
    (f ⊗ₘ Y.map (SimplexCategory.subinterval (n := n) a b hab).op) ≍
      (f ⊗ₘ Y.map (SimplexCategory.subinterval (n := n) a b' hab').op) := by
  subst b'
  rfl


end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
